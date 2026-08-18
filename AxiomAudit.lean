import Lean

/-!
# `axiom-audit`: an axiom-allowlist audit for Lean libraries

Builds a library's environment from its compiled `.olean`s and reports, for every declaration
*defined in the audited root namespace*, the axioms it transitively depends on — failing if any lie
outside a configurable allowlist (by default `propext`, `Classical.choice`, `Quot.sound`). Because
it works on the kernel environment rather than source text, it catches what a `grep` cannot:
`sorry`/`admit` (`sorryAx`), `native_decide` (`Lean.ofReduceBool`), and any home-rolled `axiom`,
including ones reaching in through imports.

This is a generalization of the audit Kim Morrison wrote for the TauCeti library.
-/

open Lean

namespace AxiomAudit

/--
Reader/State monad for the shared axiom-collection pass: the `Environment` is read-only and the
`NameMap (Array Name)` memoizes, for every constant visited, the (sorted) set of axioms it
transitively depends on. The map is threaded across *all* declarations so the shared dependency
closure (e.g. all of Mathlib) is walked once in total, not re-walked per declaration.
-/
abbrev AxiomM := ReaderT Environment (StateM (NameMap (Array Name)))

/--
The axioms transitively used by `c`, memoized in the shared `NameMap`. Mirrors `Lean.collectAxioms`'
traversal of each declaration's type and value, but shares one cache across every call — the stock
`collectAxioms` rebuilds its state and redoes per-call setup on each invocation, which dominates a
whole-library audit. A constant is recorded with the empty set before recursing so cycles terminate;
axioms are leaves, so a back edge into an in-progress constant contributes nothing to it directly.

Soundness for an allowlist audit: the declaration that *directly* mentions a disallowed axiom always
gets that axiom in its own set (the edge to the leaf axiom is in its own frame, not a back edge), and
since the imported libraries are axiom-clean that declaration is itself an audited candidate — so any
violation is reported and fails the run, and the project-wide union of axioms is complete. The empty
sentinel can, in a cyclic declaration cluster, leave *other* members of the cluster with an
incomplete set, so a per-declaration list may under-count there (a re-run flags the rest); it never
hides an axiom project-wide and never lets a violation pass.

TODO(migration): once `Lean.collectAxiomsMany` (leanprover/lean4#14157) is in this tool's
minimum-supported Lean version, replace this with one call — `collectAxiomsMany candidates` — which
is faster still (it reuses the precomputed per-module axiom data) and removes the cyclic-cluster
caveat above.
-/
partial def axiomsOf (c : Name) : AxiomM (Array Name) := do
  if let some s := (← get).find? c then return s
  modify (·.insert c #[])
  let env ← read
  let fromConsts (ds : Array Name) (init : NameSet) : AxiomM NameSet :=
    ds.foldlM (init := init) fun acc d => return (← axiomsOf d).foldl (·.insert ·) acc
  let fromExprs (es : Array Expr) : AxiomM NameSet :=
    es.foldlM (init := {}) fun acc e => fromConsts e.getUsedConstants acc
  let used : NameSet ← do
    match env.find? c with
    | some (.axiomInfo v) =>
        let t ← fromExprs #[v.type]
        pure (t.insert c)
    | some (.defnInfo v)   => fromExprs #[v.type, v.value]
    | some (.thmInfo v)    => fromExprs #[v.type, v.value]
    | some (.opaqueInfo v) => fromExprs #[v.type, v.value]
    | some (.quotInfo _)   => pure ({} : NameSet)
    | some (.ctorInfo v)   => fromExprs #[v.type]
    | some (.recInfo v)    => fromExprs #[v.type]
    | some (.inductInfo v) =>
        let base ← fromExprs #[v.type]
        fromConsts v.ctors.toArray base
    | none                 => pure ({} : NameSet)
  let arr := used.toArray.qsort Name.lt
  modify (·.insert c arr)
  return arr

/-- Build the environment from the given imported modules and run `act` in `CoreM`.
`trustLevel := 1024` means imported constants are taken as type-correct rather than re-checked: this
audit checks *which axioms* a declaration depends on, not whether the proofs are valid, so it relies
on a prior `lake build` having kernel-checked the library. It is not a defense against stale or
hand-forged `.olean`s.

`loadExts := true` materializes the persistent environment extensions, needed to find
source locations of declarations.
 -/
def withImportedEnv {α} (modules : Array Name) (act : CoreM α) : IO α := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution -- required by `loadExts := true`; the exe supports the interpreter
  let env ← importModules (modules.map (fun m => { module := m })) {} (trustLevel := 1024)
    (loadExts := true)
  try
    Prod.fst <$> Core.CoreM.toIO act
      (ctx := { fileName := "<axiom-audit>", fileMap := default }) (s := { env := env })
  finally
    unsafe env.freeRegions

/-- Is `mod` the audited root or one of its submodules? -/
def inAuditedLib (root : Name) (mod : Name) : Bool := mod == root || root.isPrefixOf mod

/-- The module name for a `.lean` source path, e.g. `MyLib/Foo/Bar.lean ↦ MyLib.Foo.Bar`. -/
def pathToModule (p : System.FilePath) : Name :=
  (p.withExtension "").components.foldl (fun n s => Name.mkStr n s) Name.anonymous

/-- Every `.lean` module under `dir`, recursively (paths kept relative to the cwd, so module names
come out right when the tool is run from the project root). -/
partial def collectLeanModules (dir : System.FilePath) : IO (Array Name) := do
  let mut acc := #[]
  for entry in (← dir.readDir) do
    if (← entry.path.isDir) then
      acc := acc ++ (← collectLeanModules entry.path)
    else if entry.path.extension == some "lean" then
      acc := acc.push (pathToModule entry.path)
  return acc

/-- Best-effort auto-detection of the library root: the first `lean_lib` name in the lakefile
(`lakefile.toml`'s `[[lean_lib]]` or `lakefile.lean`'s `lean_lib`). Used when `--root` is not given,
so `axiom-audit` "just works" in a standard single-library workspace. Returns `none` if no lakefile
or no library is found (then the caller asks for an explicit `--root`). -/
def detectRoot : IO (Option Name) := do
  let firstQuoted (s : String) : Option Name :=
    match s.splitOn "\"" with
    | _ :: v :: _ => some v.toName
    | _ => none
  if (← System.FilePath.pathExists "lakefile.toml") then
    let mut inLib := false
    for line in (← IO.FS.readFile "lakefile.toml").splitOn "\n" do
      if line.startsWith "[[lean_lib]]" then inLib := true
      else if line.startsWith "[" then inLib := false
      else if inLib && line.startsWith "name" then
        if let some n := firstQuoted line then return some n
    return none
  else if (← System.FilePath.pathExists "lakefile.lean") then
    for line in (← IO.FS.readFile "lakefile.lean").splitOn "\n" do
      if let some after := (line.splitOn "lean_lib ")[1]? then
        let tok := (((after.splitOn " ")[0]?.getD "").replace "«" "").replace "»" ""
        if tok ≠ "" then return some tok.toName
    return none
  else
    return none

/-- A source location, `1`-based line and `0`-based column. -/
structure Loc where
  path : String
  line : Nat
  col : Nat

instance : ToString Loc := ⟨fun l => s!"{l.path}:{l.line}:{l.col}"⟩

/-- An offending declaration. -/
structure Violation where
  decl : String
  axioms : Array String
  loc? : Option Loc

/-- The result of an audit, rendered to `String`s inside the environment callback (declaration and
axiom `Name`s live in a memory-mapped region unmapped once `withImportedEnv` returns). -/
structure Report where
  root : String
  allowed : Array String
  audited : Nat
  /-- Distinct axioms used anywhere under `root`, sorted. -/
  axiomsUsed : Array String
  violations : Array Violation

/-- The audit succeeded only if there were no violations AND something was actually audited (an
empty audit usually means a miswired root/module selection, not a clean library). -/
def Report.ok (r : Report) : Bool := r.violations.isEmpty && r.audited > 0

/-- A heap-owned copy of a string. Data loaded from `.olean`s lives in a memory-mapped region that
is unmapped once `withImportedEnv` returns; strings derived from it can still be backed by that
region, so we rebuild them character by character to make them self-owned and safe to keep in the
returned `Report`. -/
def freshStr' (s : String) : String := s.foldl (fun acc c => acc.push c) ""

/-- A heap-owned copy of a name's string; see `freshStr'`. -/
def freshStr (n : Name) : String := freshStr' (toString n)

/-- `p` relative to the current directory when it lies under it,
otherwise unchanged (absolute). -/
def relativeToCwd (p : System.FilePath) : IO System.FilePath := do
  let cwd := (← IO.currentDir).toString
  let p := (← IO.FS.realPath p).toString
  let pre := cwd ++ System.FilePath.pathSeparator.toString
  return ⟨if p.startsWith pre then (p.toSubstring.drop pre.length).toString else p⟩

/-- The source file of module `mod`. Searches `LEAN_SRC_PATH`, falls back to guessing
the path from the module name. -/
def moduleSource (mod : Name) : IO System.FilePath := do
  match ← (← getSrcSearchPath).findModuleWithExt "lean" mod with
  | some p => relativeToCwd p
  | none => return System.mkFilePath (mod.components.map toString) |>.addExtension "lean"

/-- The source location of `decl`'s name: the file of its module plus the declaration's selection
range (where Lean's own diagnostics for the declaration point). `none` when the module is unknown
or the library was compiled without declaration ranges. Strings are rebuilt via `freshStr'` for the
same reason as everywhere else: the backing data can be memory-mapped. -/
def declLoc? (decl : Name) : CoreM (Option Loc) := do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? decl | return none
  let some mod := env.allImportedModuleNames[idx.toNat]? | return none
  let some ranges ← findDeclarationRanges? decl | return none
  return some {
    path := freshStr' (← moduleSource mod).toString
    line := ranges.selectionRange.pos.line
    col := ranges.selectionRange.pos.column
  }

/-- Audit every declaration defined under `root`, against `allowed`. -/
def audit (root : Name) (allowed : List Name) : CoreM Report := do
  let env ← getEnv
  let allowedSet : NameSet := allowed.foldl (·.insert ·) {}
  let modNames := env.allImportedModuleNames
  -- Candidates: declarations defined in a module under `root`.
  let candidates : Array Name := env.constants.fold (init := #[]) fun acc declName _ =>
    match env.getModuleIdxFor? declName with
    | some idx =>
      match modNames[idx.toNat]? with
      | some m => if inAuditedLib root m then acc.push declName else acc
      | none => acc
    | none => acc
  -- One shared-cache pass: the full axiom set of every candidate.
  let perDecl : Array (Array Name) := (candidates.mapM axiomsOf |>.run env).run' {}
  let mut usedAll : NameSet := {}
  let mut violations : Array Violation := #[]
  for i in [0:candidates.size] do
    let decl := candidates[i]!
    let axs := perDecl[i]!
    for ax in axs do usedAll := usedAll.insert ax
    let bad := axs.filter (!allowedSet.contains ·)
    if !bad.isEmpty then
      violations := violations.push {
        decl := freshStr decl
        axioms := bad.map freshStr
        loc? := ← declLoc? decl
      }
  return {
    root := freshStr root
    allowed := (allowed.map freshStr).toArray
    audited := candidates.size
    axiomsUsed := (usedAll.toArray.qsort Name.lt).map freshStr
    violations
  }

/-- Machine-readable report for `--json`. -/
def Report.toJson (r : Report) : Lean.Json :=
  Json.mkObj [
    ("root", Json.str r.root),
    ("allowed", Lean.toJson r.allowed),
    ("audited", Lean.toJson r.audited),
    ("ok", Json.bool r.ok),
    ("axiomsUsed", Lean.toJson r.axiomsUsed),
    ("violations", Lean.toJson (r.violations.map fun v =>
      Json.mkObj <| [("decl", Json.str v.decl), ("axioms", Lean.toJson v.axioms)] ++
        match v.loc? with
        | some l => [("file", Json.str l.path), ("line", Lean.toJson l.line),
                     ("col", Lean.toJson l.col)]
        | none => []))
  ]

end AxiomAudit

import AxiomAudit

open Lean AxiomAudit

def usage : String :=
"axiom-audit — fail if any declaration in your library depends on an axiom outside the allowlist.

USAGE:
  axiom-audit [options]

By default it audits the library found in the current lakefile, allowing propext,
Classical.choice, Quot.sound. Run from the project root after `lake build`
(e.g. `lake env axiom-audit`).

OPTIONS:
  --root <Namespace>     audit declarations defined in modules under this root. If omitted, the
                         first `lean_lib` in the lakefile is used.
  --allow a,b,c          comma-separated allowlist of axioms
                         (default: propext,Classical.choice,Quot.sound)
  --modules a,b,c        import exactly these modules to build the environment
                         (instead of importing the root module)
  --modules-from <dir>   import every .lean module found under <dir> — for a root that does not
                         transitively import the whole library (e.g. an intentionally empty root)
  --json                 print a machine-readable JSON report instead of human-readable text
  -h, --help             show this help

Exits 0 if clean, 1 on a violation (or nothing audited), 2 on a usage/IO error."

structure Opts where
  root : Option Name := none
  allow : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  modules : Option (Array Name) := none
  modulesFrom : Option System.FilePath := none
  json : Bool := false

/-- Drop all whitespace from a token (axiom names contain none, so this is an allocation-free trim
that avoids the deprecated `String` trim APIs). -/
def squash (s : String) : String := s.foldl (fun acc c => if c.isWhitespace then acc else acc.push c) ""

/-- Split a comma-separated string into `Name`s, trimming each and dropping blanks. -/
def parseNames (s : String) : List Name :=
  (s.splitOn ",").filterMap fun p => let p := squash p; if p.isEmpty then none else some p.toName

/-- Normalize `--key=value` into two tokens `--key`, `value`. -/
def normalize (args : List String) : List String :=
  (args.map fun a =>
    if a.startsWith "--" then
      match a.splitOn "=" with
      | k :: rest@(_ :: _) => [k, String.intercalate "=" rest]
      | _ => [a]
    else [a]).flatten

partial def parse : List String → Opts → Except String Opts
  | [], o => .ok o
  | "--json" :: rest, o => parse rest { o with json := true }
  | "--root" :: v :: rest, o => parse rest { o with root := some v.toName }
  | "--allow" :: v :: rest, o => parse rest { o with allow := parseNames v }
  | "--modules" :: v :: rest, o => parse rest { o with modules := some (parseNames v).toArray }
  | "--modules-from" :: v :: rest, o => parse rest { o with modulesFrom := some v }
  | a :: _, _ => .error s!"unknown or incomplete argument: {a}"

/-- A JSON error object for `--json` mode, so machine consumers always get parseable output. -/
def errorJson (msg : String) : Lean.Json :=
  Json.mkObj [("ok", Json.bool false), ("audited", Lean.toJson 0), ("error", Json.str msg)]

/-- Report a usage/IO error (exit code 2), as JSON or human text. -/
def usageError (json : Bool) (msg : String) : IO UInt32 := do
  if json then IO.println (errorJson msg).compress
  else IO.eprintln s!"axiom-audit: {msg}\n\n{usage}"
  return 2

def main (args : List String) : IO UInt32 := do
  if args.contains "-h" || args.contains "--help" then
    IO.println usage
    return 0
  let o ← match parse (normalize args) {} with
    | .error e => return (← usageError (args.contains "--json") e)
    | .ok o => pure o
  if o.modules.isSome && o.modulesFrom.isSome then
    return (← usageError o.json "pass at most one of --modules and --modules-from")
  -- Resolve the root: explicit `--root`, else auto-detect the first lakefile library.
  let some root ← (match o.root with | some r => pure (some r) | none => detectRoot)
    | return (← usageError o.json "could not determine the library root from a lakefile; pass --root <Namespace>")
  if root.isAnonymous then
    return (← usageError o.json "the root namespace is empty; pass a non-empty --root")
  -- Resolve the modules to import (and audit-import).
  let importModules ← match o.modules, o.modulesFrom with
    | some ms, _     => pure ms
    | none, some dir => pure ((← collectLeanModules dir).qsort Name.lt)
    | none, none     => pure #[root]
  if importModules.isEmpty then
    return (← usageError o.json "no modules to import (check --modules / --modules-from)")
  -- Build the environment and audit, turning import/IO failures into a clean error (no crash).
  let result ← try
      let r ← withImportedEnv importModules (audit root o.allow)
      pure (Except.ok r)
    catch e => pure (Except.error (toString e))
  match result with
  | .error msg =>
    usageError o.json s!"failed to load the environment or audit: {msg}"
  | .ok r =>
    if o.json then
      IO.println r.toJson.compress
      return (if r.ok then 0 else 1)
    if r.audited == 0 then
      IO.eprintln s!"axiom-audit: audited 0 declarations under '{r.root}' — nothing imported? \
        check --root / --modules / --modules-from."
      return 1
    if r.violations.isEmpty then
      IO.println s!"axiom-audit: audited {r.audited} declaration(s) under '{r.root}'; \
        all within the allowlist {r.allowed.toList}."
      return 0
    else
      IO.eprintln s!"axiom-audit: {r.violations.size} declaration(s) under '{r.root}' use disallowed axioms:"
      for (d, axs) in r.violations do
        IO.eprintln s!"  {d} → {axs.toList}"
      IO.eprintln s!"allowed: {r.allowed.toList}"
      return 1

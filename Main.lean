import AxiomAudit

open Lean AxiomAudit

def usage : String :=
"axiom-audit — fail if any declaration under <root> depends on an axiom outside the allowlist.

USAGE:
  axiom-audit --root <Namespace> [options]

OPTIONS:
  --root <Namespace>     (required) audit declarations defined under this namespace
  --allow a,b,c          comma-separated allowlist of axioms, no spaces
                         (default: propext,Classical.choice,Quot.sound)
  --modules a,b,c        import exactly these modules to build the environment
  --modules-from <dir>   import every .lean module found under <dir> — for a root that does not
                         transitively import the whole library (e.g. an intentionally empty root)
  --json                 print a machine-readable JSON report (summary, the distinct axioms used,
                         and the violations) instead of human-readable text
  -h, --help             show this help

With neither --modules nor --modules-from, the root module itself is imported (assuming it imports
the library). Run from the project root after `lake build`, e.g. `lake env axiom-audit --root MyLib`.
Exits 0 if clean, 1 on a violation (or nothing audited), 2 on a usage error."

structure Opts where
  root : Option Name := none
  allow : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  modules : Option (Array Name) := none
  modulesFrom : Option System.FilePath := none
  json : Bool := false

/-- Split a comma-separated string into `Name`s, dropping blanks. -/
def parseNames (s : String) : List Name :=
  -- comma-separated, no surrounding spaces (avoids depending on version-churny String trim APIs)
  (s.splitOn ",").filterMap fun p => if p.isEmpty then none else some p.toName

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

def main (args : List String) : IO UInt32 := do
  if args.contains "-h" || args.contains "--help" then
    IO.println usage
    return 0
  match parse (normalize args) {} with
  | .error e =>
    IO.eprintln s!"axiom-audit: {e}\n\n{usage}"
    return 2
  | .ok o =>
    match o.root with
    | none =>
      IO.eprintln s!"axiom-audit: --root is required\n\n{usage}"
      return 2
    | some root =>
      let importModules ←
        match o.modules, o.modulesFrom with
        | some ms, _      => pure ms
        | none, some dir  => collectLeanModules dir
        | none, none      => pure #[root]
      if importModules.isEmpty then
        IO.eprintln "axiom-audit: no modules to import (check --root / --modules / --modules-from)"
        return 2
      let r ← withImportedEnv importModules (audit root o.allow)
      if o.json then
        IO.println r.toJson.compress
        return (if r.ok && r.audited > 0 then 0 else 1)
      -- human-readable
      if r.audited == 0 then
        IO.eprintln s!"axiom-audit: audited 0 declarations under '{r.root}' — nothing imported? \
          check --root / --modules / --modules-from."
        return 1
      if r.ok then
        IO.println s!"axiom-audit: audited {r.audited} declaration(s) under '{r.root}'; \
          all within the allowlist {r.allowed.toList}."
        return 0
      else
        IO.eprintln s!"axiom-audit: {r.violations.size} declaration(s) under '{r.root}' use disallowed axioms:"
        for (d, axs) in r.violations do
          IO.eprintln s!"  {d} → {axs.toList}"
        IO.eprintln s!"allowed: {r.allowed.toList}"
        return 1

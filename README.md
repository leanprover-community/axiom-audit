# axiom-audit

A fast, dependency-free **axiom-allowlist audit** for Lean 4 libraries: fail CI if any declaration
in your library transitively depends on an axiom outside an allowlist (by default `propext`,
`Classical.choice`, `Quot.sound`). Because it inspects the *kernel environment* rather than source
text, it catches what a `grep` cannot:

- `sorry` / `admit` (which surface as `sorryAx`),
- `native_decide` (which adds `Lean.ofReduceBool`),
- any home-rolled `axiom`, including ones reaching in through imports.

## Usage

Build your project first, then run the tool **from the project root** so it can find your oleans:

```bash
lake build
lake exe axiom-audit --root MyLib
```

or, if you depend on it as a Lake package, `lake exe axiom-audit …`. It exits `0` when clean, `1`
on a violation (or if nothing was audited), and `2` on a usage error.

### Options

| flag | meaning |
| --- | --- |
| `--root <Namespace>` | **(required)** audit declarations defined under this namespace |
| `--allow a,b,c` | comma-separated allowlist of axioms (no spaces). Default: `propext,Classical.choice,Quot.sound` |
| `--modules a,b,c` | import exactly these modules to build the environment |
| `--modules-from <dir>` | import every `.lean` module found under `<dir>` — for a root that does not transitively import the whole library (e.g. an intentionally empty root) |
| `--json` | print a machine-readable JSON report instead of human-readable text |
| `-h`, `--help` | show help |

With neither `--modules` nor `--modules-from`, the root module itself is imported (assuming it
imports the library).

### JSON output (`--json`)

For tool interaction, `--json` reports **all axioms used** project-wide plus any violations:

```json
{
  "root": "MyLib",
  "allowed": ["propext", "Classical.choice", "Quot.sound"],
  "audited": 4426,
  "ok": true,
  "axiomsUsed": ["propext", "Classical.choice", "Quot.sound"],
  "violations": [ { "decl": "MyLib.bad", "axioms": ["MyLib.myAxiom"] } ]
}
```

## How it works

The tool builds your library's environment from its compiled `.olean`s (with `trustLevel := 1024`:
it checks *which* axioms each declaration uses, not whether proofs are valid — run `lake build`
first), and collects each declaration's transitive axioms in a single memoized pass that shares one
cache across the whole library. That sharing is the point: calling `Lean.collectAxioms` once per
declaration rebuilds its cache and redoes per-call setup every time, which on a large library
(thousands of declarations over Mathlib) takes minutes; the shared pass takes seconds.

The shared-cache traversal is adapted from Robin Arnez's Mathlib-wide version (leanprover Zulip,
[#general > "Checking which axioms are used in a project"](https://leanprover.zulipchat.com/#narrow/stream/113489-general/topic/Checking.20which.20axioms.20are.20used.20in.20a.20project)),
and generalizes the audit Kim Morrison wrote for the TauCeti library.

> **Note:** [leanprover/lean4#14157](https://github.com/leanprover/lean4/pull/14157) proposes a
> `Lean.collectAxiomsMany` that does exactly this shared-cache collection in core (faster still, via
> precomputed per-module axiom data). Once it lands in this tool's minimum-supported Lean version,
> the embedded traversal will be replaced by a single call to it. Until then, the embedded version
> is the compatibility layer.

## License

Apache-2.0.

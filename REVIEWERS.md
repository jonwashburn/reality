## JOSS Reviewer Guide

This short guide helps you verify the artifact quickly and consistently. It summarizes how to build, run the smoke checks, exercise the proof reports, and validate the unitless audit comparator. No dataset downloads or secret tokens are required.

### What this repository claims (high-level)
- One foundational axiom (MP) and a proof spine to a unique, parameter-free framework at the golden ratio φ.
- Apex certificates: `PrimeClosure`, `ExclusiveRealityPlus`, `RecognitionReality` (with bi-interpretability), and `UltimateClosure`.
- A unitless audit harness: emits instrument predictions as JSON and compares them with a measurements file. Proven items gate CI; Scaffold/Planned are reported but non-gating.

### Prerequisites
- Platform: macOS/Linux recommended.
- Lean toolchain via `elan` (version pinned by `lean-toolchain`).
- Bash, Python 3.

### Install and build
```bash
elan toolchain install $(cat lean-toolchain)
source "$HOME/.elan/env"
lake build
```

### CI smoke check (minimal)
```bash
lake exe ci_checks
# Expect: "CI smoke: toolchain OK"
```

### Proof reports (optional quick look)
Open `IndisputableMonolith/URCAdapters/Reports.lean` and evaluate some `#eval` endpoints in your editor:
```lean
#eval IndisputableMonolith.URCAdapters.exclusive_reality_plus_report
#eval IndisputableMonolith.URCAdapters.recognition_reality_accessors_report
#eval IndisputableMonolith.URCAdapters.ultimate_closure_report
#eval IndisputableMonolith.URCAdapters.recognition_phi_eq_constants_report
```

### Reproducible summary (CLI)
```bash
lake exe ok            # human-readable summary
lake exe ok --json     # machine-readable summary
```

### Unitless audit (hard gate)
1) Build and emit instrument predictions:
```bash
lake build
lake exe audit > .out.json
```
2) Compare against measurements with the repository comparator:
```bash
./scripts/audit_compare.sh .out.json measurements.json
```
Expected: PASS for all `Proven` items; WARN for `Scaffold`; INFO for `Planned`. The script fails if any `Proven` item violates exact or z-score rules or if an upper-bound is exceeded.

### What to check for JOSS
- Functionality: `lake build` succeeds; smoke check prints OK; audit comparator passes for Proven items.
- Documentation: `README.md` quickstart, `machine-verified.tex` overview, `paper.md` (JOSS manuscript), and this guide.
- Tests/proofs: presence of `URCAdapters/Reports.lean` endpoints, CLI `ok` summary, and audit comparator wiring.
- Community: License, CODE_OF_CONDUCT.md, CONTRIBUTING.md, CITATION.cff.
- Research relevance: The formal proof artifacts (`PrimeClosure`, `ExclusiveRealityPlus`, `RecognitionReality`, `UltimateClosure`) and the unitless audit surface.

### Filing issues and questions
- Please open GitHub issues on this repository with a clear title (prefix with "review:"). Include command output when relevant.

### Time-boxed path (10–15 minutes)
1) `elan` install, `lake build`
2) `lake exe ci_checks` -> expect smoke OK
3) `lake exe audit | tee .out.json`
4) `./scripts/audit_compare.sh .out.json measurements.json` -> expect PASS for Proven
5) Optionally run `lake exe ok` and skim `machine-verified.tex`



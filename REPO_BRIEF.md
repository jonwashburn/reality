## Recognition — Brief Guide

This Lean 4 project houses the Recognition Science proof spine: from a single logical axiom to a gauge‑rigid bridge and a bundle that “RS measures reality.” It builds with Lake and depends on `mathlib`.

### Toolchain and Build
- **Lean**: `leanprover/lean4:v4.24.0-rc1` (from `lean-toolchain`)
- **Lake**: Package manager/build tool
- **Dependencies**: `mathlib` (git, see `lakefile.lean`)
- **Libraries**: `IndisputableMonolith`, `URC`

Commands:
```bash
elan default leanprover/lean4:v4.24.0-rc1 # if needed
lake build
lake exe ci_checks
```

### Quick Demos
- Reports: see `IndisputableMonolith/URCAdapters/Reports.lean` for `#eval` endpoints (e.g., `reality_bridge_report`, `recognition_closure_report`, `k_gate_report`).
- CI smoke (fast, minimal): `lake exe ci_checks`.

### Project Top‑Level
- `lakefile.lean`: package `recognition`, requires `mathlib`, defines `lean_lib`s and `ci_checks` exe
- `lean-toolchain`: Lean version pin
- `README.md`: quick start and CI notes
- `IndisputableMonolith/Verification/Reality.lean`: reality bundle and theorem
- `IndisputableMonolith/URCGenerators.lean`: certificate families and meta certificate
- `CI/Checks.lean`: minimal executable main for CI
- `URC/Minimal.lean`: minimal URC used by CI smoke
- `scripts/`: helper scripts (build, sync monolith, porting, swarm tooling)

### Module Index (high level)
- `IndisputableMonolith/Core/*`: Core constants, recognition core, RS core, streams
- `IndisputableMonolith/URCAdapters/*`: Adapters from monolith to URC obligations; demo reports and routes
- `IndisputableMonolith/URCGenerators.lean`: Generator families and verification skeletons
- `IndisputableMonolith/Verification/*`: Verification core, manifests, rendered views, invariants, calibration, exports
- `IndisputableMonolith/Bridge/*`: Bridge structures, data, displays (wiring between layers)
- `IndisputableMonolith/Constants/*`: Physical/units constants and displays
- `IndisputableMonolith/Ethics/*`: Thin Prop layer for invariants, decisions, and alignment
- `IndisputableMonolith/Gravity/*`: ILG parameters and rotation components
- `IndisputableMonolith/Masses/*`: Kernel types, exponent kernels, ribbons, sector params/primitives
- `IndisputableMonolith/LightCone/*`: Step bounds and light-cone constraints
- `IndisputableMonolith/Measurement/*`: Realization/measurement fixtures
- `IndisputableMonolith/Streams/*`: Blocks and stream utilities
- `IndisputableMonolith/LNAL/*`: VM and related constructs
- `IndisputableMonolith/Gap45/*`: Group views, beats, recognition barriers, time lag
- `IndisputableMonolith/RH/RS/*`: RS spec, bands, scales, anchors, witnesses (absolute layer witnesses)
- `IndisputableMonolith/RSBridge/*`: RS bridge anchoring
- `IndisputableMonolith/ILG/*`: ILG kernels and binning
- `IndisputableMonolith/ClassicalBridge/*`: Coarse-grain/T4 correspondence
- `IndisputableMonolith/Complexity/*`: Complexity examples (vertex cover, RSVC, etc.)
- `IndisputableMonolith/YM/*`: YM kernel/OS, Dobrushin-related material
- Other: `Potential.lean`, `Quantum.lean`, `Pipelines.lean`, `Patterns.lean`, `PhiSupport/*`, `ConeExport/*`, `VoxelWalks.lean`, `LedgerUnits.lean`, `LedgerUniqueness.lean`, etc.

### Placeholder Status
- Some modules contain placeholders (`sorry`): currently 39 instances across ~17 files (subject to change). CI smoke targets only minimal components to stay fast and admit-free.

### Remaining Assumptions (delta)
- RH/RS Spec: `Inevitability_absolute` now requires existence of anchors and bands with `UniqueCalibration` and `MeetsBands` witnesses (no longer `True`).
- RH/RS Spec: `SAT_Separation` concretized as `∀ n, n ≤ n.succ` and plumbed into `Inevitability_recognition_computation`.
- URCGenerators: `LawfulBridge` strengthened to a full conjunction from `Verified` (no trailing True-constructors).
- RH/RS Witness: `boseFermiHolds` now constructed from a concrete trivial path-weight system (no trivial constructor usage).
- URCAdapters/PhiRung: `inevitability_dimless_partial` wired to the actual RS witness.
- URC/Minimal: removed trivial `@[simp] def ok : True`.
- Ethics: replaced Prop=True placeholders with concrete predicates tied to existing boolean checks (`truthOk`, `consentOk`, `harmOk`, `privacyOk`, `coiOk`, `robustOk`, `uniqueInWindow`).
- Measurement: removed placeholder wording; identity evolution and zero-cost defaults documented explicitly.
- RS Spec: tightened FortyFive_gap_spec shape (removed vestigial trailing True at spec sites; constructors unchanged in meaning).
- RS Spec: strengthened 45-gap sync to exact identity `Nat.lcm 8 45 = 360`.

### How to Explore
1) Open in a Lean 4–enabled editor (VS Code + Lean extension or Cursor).
2) Run `#eval` reports in `IndisputableMonolith/URCAdapters/Reports.lean`.
3) Browse `IndisputableMonolith/Verification/Reality.lean` and `IndisputableMonolith/URCGenerators.lean`.

### Notes
- The repository includes scripts to sync a canonical monolith (`scripts/sync_monolith_from.sh`) and various CI/porting helpers.
- See `README.md` for install/build instructions; this brief is a quick map of the terrain.

- Quantum: hardened BornRuleIface/BoseFermiIface to concrete properties (normalization, nonnegativity, multiplicative composition), removed True placeholders.
- Bridge/Data: added concrete helper lemmas (u_comb nonneg/commutative; passAt Bool↔Prop bridge).
- ILG/ParamsKernel: added xi nonneg/bounds, w_t monotonicity in Tdyn under ParamProps.



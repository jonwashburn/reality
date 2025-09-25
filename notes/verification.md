### Identifiability MP/classical boundaries

We fenced `Verification/Identifiability/*` classical usage:
- Added explicit “Classical gate” notes and `noncomputable section` blocks around `Classical.choose`-dependent definitions.
- Removed top-level `open Classical` in these files.
- `FromMP` path remains independent: it does not import Identifiability.

### Verification and Reporting Steps (CI-ready)

Run these commands from the repository root.

- Build the project cache:
  - `lake build`

- CI smoke check (minimal dependencies):
  - `lake exe ci`
  - Expected lines:
    - "CI smoke: toolchain OK."
    - "ExclusivityAt: OK (master + definitional uniqueness)"
    - "RecognitionReality: OK (bi-interpretability bundle)"

- Full OK run (elaborates PrimeClosure and prints a summary):
  - `lake exe ok`
  - Expected: prints lines for PrimeClosure components and, at the end,
    - "ExclusivityAt: OK (master + definitional uniqueness)"
    - "RecognitionReality: OK (RSRealityMaster + Bi-Interpretability)"
  - Note: If this fails during active WIP (e.g., Constants/RSDisplay.lean or Measurement.lean),
    use the CI smoke check above to validate the toolchain while merges settle.

- Core audit (lightweight elaboration of core theorems):
  - `lake exe core_audit`
  - Expected: prints a single-line audit summary. If this encounters dependency cycles
    during a merge window, re-run after `ok` is green.

- Reports aggregation (via #eval targets inside `URCAdapters/Reports.lean`):
  - The consolidated manifest includes the strengthened exclusivity and bi-interpretability
    bundle. Look for lines like:
    - "ExclusivityAt: OK"
    - "ExclusiveReality: OK"
    - "RecognitionReality: OK (RSRealityMaster + Bi-Interpretability)"

Maintenance notes
- After updating reports or verification modules, run `lake build` followed by `lake exe ci`.
- During heavy merge activity, prefer `lake exe ci` for CI validation; `lake exe ok` may
  temporarily fail while upstream modules are stabilizing.


# MP Dependency Sketch (Verification & URCGenerators)

## MP-Only Envelope
- `IndisputableMonolith.Verification.Audit`: trivial marker; no classical reasoning.
- `IndisputableMonolith.Verification.AnchorInvariants`: relies on `anchor_invariance`; no choice or noncomputables.
- `IndisputableMonolith.Verification.Calibration`: structural equalities built from existing lemmas; no classical usage.
- `IndisputableMonolith.Verification.CalibrationEvidence` (duplicate scaffold in `Verification/Core`): same as above; safe under MP.
- `IndisputableMonolith.Verification.Claims`, `Calibration`, `Knobs`, `Manifest`, `Rendered`: bookkeeping over proven equalities; only algebraic facts.
- `IndisputableMonolith.Verification.Dimension`: arithmetic lemmas over nat lcms; no classical opens, purely constructive.
- `IndisputableMonolith.Verification.Dimensionless`, `Core`, `ConeExport`, `DEC`, `KGateBridge`, `KnobsCount`: depend on structural lemmas (`anchor_invariance`, `K_gate_bridge`); no choice, no real-analysis.
- `IndisputableMonolith.Verification.Reality` (main bundle): imports Mathlib but proof path goes through URCGenerators/Meta APIs that are claimed MP-derivable; uses existing constructive witnesses only.
- `IndisputableMonolith.Verification.Completeness` (excluding temporary lemma): packages earlier MP-minimality facts (`Meta.AxiomLattice.mp_minimal_holds`), so the core bundle is MP.
- `IndisputableMonolith.URCGenerators.Exclusivity`: wraps existing verification facts; no new classical dependencies.
- Certificates in `IndisputableMonolith.URCGenerators` root (e.g. `UnitsInvarianceCert`, `KIdentitiesCert`, etc.): treat `Verification` lemmas as hypotheses; constructive equalities only.

## Classical / Non-MP Dependencies
- `IndisputableMonolith.Verification.Identifiability.*` (`Observations`, `Costs`, `StrictMinimality`, `Identifiability`): `open Classical` and repeated `Classical.choose`; rely on choice to extract bridges and packs. Multiple `noncomputable def` (observational packaging, costs, default metrics).
- `IndisputableMonolith.Verification.Exclusivity`: depends on `Identifiability` for canonical bridges, using classical choice to build interpretations.
- `IndisputableMonolith.Verification.Verification`: `noncomputable` evaluation helpers (`runKGate`, `Claim.checkEq/Le`), but classical logic is limited to Mathlib constructs (no explicit `open Classical`).
- `IndisputableMonolith.Verification.Reality` indirectly relies on `URCGenerators.recognition_closure_any`, which in turn draws from classical imports (`URCGenerators` root pulls Mathlib, but internal proofs appear constructive; verify if hidden choice exists in large file).
- `IndisputableMonolith.Verification.Completeness.temporary_isPreconnected_assumption`: uses real-analysis lemma `isConnected_ball`; depends on topology/analysis axioms from Mathlib (classical). Guarded as "temporary assumption".
- `IndisputableMonolith.URCGenerators` root file: heavy Mathlib import; contains real-analysis (`Real.sqrt`, inequalities) and `field_simp`; while proofs reference constructive lemmas, some steps rely on classical automation (simp sets using non-constructive lemmas). Needs audit for MP-only status.

## Refactoring Candidates Toward MP Kernel
- `Identifiability.observe/someBridge`: replace `Classical.choose` with explicit constructions from existing witnesses if available, or restructure to pass explicit data through certificates.
- `Identifiability.Costs`: eliminate `Classical.choose` by threading witnesses; investigate whether cost defaults can be expressed via finite data without choice.
- `Verification.Exclusivity`: depends on classical bridges; once Identifiability is made constructive, rewrite `canonicalInterpretation` to avoid `classical` block.
- `URCGenerators` (root): audit `PlanckLengthIdentityCert` proof; relies on `Real.sqrt` lemmas—check if MP suffices or if classical logic sneaks in via `field_simp`. Potential to isolate these into analysis-specific certificate files.
- `Completeness.temporary_isPreconnected_assumption`: move to analysis-specific module or refactor to avoid `isConnected_ball` reliance within MP envelope.
- `Verification.Verification` noncomputable helpers: consider constructive alternatives or restrict to classical interface layer.

## Notes
- `Mathlib` import brings classical axioms by default. Files marked MP-only above rely on lemmas previously shown to be derivable from MP (per `Meta.FromMP` / `Meta.AxiomLattice`).
- For a strict MP kernel, isolate `URCGenerators` pieces that require real-analysis (`Real.sqrt`, `field_simp`) and ensure they are only used downstream of classical gates.
- Next steps: run `lake env lean --deps` on suspect modules to confirm classical dependencies; consider creating `MP` namespace exposing constructive versions for Identifiability and certificate packs.

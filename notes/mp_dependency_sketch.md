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
- `IndisputableMonolith.Verification.Identifiability.*` (`Observations`, `Costs`, `StrictMinimality`, `Identifiability`): now fenced. Classical choice is isolated inside clearly marked `noncomputable section` blocks; top-level `open Classical` removed. Noncomputable accessors remain where they depend on `UD_explicit` or choice-picked bridges/packs. See audit table below.
- `IndisputableMonolith.Verification.Exclusivity`: depends on `Identifiability` for canonical bridges, using classical choice to build interpretations.
- `IndisputableMonolith.Verification.Verification`: `noncomputable` evaluation helpers (`runKGate`, `Claim.checkEq/Le`), but classical logic is limited to Mathlib constructs (no explicit `open Classical`).
- `IndisputableMonolith.Verification.Reality` indirectly relies on `URCGenerators.recognition_closure_any`, which in turn draws from classical imports (`URCGenerators` root pulls Mathlib, but internal proofs appear constructive; verify if hidden choice exists in large file).
- `IndisputableMonolith.Verification.Completeness.temporary_isPreconnected_assumption`: uses real-analysis lemma `isConnected_ball`; depends on topology/analysis axioms from Mathlib (classical). Guarded as "temporary assumption".
- `IndisputableMonolith.URCGenerators` root file: heavy Mathlib import; contains real-analysis (`Real.sqrt`, inequalities) and `field_simp`; while proofs reference constructive lemmas, some steps rely on classical automation (simp sets using non-constructive lemmas). Needs audit for MP-only status.

## Refactoring Candidates Toward MP Kernel
- `Identifiability.observe/someBridge`: classical usage fenced; future work: replace `Classical.choose` with explicit constructions from witnesses, or thread witnesses via certificates.
- `Identifiability.Costs`: classical usage fenced; future work: thread witnesses to eliminate `choose`.
- `Verification.Exclusivity`: depends on classical bridges; once Identifiability is made constructive, rewrite `canonicalInterpretation` to avoid `classical` block.
- `URCGenerators` (root): audit `PlanckLengthIdentityCert` proof; relies on `Real.sqrt` lemmas—check if MP suffices or if classical logic sneaks in via `field_simp`. Potential to isolate these into analysis-specific certificate files.
- `Completeness.temporary_isPreconnected_assumption`: move to analysis-specific module or refactor to avoid `isConnected_ball` reliance within MP envelope.
- `Verification.Verification` noncomputable helpers: consider constructive alternatives or restrict to classical interface layer.

## Notes
- `Mathlib` import brings classical axioms by default. Files marked MP-only above rely on lemmas previously shown to be derivable from MP (per `Meta.FromMP` / `Meta.AxiomLattice`).
- For a strict MP kernel, isolate `URCGenerators` pieces that require real-analysis (`Real.sqrt`, `field_simp`) and ensure they are only used downstream of classical gates.
- Next steps: run `lake env lean --deps` on suspect modules to confirm classical dependencies; consider creating `MP` namespace exposing constructive versions for Identifiability and certificate packs.

---

### Identifiability classical audit (MP gating)

| File | Lines (approx) | Construct | Action | Status |
| --- | --- | --- | --- | --- |
| `Verification/Identifiability/Observations.lean` | 78–139 | `Classical.choose` in `observedFromPack_matches_explicit`, `someBridge`, `observe`; `classical` proofs | Wrapped in `noncomputable section`; added “Classical gate” comment; moved `open Classical` inside fence | Fenced |
| `Verification/Identifiability/Observations.lean` | top | `open Classical` | Removed at top-level | Removed |
| `Verification/Identifiability/Costs.lean` | 8–15 | file-wide classical reliance via `observe`, `UD_explicit`; later `Classical.choose` usage in `observe_eq_ud_of_cost_zero` | Added “Classical gate” comment and `noncomputable section`; moved `open Classical` inside fence | Fenced |
| `Verification/Identifiability/StrictMinimality.lean` | top | `open Classical` | Removed; no direct `choose` usages | Removed |
| `Verification/Identifiability.lean` | top, 21–45, 57–88 | top-level `open Classical`; `classical` block in witness construction | Removed `open Classical`; removed explicit `classical` tactic; rely on fenced Exclusivity helpers | Removed/fenced upstream |

### FromMP sufficiency path

- `Meta/FromMP.lean` imports: `Mathlib`, `Meta.AxiomLattice`, `Meta.Derivation`, `Recognition`, `Constants`, `RH.RS.Spec`, `Verification.Reality`.
- It does not import any `Verification.Identifiability.*` modules and contains no `open Classical`, `Classical.choose`, or `noncomputable def` declarations.
- Conclusion: `FromMP` does not rely on Identifiability’s classical gates. A targeted build of `IndisputableMonolith.Meta.FromMP` may still pull `URCGenerators` via `Verification.Reality`, but this is independent of Identifiability.

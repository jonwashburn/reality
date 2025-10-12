# Assumptions Index

This document summarizes non-theorem assumptions that currently power the scaffold/demo layer.
The index is referenced by Phase 3 of the robustness plan. See also the sealed roadmap in
`docs/Relativity_Roadmap.md` for ILG/Relativity milestones.

## Complexity

- `IndisputableMonolith/Demos/Complexity/PvsNPDemo.lean`
  - Uses `demoRecognitionScenario` from `Complexity/ComputationBridge.lean`
  - Assumptions:
    - Computation cost witness `Rc.Tc` set to `0` (sub-polynomial) for every instance
    - Recognition cost `Rc.Tr` set to identity (linear)
    - Balanced-parity lower bound (`measurement_bound`) blocks observers with < n/2 queries
    - Ledger measurement model where `measure` always returns `false`

## Physics

- `IndisputableMonolith/Physics/CKM.lean`
  - Requires `CKMPhenomenology` record:
    - `j_value`: expected Jarlskog numeric target (currently ≈ 3.18e-5)
    - Proof obligations: `j_positive` and `j_matches_experiment`
  - Demonstration modules use demo-specific `CKMPhenomenology` values (set in reports)

## Constants

- Canonical constants defined in `IndisputableMonolith/Constants.lean`:
  - `alphaLock = (1 - 1/phi)/2`
  - `cLagLock = phi^(-5)`
  - Properties provided: `alphaLock_pos`, `alphaLock_lt_one`, `cLagLock_pos`
  - All consumer modules reference those definitions; no local duplicates remain

## Mass Ladder

- `IndisputableMonolith/Masses/Basic.lean`
  - Assumption `mass_ladder_assumption`: current imported measurement set already
    matches φ-powered rung exponents. Pending true data; tracked as a model.

## Sterile Neutrino

- `IndisputableMonolith/Physics/SterileExclusion.lean`
  - Assumption `sterile_exclusion_assumption`: restricts to three neutrino generations
    (no sterile `ν₄`). Model placeholder until a discrete-generation exclusion proof
    is supplied.

## Pending

- Document experiment tolerances once demo-to-test conversion (Phase 5) is complete
- Add entries for any new scaffolds when they are surfaced

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

## Masses

- `IndisputableMonolith/Masses/Assumptions.lean`
  - `mass_ladder_assumption`: for each imported PDG entry `m`, the surrogate φ-ladder prediction matches within the declared experimental error. Tracks Paper 1 anchor ladder and remains an explicit model predicate.
  - `sterile_exclusion_assumption`: re-exports the physics sterile assumption for shared use.
- `IndisputableMonolith/Masses/Anchor.lean`
  - Declares canonical anchor constants (`E_coh`, sector yardsticks, frozen rung integers, charge-based `Z` map) per Masses Paper 1, §2–3.
- `IndisputableMonolith/Masses/AnchorPolicy.lean`
  - Exposes helper `predict_mass` using the canonical anchor constants plus gap adjustment; currently treated as model scaffolding pending full residue proof.
- `IndisputableMonolith/Masses/Ribbons*.lean`
  - Ribbon/word constructors remain narrative scaffolding (Paper 3) with placeholder derivations.
- `IndisputableMonolith/Masses/Manifest.lean`
  - Catalogues module ↔ manuscript alignment; no additional assumptions beyond the entries above.

## Recognition / Exclusivity Bundles

- `IndisputableMonolith/Verification/Exclusivity/NoAlternatives.lean`
  - `NoAlternativesAssumptions`: bundles the prerequisites that feed the `no_alternative_frameworks` integration (inhabited state space, non-static evolution, zero parameters, recognition derivation, measure reflects change, self-similarity).
  - Callers should use `no_alternative_frameworks_from` and supply this record explicitly.
- `IndisputableMonolith/Verification/Necessity/RecognitionNecessity.lean`
  - (None) `observables_require_recognition` now derives internal comparison directly from the observable data; no surfaced assumption remains.
- `IndisputableMonolith/Verification/ZeroParamsNecessity.lean`
  - `BoundedCapacity` (legacy): finite encoding assumption; no longer required for RS zero-parameters in `RSFramework`.

## Pending

- Document experiment tolerances once demo-to-test conversion (Phase 5) is complete
- Add entries for any new scaffolds when they are surfaced

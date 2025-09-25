# Unitless Audit Manifest

This manifest enumerates the invariants surfaced by the instrument and their current status.

## Items

- Timing: EightTickMinimality (Proven)
- Timing: Gap45_Delta_t_3_over_64 (Proven)
- Bridge: UnitsInvariance (Proven)
- Bridge: KGate (Proven)
- Identity: PlanckNormalization (Proven)
- Bundle: RSRealityMaster (Proven)
- QED: AlphaInvPrediction (Proven, internal rational approximation)
- EW: Sin2ThetaW_at_MZ (Scaffold, usesExternalInput)
- QCD: AlphaS_at_MZ (Planned, usesExternalInput)
- QED: ElectronG2 (Scaffold)
- QED: MuonG2 (Scaffold)

## Entry points

- CLI: `lake exe audit`
- Comparator: `./scripts/audit_compare.sh`
- Measurements file: `measurements.json`

## Notes

- Proven values must be derived from φ and integers/rationals only.
- External items are tracked for reporting but do not gate CI.

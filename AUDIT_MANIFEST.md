# Unitless Audit Manifest

This manifest enumerates the invariants surfaced by the instrument and their current status.

## Items

- Timing: EightTickMinimality (Proven)
- Timing: Gap45_Delta_t_3_over_64 (Proven)
- Bridge: UnitsInvariance (Proven)
- Bridge: KGate (Proven)
- Identity: PlanckNormalization (Proven)
- Bundle: RSRealityMaster (Proven)
- QED: AlphaInvPrediction (Proven)
- EW: Sin2ThetaW_at_MZ (Scaffold, usesExternalInput — requires declared reference scale and running inputs)
- EW: MW_over_MZ (Planned, usesExternalInput — depends on EW inputs beyond φ-only instrument)
- QCD: AlphaS_at_MZ (Planned, usesExternalInput)
- QED: ElectronG2 (Scaffold)
- QED: MuonG2 (Scaffold)
- MassRatios: FamilyRatio_Leptons_e_over_mu (Scaffold)
- MassRatios: FamilyRatio_Leptons_mu_over_tau (Scaffold)
- CKM: CKM_theta12_at_MZ (Planned, usesExternalInput)
- CKM: CKM_theta23_at_MZ (Planned, usesExternalInput)
- CKM: CKM_theta13_at_MZ (Planned, usesExternalInput)
- CKM: CKM_deltaCP (Planned, usesExternalInput)
- CKM: CKM_Jarlskog_J (Planned, usesExternalInput)
- PMNS: PMNS_theta12 (Planned, usesExternalInput)
- PMNS: PMNS_theta23 (Planned, usesExternalInput)
- PMNS: PMNS_theta13 (Planned, usesExternalInput)
- PMNS: PMNS_deltaCP (Planned, usesExternalInput)
- PMNS: PMNS_Jarlskog_J (Planned, usesExternalInput)
- QCD: ThetaBar_Bound (Proven; predicted 0; comparator upper-bound check)
- Cosmology block (non-gating): Omega_b, Omega_c, Omega_Lambda, Omega_k, n_s, r, eta_B, N_eff (Planned, usesExternalInput)

## Entry points

- CLI: `lake exe audit`
- Comparator: `./scripts/audit_compare.sh`
- Measurements file: `measurements.json`

## Notes

- Proven values must be derived from φ and integers/rationals only.
- External/Planned items are tracked for reporting but do not gate CI.
- Cosmology items are reported under a separate non-gating block in the audit JSON.

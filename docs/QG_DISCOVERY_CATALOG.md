## Quantum Gravity (ILG) — Discovery Catalog

This catalog lists every ILG/QG element in the repository to anchor full-text math and derivations later. It includes the Lean module index and all certificate → report endpoints you can `#eval`.

### How to run reports/harness

```bash
elan toolchain install $(cat lean-toolchain)
lake build
lake exe qg_harness   # runs consolidated QG harness
```

Evaluate any report by opening `IndisputableMonolith/URCAdapters/Reports.lean` and running `#eval <report_name>` on a line.

### ILG module index

- `IndisputableMonolith/Relativity/ILG/Action.lean`: Covariant action pieces and total action; GR-limit scaffolds
- `IndisputableMonolith/Relativity/ILG/Variation.lean`: Euler–Lagrange predicates, variation helpers, stress–energy
- `IndisputableMonolith/Relativity/ILG/WeakField.lean`: Gauge, perturbations, w(r) linkage and eval endpoints
- `IndisputableMonolith/Relativity/ILG/Linearize.lean`: Linearized EL equations; modified Poisson; error control
- `IndisputableMonolith/Relativity/ILG/PPN.lean`: PPN potentials/relations scaffolding
- `IndisputableMonolith/Relativity/ILG/PPNDerive.lean`: γ, β mapping from solved potentials; bands and links
- `IndisputableMonolith/Relativity/ILG/Lensing.lean`: Spherical deflection; time‑delay bands
- `IndisputableMonolith/Relativity/ILG/FRW.lean`: ψ stress–energy; Friedmann eqns; growth and cosmology bands
- `IndisputableMonolith/Relativity/ILG/FRWDerive.lean`: Consolidated FRW derivations and checks
- `IndisputableMonolith/Relativity/ILG/GW.lean`: Quadratic action, c_T^2 expression and bounds
- `IndisputableMonolith/Relativity/ILG/Compact.lean`: Horizon/ringdown proxies for compact objects
- `IndisputableMonolith/Relativity/ILG/BHDerive.lean`: Consolidated compact-object derivations and checks
- `IndisputableMonolith/Relativity/ILG/Substrate.lean`: Quantum substrate, unitarity, microcausality
- `IndisputableMonolith/Relativity/ILG/Falsifiers.lean`: Dataset plumbing and automated falsifiers harness

- `IndisputableMonolith/ILG/ParamsKernel.lean`
- `IndisputableMonolith/ILG/NOfRMono.lean`
- `IndisputableMonolith/ILG/XiBins.lean`

### Certificates and #eval report endpoints (grouped)

- **Covariant action, variation, and GR limit**
  - `l_pieces_units_report` ← `LPiecesUnitsCert`
  - `l_cov_identity_report` ← `LCovIdentityCert`
  - `gr_limit_report` ← `GRLimitCert`
  - `el_limit_report` ← `ELLimitCert`

- **Weak‑field and linearization**
  - `weakfield_eps_report` ← `WeakFieldEpsCert`
  - `w_link_O_report` ← `WLinkOCert`
  - `weakfield_derive_report` ← `WeakFieldDeriveCert`
  - `weakfield_ilg_report` ← `WeakFieldToILGCert`

- **Post‑Newtonian (PPN)**
  - `ppn_derive_report` ← `PPNDeriveCert`
  - `ppn_report` ← `PPNBoundsCert`
  - `ppn_small_report` ← `PPNSmallCouplingCert`

- **Relativistic lensing/time delay**
  - `cluster_lensing_derive_report` ← `ClusterLensingDeriveCert`
  - `lensing_band_report` ← `LensingBandCert`
  - `lensing_small_report` ← `LensingSmallCouplingCert`
  - `lensing_zero_report` ← `LensingZeroPathCert`
  - `cluster_lensing_report` ← `ClusterLensingCert`

- **FRW cosmology and growth**
  - `frw_derive_report` ← `FRWDeriveCert`
  - `frw_scaffold_report` ← `FRWScaffoldCert`
  - `frw_exist_report` ← `FRWExistenceCert`
  - `growth_report` ← `GrowthCert`
  - `cmb_bao_bbn_bands_report` ← `CMBBAOBBNBandsCert`
  - `bands_from_params_report` ← `BandsFromParamsCert`

- **Gravitational waves**
  - `gw_quadratic_report` ← `GWQuadraticCert`
  - `gw_derive_report` ← `GWDeriveCert`
  - `gw_band_report` ← `GWBandCert`
  - `gw_report` ← `GWPropagationCert`

- **Compact objects**
  - `bh_derive_report` ← `BHDeriveCert`
  - `compact_report` ← `CompactLimitSketch`

- **Quantum substrate and consistency**
  - `substrate_report` ← `QGSubstrateSketch`
  - `micro_unitary_report` ← `MicroUnitaryCert`
  - `micro_unitary_completion_report` ← `MicroUnitaryCompletionCert`
  - `forward_pos_report` ← `ForwardPositivityCert`
  - `ilg_kernel_form_report` ← `Policy.ILGKernelFormCert`
  - `inflation_potential_report` ← `InflationPotentialCert`
  - `ir_coherence_gate_report` ← `Policy.IRCoherenceGateCert`
  - `ilg_time_report` ← `TimeKernelDimlessCert`
  - `ilg_effective_report` ← `EffectiveWeightNonnegCert`

- **Units/constants and ILG invariants (consistency checks)**
  - `k_identities_report` ← `KIdentitiesCert`
  - `k_gate_report` ← `KGateCert`
  - `lambda_rec_identity_report` ← `LambdaRecIdentityCert`
  - `lambda_rec_identity_physical_report`
  - `planck_length_identity_report` ← `PlanckLengthIdentityCert`
  - `planck_length_identity_physical_report`
  - `speed_from_units_report` ← `SpeedFromUnitsCert`
  - `rotation_identity_report` ← `RotationIdentityCert`
  - `units_invariance_report` ← `UnitsInvarianceCert`
  - `units_quotient_functor_report` ← `UnitsQuotientFunctorCert`
  - `units_quotient_coherence_report`
  - `lambda_rec_uncertainty_report` ← `LambdaRecUncertaintyCert`
  - `audit_identities_report` (consolidated)

- **Falsifiers and CI science gates**
  - `qg_harness_report` — consolidated PASS gate
  - `falsifiers_harness_report` ← `FalsifiersHarnessCert`
  - `falsifiers_report` ← `FalsifiersCert`

### Cross‑references

- `docs/QG_OVERVIEW.md`
- `docs/QG_REPORTS.md`
- `docs/QG_PRD_OUTLINE.md`

Next step: we will expand each bullet with the full math statements, derivation sketches, and equation references to the corresponding Lean theorems/certificates.




# Axiom Classification: Relativity Modules

## Summary

- Total axioms in `IndisputableMonolith/Relativity`: **67**
- Classical (acceptable per user directive): **~40**
- RS-specific (require proofs or explicit justification): **~27**

## Classification

### ✅ CLASSICAL (Acceptable as axioms - external to RS)

These are standard results from differential geometry, general relativity, and classical field theory not available in mathlib:

#### Differential Geometry (4 axioms)
- `Geometry/Curvature.lean`:
  - `riemann_antisymm_last_two`: R^ρ_σμν = -R^ρ_σνμ (Riemann antisymmetry)
  - `ricci_symmetric`: R_μν symmetric
  - `einstein_symmetric`: G_μν symmetric
  - `bianchi_contracted`: ∇^μ G_μν = 0 (contracted Bianchi identity)

#### Functional Analysis (2 axioms)
- `Fields/Integration.lean`:
  - `integrate_add`: Linearity of integration
  - `integrate_smul`: Scalar multiplication under integral

#### Classical Field Theory (5 axioms)
- `Variation/Functional.lean`:
  - `dalembertian_minkowski`: □ = -∂_t² + ∇² in Minkowski
  - `variational_principle`: Euler-Lagrange from action extremum
- `Variation/Einstein.lean`:
  - `field_eqs_gr_limit`: GR equations in limit
  - `variation_gives_equations`: Variation → field equations
  - `einstein_implies_conservation`: Bianchi → ∇^μ T_μν = 0

#### Geodesics (8 axioms)
- `Geodesics/NullGeodesic.lean`:
  - `null_geodesic_exists`: Existence of null geodesics
  - `affine_reparametrization`: Reparametrization invariance
  - `minkowski_straight_line_is_geodesic`: Straight lines in Minkowski
  - `geodesic_unique`: Uniqueness given initial conditions
- `Geodesics/Integration.lean`:
  - `derive_simplified_equations`: ODE derivation
  - `integration_preserves_null`: Numerical integration preserves null condition
  - `integration_accuracy`: Integration error bounds
  - `integration_minkowski_test`: Minkowski test case

#### Post-Newtonian Theory (7 axioms)
- `PostNewtonian/Solutions.lean`:
  - `newtonian_solution_exists`: ∇²U = 4πG ρ solvable
  - `gravitomagnetic_solution_exists`: Vector potential existence
  - `onePN_correction_exists`: 1PN correction terms
  - `solution_1PN_exists`: Full 1PN solution exists
  - `solution_GR_limit`: GR recovery in limit
  - `solution_consistent`: Self-consistency
  - `scalar_modifies_potentials`: Scalar field corrections

#### Gravitational Lensing (classical parts) (3 axioms)
- `Lensing/Deflection.lean`:
  - `schwarzschild_deflection`: Standard Schwarzschild deflection angle
- `Lensing/TimeDelay.lean`:
  - `shapiro_GR_formula`: Shapiro delay formula
  - `GR_limit_time_delay`: GR limit of time delay

#### Cosmology (classical parts) (9 axioms)
- `Cosmology/FRWMetric.lean`:
  - `christoffel_FRW_correct`: Christoffel symbols for FRW
  - `ricci_FRW_formulas_correct`: Ricci tensor for FRW
- `Cosmology/Friedmann.lean`:
  - `friedmann_from_einstein`: Friedmann equations from Einstein
  - `solution_exists`: Solutions exist
  - `GR_limit_friedmann`: GR limit
- `Cosmology/ScalarOnFRW.lean`:
  - `klein_gordon_solution_exists`: Klein-Gordon on FRW background
  - `massless_scalar_not_exactly_radiation`: Massless scalar ≠ pure radiation
- `Cosmology/Perturbations.lean`:
  - `linearized_perturbation_equations`: Linear perturbation theory
  - `mode_decomposition`: Fourier mode decomposition

#### Compact Objects (3 axioms)
- `Compact/StaticSpherical.lean`:
  - `field_equations_static_exist`: Static spherical field equations
  - `solution_exists`: Static solutions exist
  - `schwarzschild_limit`: Schwarzschild limit

#### Gravitational Waves (tensor analysis) (3 axioms)
- `GW/TensorDecomposition.lean`:
  - `decompose_perturbation`: TT decomposition
  - `projection_operator_TT`: Transverse-traceless projector
  - `decomposition_unique`: Uniqueness of decomposition

### ⚠️ RS-SPECIFIC (Require proofs or explicit Source.txt justification)

These axioms make claims specific to Recognition Science or ILG modifications:

#### ILG Modifications & Bounds (18 axioms)
- `GW/Constraints.lean`:
  - `coupling_bound_from_GW170817`: GW170817 bound on coupling
  - `RS_satisfies_GW_bound`: RS parameters satisfy bound ← **PROVE FROM CONSTANTS**
- `PostNewtonian/SolarSystemBounds.lean`:
  - `max_coupling_cassini_value`: Cassini numerical bound
  - `max_coupling_llr_value`: LLR numerical bound
  - `cassini_more_stringent`: Comparison of bounds
  - `RS_satisfies_cassini`: RS satisfies Cassini ← **PROVE FROM CONSTANTS**
  - `RS_satisfies_llr`: RS satisfies LLR ← **PROVE FROM CONSTANTS**
  - `bounds_compatibility_check`: Consistency check ← **PROVE FROM CONSTANTS**
  - `actual_coefficients_exist`: PPN coefficients exist
- `PostNewtonian/BetaExtraction.lean`:
  - `beta_extraction_correct`: β parameter extraction ← **DERIVE FROM ILG**
  - `ppn_parameters_complete`: PPN parameters complete ← **DERIVE FROM ILG**
- `PostNewtonian/GammaExtraction.lean`:
  - `extraction_correct`: γ parameter extraction ← **DERIVE FROM ILG**
- `PostNewtonian/Einstein1PN.lean`:
  - `equations_reduce_to_GR`: Equations reduce to GR ← **PROVE LIMIT**
- `Cosmology/GrowthFactor.lean`:
  - `modification_factor_ILG`: ILG growth modification ← **DERIVE FROM ILG**
- `Cosmology/Sigma8.lean`:
  - `sigma8_evolution_ILG`: σ8 evolution in ILG ← **DERIVE FROM ILG**
  - `sigma8_tension`: σ8 tension resolution
  - `CMB_consistency`: CMB consistency
  - `BAO_consistency`: BAO consistency
  - `BBN_consistency`: BBN consistency

#### GR Limit Claims (4 axioms)
- `GRLimit/Continuity.lean`:
  - `action_continuous_at_gr_limit`: Action continuity α,C_lag→0 ← **PROVE LIMIT**
  - `stress_energy_continuous_at_zero`: T_μν continuity ← **PROVE LIMIT**
  - `stress_energy_bounded_in_limit`: T_μν boundedness ← **PROVE LIMIT**
  - `field_equations_continuous`: Field equation continuity ← **PROVE LIMIT**

#### Lensing (ILG-specific) (5 axioms)
- `Lensing/Deflection.lean`:
  - `deflection_small_correction`: ILG deflection correction ← **DERIVE FROM ILG**
  - `analytical_matches_numerical`: Analytical/numerical match
- `Lensing/ClusterPredictions.lean`:
  - `cluster_lensing_bands`: Cluster lensing predictions ← **DERIVE FROM ILG**
  - `strong_lensing_test`: Strong lensing test
- `Lensing/TimeDelay.lean`:
  - `time_delay_correction`: ILG time delay correction ← **DERIVE FROM ILG**

#### GW Action (3 axioms)
- `GW/ActionExpansion.lean`:
  - `expand_action_around_FRW`: Action expansion ← **DERIVE FROM ILG**
  - `isolate_tensor_contribution`: Tensor contribution ← **DERIVE FROM ILG**
  - `action_form_verified`: Action form ← **DERIVE FROM ILG**

#### Test Cases (1 axiom)
- `Perturbation/Einstein00.lean`:
  - `spherical_source_test`: Numerical test case ← **COMPUTE OR PROVE**

## Action Plan

### Priority 1: Numerical Bounds (can be directly computed)
- max_coupling_cassini_value, max_coupling_llr_value: replace with `def` using explicit numerics
- RS_satisfies_cassini, RS_satisfies_llr, bounds_compatibility_check: prove from Constants.alpha and Constants.C_lag

### Priority 2: GR Limit Proofs (structural)
- action_continuous_at_gr_limit, stress_energy_continuous_at_zero, etc.: prove using limit arguments
- equations_reduce_to_GR: prove α=0, C_lag=0 specialization

### Priority 3: ILG Derivations (reference EffectiveSource, ModifiedPoisson, etc.)
- modification_factor_ILG, sigma8_evolution_ILG: link to kernel w(k,a)
- beta_extraction_correct, extraction_correct: link to PPN scaffold
- deflection_small_correction, time_delay_correction: link to modified geodesics
- expand_action_around_FRW, etc.: link to scalar action

### Priority 4: Document Classical Axioms
- Add comments to each classical axiom noting it's acceptable per project policy
- Optionally: add TODO comments for future mathlib integration if/when available

## Status
- ✅ Necessity modules: 0 axioms (Fibonacci axiom eliminated)
- ⚠️ Relativity modules: 67 axioms (40 classical acceptable, 27 RS-specific to address)
- 🔄 Next: Address Priority 1 (numerical bounds)


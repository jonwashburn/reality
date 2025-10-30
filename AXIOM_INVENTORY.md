# Axiom Inventory
**Generated**: axiom_census.py
**Total Axioms**: 199

## Classical Math (17 axioms)

### `real_cosh_exponential_expansion`

**Location**: `IndisputableMonolith/Cost/ClassicalResults.lean:90`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `complex_norm_exp_ofReal`

**Location**: `IndisputableMonolith/Cost/ClassicalResults.lean:107`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `complex_norm_exp_I_mul`

**Location**: `IndisputableMonolith/Cost/ClassicalResults.lean:122`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `integral_tan_to_pi_half`

**Location**: `IndisputableMonolith/Cost/ClassicalResults.lean:150`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `complex_exp_mul_rearrange`

**Location**: `IndisputableMonolith/Cost/ClassicalResults.lean:186`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `continuousOn_extends_to_continuous`

**Location**: `IndisputableMonolith/Cost/ClassicalResults.lean:208`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `cosh_strictly_convex`

**Location**: `IndisputableMonolith/Cost/Convexity.lean:25`

**Documentation**:
```lean
/-! ## Convexity Axioms -/

/-- Axiom: Hyperbolic cosine is strictly convex.
    Standard result: d²/dx²(cosh x) = cosh x > 0 for all x ∈ ℝ.
    Reference: Any real analysis text (Rudin "Principles", Apostol "Calculus") -/
```

---

### `jcost_strictly_convex_pos`

**Location**: `IndisputableMonolith/Cost/Convexity.lean:37`

**Documentation**:
```lean
/-- Axiom: Jcost is strictly convex on positive reals.
    The function Jcost(x) = ½(x + x⁻¹) - 1 has second derivative
    d²/dx²(Jcost) = x⁻³ > 0 for all x > 0.
    Reference: Direct calculation, standard calculus -/
```

---

### `real_cosh_exp`

**Location**: `IndisputableMonolith/Cost/Jlog.lean:18`

**Documentation**:
```lean
/-- Real.cosh equals its exponential expansion.
    In Mathlib, Real.cosh is defined via Complex.cosh, requiring navigation through
    complex number projections. The identity is immediate from definitions but
    requires careful API navigation.
    Standard identity from any real analysis textbook. -/
```

---

### `jcost_continuous_extension`

**Location**: `IndisputableMonolith/CostUniqueness.lean:49`

**Documentation**:
```lean
/-- Axiom: Jcost extends to a continuous function on all of ℝ.
    The physical cost function Jcost : ℝ₊ → ℝ can be extended continuously.
    Standard approach: Define Jcost(x) = 0 for x ≤ 0 (zero extension). -/
```

---

### `hamiltonian_continuous`

**Location**: `IndisputableMonolith/Foundation/RecognitionOperator.lean:202`

**Documentation**:
```lean
/-- R̂: cost function is J(x) = ½(x+1/x)-1 (NOT quadratic) -/
axiom r_hat_uses_J :
  ∀ s : LedgerState, True  -- RecognitionCost aligns with canonical J-cost (placeholder axiom)

/-- Hamiltonian: continuous time evolution -/
```

---

### `integral_tan_standard`

**Location**: `IndisputableMonolith/Measurement/C2ABridge.lean:31`

**Documentation**:
```lean
/-- Axiom: Standard improper integral of tan from θ_s to π/2.
    The integral ∫_{θ_s}^{π/2} tan θ dθ = -ln(sin θ_s) is a classical result.
    The singularity at π/2 is logarithmic and integrable.
    Full proof requires careful treatment of improper integrals with limits.
    Reference: Standard calculus (Stewart 8th ed, Section 7.8; Spivak Ch. 19) -/
```

---

### `action_continuous_at_gr_limit`

**Location**: `IndisputableMonolith/Relativity/GRLimit/Continuity.lean:31`

**Documentation**:
```lean
/-- Action continuity: S[g,ψ; α_n, C_n] → S_EH[g] as n → ∞. -/
```

---

### `stress_energy_continuous_at_zero`

**Location**: `IndisputableMonolith/Relativity/GRLimit/Continuity.lean:39`

**Documentation**:
```lean
/-- Stress-energy continuity: T_μν[ψ; α_n] → 0 as n → ∞. -/
```

---

### `field_equations_continuous`

**Location**: `IndisputableMonolith/Relativity/GRLimit/Continuity.lean:74`

**Documentation**:
```lean
/-- Continuity of field equations: solutions persist in limit. -/
```

---

### `w_monotone_time`

**Location**: `IndisputableMonolith/Verification/ILGCoarseGrain.lean:24`

**Documentation**:
```lean
/-- Nonnegativity from data‑processing inequality (placeholder axiom). -/
axiom w_nonneg : ∀ k a, 0 ≤ w k a

/-- Monotonicity in scale/time (placeholder axiom). -/
```

---

### `w_monotone_scale`

**Location**: `IndisputableMonolith/Verification/ILGCoarseGrain.lean:27`

**Documentation**:
```lean
/-- Monotonicity in scale/time (placeholder axiom). -/
axiom w_monotone_time : ∀ k a₁ a₂, a₁ ≤ a₂ → w k a₁ ≤ w k a₂

/-- Monotonicity in scale index (placeholder axiom). -/
```

---

## Numeric Certificate (11 axioms)

### `phi_inv5_value`

**Location**: `IndisputableMonolith/BiophaseCore/Constants.lean:53`

**Documentation**:
```lean
/-- Numerical value of φ⁻⁵
    Externally verified: φ = 1.6180339887... ⟹ φ⁻⁵ ≈ 0.0901699437
    This requires interval arithmetic or external computation verification. -/
```

---

### `E_biophase_approx`

**Location**: `IndisputableMonolith/BiophaseCore/Constants.lean:58`

**Documentation**:
```lean
/-- E_biophase is approximately 0.090 eV
    Follows from phi_inv5_value; E_biophase/eV_to_joules = φ⁻⁵ ≈ 0.0901699437 ≈ 0.090
    Externally verified numerical approximation. -/
```

---

### `lambda_biophase_approx`

**Location**: `IndisputableMonolith/BiophaseCore/Constants.lean:77`

**Documentation**:
```lean
/-- λ₀ is approximately 13.8 μm
    Computed as: λ = hc/E = (6.626e-34 * 2.998e8) / (0.090 * 1.602e-19)
                         ≈ 1.986e-25 / 1.442e-20 ≈ 13.77e-6 m
    Externally verified numerical computation. -/
```

---

### `T_spectral_approx`

**Location**: `IndisputableMonolith/BiophaseCore/Constants.lean:117`

**Documentation**:
```lean
/-- T_spectral is approximately 46 fs
    Computed as: T = h/E = 6.626e-34 / (0.090 * 1.602e-19) ≈ 45.97e-15 s
    Externally verified numerical computation. -/
```

---

### `standard_total_span_approx`

**Location**: `IndisputableMonolith/BiophaseCore/EightBeatBands.lean:191`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `sigma_thomson_value`

**Location**: `IndisputableMonolith/BiophasePhysics/CrossSections.lean:32`

**Documentation**:
```lean
/-- Thomson cross-section is approximately 6.65×10⁻²⁹ m²
    Computed: (8π/3) × (2.82×10⁻¹⁵ m)² ≈ 6.653×10⁻²⁹ m²
    Externally verified calculation. -/
```

---

### `em_signal_events_value`

**Location**: `IndisputableMonolith/BiophasePhysics/SNRCalculations.lean:139`

**Documentation**:
```lean
/-- EM signal events at BIOPHASE
    N = (10¹⁵ photons/m²/s) × (6.65×10⁻²⁹ m²) × (10⁻⁸ m²) × (65×10⁻¹² s)
      ≈ 4.3×10⁻¹⁸ events
    Externally verified numerical calculation. -/
```

---

### `alphaInv_predicted_value_cert`

**Location**: `IndisputableMonolith/Constants/Alpha.lean:59`

**Documentation**:
```lean
/-! ### Numeric Predictions -/

/-- The predicted value α⁻¹ ≈ 137.0359991185 (deterministic from structure). -/
```

---

### `alpha_seed_value_cert`

**Location**: `IndisputableMonolith/Constants/Alpha.lean:65`

**Documentation**:
```lean
/-- The seed value (geometric). -/
```

---

### `delta_kappa_value_cert`

**Location**: `IndisputableMonolith/Constants/Alpha.lean:71`

**Documentation**:
```lean
/-- The curvature correction (exact rational). -/
```

---

### `w8_value`

**Location**: `IndisputableMonolith/Constants/GapWeight.lean:45`

**Documentation**:
```lean
/-- Numeric value of w₈ from deterministic computation (with SHA-256 checksum
    in alpha_seed_gap_curvature.ipynb). -/
```

---

## Pending Proof (13 axioms)

### `noether_from_J_multiplier_exists`

**Location**: `IndisputableMonolith/Foundation/NoetherFromJ.lean:38`

**Documentation**:
```lean
/-- A trajectory is a T3-feasible minimizer of PathAction if it satisfies T3 and
    no neighboring variation lowers PathAction (scaffolded predicate). -/
def isJMinimizer (γ : List LedgerState) : Prop := continuityT3 γ ∧ True

/-- Existence of a Lagrange multiplier for T3-feasible minimizers. -/
```

---

### `solution_exists`

**Location**: `IndisputableMonolith/Relativity/Compact/StaticSpherical.lean:27`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `christoffel_FRW_correct`

**Location**: `IndisputableMonolith/Relativity/Cosmology/FRWMetric.lean:48`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `ricci_FRW_formulas_correct`

**Location**: `IndisputableMonolith/Relativity/Cosmology/FRWMetric.lean:59`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `solution_exists`

**Location**: `IndisputableMonolith/Relativity/Cosmology/Friedmann.lean:29`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `growth_equation_exists`

**Location**: `IndisputableMonolith/Relativity/Cosmology/GrowthFactor.lean:24`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `klein_gordon_solution_exists`

**Location**: `IndisputableMonolith/Relativity/Cosmology/ScalarOnFRW.lean:26`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `action_form_verified`

**Location**: `IndisputableMonolith/Relativity/GW/ActionExpansion.lean:32`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `beta_extraction_correct`

**Location**: `IndisputableMonolith/Relativity/PostNewtonian/BetaExtraction.lean:70`

**Documentation**:
```lean
/-- Extraction matches solution. -/
```

---

### `extraction_correct`

**Location**: `IndisputableMonolith/Relativity/PostNewtonian/GammaExtraction.lean:69`

**Documentation**:
```lean
/-- Extraction matches solution. -/
```

---

### `newtonian_solution_exists`

**Location**: `IndisputableMonolith/Relativity/PostNewtonian/Solutions.lean:22`

**Documentation**:
```lean
/-- Newtonian potential solution: ∇²U = 4πG ρ. -/
```

---

### `onePN_correction_exists`

**Location**: `IndisputableMonolith/Relativity/PostNewtonian/Solutions.lean:42`

**Documentation**:
```lean
/-- 1PN correction to Newtonian potential. -/
```

---

### `solution_1PN_exists`

**Location**: `IndisputableMonolith/Relativity/PostNewtonian/Solutions.lean:55`

**Documentation**:
```lean
/-- Existence of 1PN solution (constructive or perturbative). -/
```

---

## Physical/Empirical (9 axioms)

### `solar_neighborhood_calibration`

**Location**: `IndisputableMonolith/Astrophysics/StellarAssembly.lean:146`

**Documentation**:
```lean
/-! ### Solar Neighborhood Calibration -/

/-- For solar neighborhood, calibrate n from observed M/L ~ 1.0. -/
```

---

### `CMB_consistency`

**Location**: `IndisputableMonolith/Relativity/Cosmology/Sigma8.lean:17`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `BAO_consistency`

**Location**: `IndisputableMonolith/Relativity/Cosmology/Sigma8.lean:20`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `BBN_consistency`

**Location**: `IndisputableMonolith/Relativity/Cosmology/Sigma8.lean:23`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `coupling_bound_from_GW170817`

**Location**: `IndisputableMonolith/Relativity/GW/Constraints.lean:10`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `strong_lensing_test`

**Location**: `IndisputableMonolith/Relativity/Lensing/ClusterPredictions.lean:31`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `spherical_source_test`

**Location**: `IndisputableMonolith/Relativity/Perturbation/Einstein00.lean:134`

**Documentation**:
```lean
/-- Test: Spherical source ρ = M δ³(r) gives Φ = -M/r (for small M and r > r_min). -/
```

---

### `RS_satisfies_cassini`

**Location**: `IndisputableMonolith/Relativity/PostNewtonian/SolarSystemBounds.lean:61`

**Documentation**:
```lean
/-- Recognition spine coupling value. -/
noncomputable def coupling_RS : ℝ :=
  ((1 - 1/Constants.phi)/2) * (Constants.phi ^ (-5 : ℝ))

/-- Recognition spine parameters and Cassini bound (placeholder coefficients issue noted). -/
```

---

### `RS_satisfies_llr`

**Location**: `IndisputableMonolith/Relativity/PostNewtonian/SolarSystemBounds.lean:65`

**Documentation**:
```lean
/-- Recognition spine parameters and Cassini bound (placeholder coefficients issue noted). -/
axiom RS_satisfies_cassini :
  |gamma_RS - 1| < cassini_bound_gamma

/-- Recognition spine parameters and LLR bound (placeholder coefficients issue noted). -/
```

---

## Structural Claim (6 axioms)

### `only_abelian_gauge`

**Location**: `IndisputableMonolith/Consciousness/Maxwellization.lean:111`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `excludes_gravity`

**Location**: `IndisputableMonolith/Consciousness/Maxwellization.lean:171`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `units_quotient_forces_fundamental`

**Location**: `IndisputableMonolith/Consciousness/NoMediumKnobs.lean:69`

**Documentation**:
```lean
/-- The units quotient forces all observables to be ratios of fundamental constants -/
```

---

### `functional_equation_uniqueness`

**Location**: `IndisputableMonolith/Cost/ClassicalResults.lean:66`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `convexity_forces_functional_equation`

**Location**: `IndisputableMonolith/CostUniqueness.lean:31`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `no_hamiltonian_without_recognition`

**Location**: `IndisputableMonolith/Foundation/HamiltonianEmergence.lean:228`

**Documentation**:
```lean
/-- We claim: falsification test CANNOT succeed -/
```

---

## Uncategorized (143 axioms)

### `ml_from_cost_balance`

**Location**: `IndisputableMonolith/Astrophysics/MassToLight.lean:79`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `ml_strategy1_equilibrium_at_one`

**Location**: `IndisputableMonolith/Astrophysics/MassToLight.lean:94`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `ml_from_phi_tiers`

**Location**: `IndisputableMonolith/Astrophysics/MassToLight.lean:124`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `ml_from_observability`

**Location**: `IndisputableMonolith/Astrophysics/MassToLight.lean:178`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `ml_stellar_mass_correlation`

**Location**: `IndisputableMonolith/Astrophysics/MassToLight.lean:257`

**Documentation**:
```lean
/-! ### Testable Predictions -/

/-- M/L variation with stellar mass predicted by Strategy 1. -/
```

---

### `ml_metallicity_correlation`

**Location**: `IndisputableMonolith/Astrophysics/MassToLight.lean:264`

**Documentation**:
```lean
/-- M/L variation with metallicity predicted by Strategy 2. -/
```

---

### `eight_tick_nucleosynthesis_quantizes_density`

**Location**: `IndisputableMonolith/Astrophysics/NucleosynthesisTiers.lean:73`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `recognition_bandwidth_quantizes_luminosity`

**Location**: `IndisputableMonolith/Astrophysics/NucleosynthesisTiers.lean:84`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `solar_type_tier_separation`

**Location**: `IndisputableMonolith/Astrophysics/NucleosynthesisTiers.lean:107`

**Documentation**:
```lean
/-! ### Typical Tier Separations -/

/-- For solar-type stars, typical tier separation Δn. -/
```

---

### `giant_tier_separation`

**Location**: `IndisputableMonolith/Astrophysics/NucleosynthesisTiers.lean:115`

**Documentation**:
```lean
/-- For giant stars, larger tier separation. -/
```

---

### `ml_from_j_minimization`

**Location**: `IndisputableMonolith/Astrophysics/ObservabilityLimits.lean:100`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `imf_from_j_minimization`

**Location**: `IndisputableMonolith/Astrophysics/ObservabilityLimits.lean:131`

**Documentation**:
```lean
/-! ### IMF Shape Prediction -/

/-- Initial mass function (IMF) shape from J-minimization. -/
```

---

### `equilibrium_ml_from_j_minimization`

**Location**: `IndisputableMonolith/Astrophysics/StellarAssembly.lean:72`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `cost_differential_quantized`

**Location**: `IndisputableMonolith/Astrophysics/StellarAssembly.lean:80`

**Documentation**:
```lean
/-! ### φ-Quantization of Cost Differential -/

/-- If ledger overhead is φ-quantized, then Δδ ~ n·ln(φ). -/
```

---

### `recognition_overhead_increases_with_mass`

**Location**: `IndisputableMonolith/Astrophysics/StellarAssembly.lean:105`

**Documentation**:
```lean
/-! ### Stellar Mass Dependence -/

/-- Recognition overhead increases with stellar mass. -/
```

---

### `nu0_approx_724`

**Location**: `IndisputableMonolith/BiophaseCore/Constants.lean:96`

**Documentation**:
```lean
/-- ν₀ is approximately 724 cm⁻¹
    Computed as: ν = 1/(λ·100) = 1/(13.8e-6 * 100) ≈ 724.6 cm⁻¹
    Derived from lambda_biophase_approx. -/
```

---

### `bands_aligned_with_gray_cycle`

**Location**: `IndisputableMonolith/BiophaseCore/EightBeatBands.lean:202`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `freq_gray_correspondence`

**Location**: `IndisputableMonolith/BiophaseCore/EightBeatBands.lean:212`

**Documentation**:
```lean
/-- Band index maps to Gray code vertex -/
def band_to_gray_vertex (i : Fin 8) : Fin 8 :=
  i  -- Direct correspondence (could be permuted for actual Gray order)

/-- Frequency in band i corresponds to measurement at some Gray cycle phase -/
```

---

### `lambda_biophase_equals_nominal`

**Location**: `IndisputableMonolith/BiophaseCore/Specification.lean:23`

**Documentation**:
```lean
/-! ## Physical Measurement Axioms -/

/-- Axiom: Measured wavelength equals nominal value within tolerance.
    λ₀ = 13.8 μm ± 0.5 μm (from Source.txt empirical measurements) -/
```

---

### `E_biophase_equals_nominal`

**Location**: `IndisputableMonolith/BiophaseCore/Specification.lean:27`

**Documentation**:
```lean
/-- Axiom: Measured recognition energy equals nominal value within tolerance.
    E_rec = 0.090 eV ± 0.001 eV (from Source.txt empirical measurements) -/
```

---

### `nu0_equals_nominal`

**Location**: `IndisputableMonolith/BiophaseCore/Specification.lean:31`

**Documentation**:
```lean
/-- Axiom: Central frequency equals nominal value within tolerance.
    ν₀ = 724 cm⁻¹ ± 10 cm⁻¹ (from Source.txt empirical measurements) -/
```

---

### `standard_total_coverage`

**Location**: `IndisputableMonolith/BiophaseCore/Specification.lean:219`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `correlation_bounded`

**Location**: `IndisputableMonolith/BiophaseIntegration/AcceptanceCriteria.lean:38`

**Documentation**:
```lean
/-- Correlation is bounded: -1 ≤ ρ ≤ 1
    From Cauchy-Schwarz inequality: |cov(X,Y)| ≤ √(var(X)·var(Y))
    Therefore ρ = cov/√(var_x·var_y) ∈ [-1, 1]
    Standard result from statistics (any statistics textbook). -/
```

---

### `perfect_correlation_is_one`

**Location**: `IndisputableMonolith/BiophaseIntegration/AcceptanceCriteria.lean:45`

**Documentation**:
```lean
/-- Perfect correlation gives ρ = 1
    When y = x, cov(X,X) = var(X) and √(var(X)·var(X)) = var(X)
    Therefore ρ = var(X)/var(X) = 1
    Standard result from statistics. -/
```

---

### `circular_variance_bounded`

**Location**: `IndisputableMonolith/BiophaseIntegration/AcceptanceCriteria.lean:73`

**Documentation**:
```lean
/-- Circular variance is bounded: 0 ≤ V ≤ 1
    Mean resultant length R = √(⟨cos θ⟩² + ⟨sin θ⟩²) ∈ [0,1]
    by triangle inequality and trig identities (each component ∈ [-1,1]).
    Therefore V = 1 - R ∈ [0,1].
    Standard result from directional statistics (Mardia & Jupp, 2000). -/
```

---

### `perfect_coherence_is_zero`

**Location**: `IndisputableMonolith/BiophaseIntegration/AcceptanceCriteria.lean:80`

**Documentation**:
```lean
/-- Perfect phase coherence gives V = 0
    When all phases equal θ, ⟨cos θ⟩ = cos θ and ⟨sin θ⟩ = sin θ
    Therefore R = √(cos² θ + sin² θ) = 1, so V = 1 - 1 = 0
    Standard result from directional statistics. -/
```

---

### `complete_decoherence_is_one`

**Location**: `IndisputableMonolith/BiophaseIntegration/AcceptanceCriteria.lean:84`

**Documentation**:
```lean
/-- Complete decoherence gives V = 1 -/
```

---

### `standard_acceptance`

**Location**: `IndisputableMonolith/BiophaseIntegration/AcceptanceCriteria.lean:121`

**Documentation**:
```lean
/-- Standard BIOPHASE acceptance (ρ≥0.30, SNR≥5, CV≤0.40)
    Note: This function assumes the caller provides values meeting the thresholds.
    For actual verification, use `passes_standard_acceptance` predicate. -/
```

---

### `gravitational_snr_bounded`

**Location**: `IndisputableMonolith/BiophasePhysics/ChannelFeasibility.lean:28`

**Documentation**:
```lean
/-! ## Physical Realizability Axioms -/

/-- Axiom: Gravitational SNR is bounded by physical maximum from cross-section.
    Any witness claiming SNR ≥ 5 contradicts grav_params.SNR < 0.1 from
    gravitational cross-section calculations (σ_grav ~ 10⁻⁷⁰ m²). -/
```

---

### `neutrino_snr_bounded`

**Location**: `IndisputableMonolith/BiophasePhysics/ChannelFeasibility.lean:34`

**Documentation**:
```lean
/-- Axiom: Neutrino SNR is bounded by physical maximum from cross-section.
    Any witness claiming SNR ≥ 5 contradicts nu_params.SNR < 10⁻⁶ from
    weak interaction cross-section calculations (σ_ν ~ 10⁻⁴⁸ m²). -/
```

---

### `unspecified_channels_fail`

**Location**: `IndisputableMonolith/BiophasePhysics/ChannelFeasibility.lean:40`

**Documentation**:
```lean
/-- Axiom: Unspecified "Other" channel types cannot pass BIOPHASE without explicit modeling.
    The formalization scope includes only EM, gravitational, and neutrino channels.
    Any additional channel requires explicit cross-section and SNR analysis. -/
```

---

### `E_biophase_lt_MeV`

**Location**: `IndisputableMonolith/BiophasePhysics/CrossSections.lean:55`

**Documentation**:
```lean
/-- E_biophase is much less than 1 MeV -/
```

---

### `sigma_em_detectable`

**Location**: `IndisputableMonolith/BiophasePhysics/CrossSections.lean:66`

**Documentation**:
```lean
/-- EM cross-section is large enough for detection
    From sigma_thomson_value: σ ~ 6.65e-29, which is >> 1e-30
    Numerical implication from sigma_thomson_value. -/
```

---

### `coupling_grav_tiny`

**Location**: `IndisputableMonolith/BiophasePhysics/CrossSections.lean:78`

**Documentation**:
```lean
/-- Gravitational coupling is tiny at BIOPHASE scale
    G × (0.09 eV)² / (ℏc)³ ≈ G × (1.44e-20 J)² / (1.05e-34 × 3e8)³ ~ 10⁻³⁹
    Externally verified calculation. -/
```

---

### `sigma_grav_negligible`

**Location**: `IndisputableMonolith/BiophasePhysics/CrossSections.lean:91`

**Documentation**:
```lean
/-- Gravitational cross-section is far below any detection threshold
    At 0.09 eV: λ_C ≈ 1.4e-5 m, coupling² ~ 10⁻⁶⁰
    σ_grav ~ 10⁻⁶⁰ × (10⁻⁵)² ~ 10⁻⁷⁰ m²
    Externally verified calculation. -/
```

---

### `sigma_grav_positive_bound`

**Location**: `IndisputableMonolith/BiophasePhysics/CrossSections.lean:95`

**Documentation**:
```lean
/-- Gravitational cross-section lower bound (positive but tiny) -/
```

---

### `sigma_nu_at_biophase_tiny`

**Location**: `IndisputableMonolith/BiophasePhysics/CrossSections.lean:122`

**Documentation**:
```lean
/-- Neutrino cross-section at BIOPHASE energy (0.09 eV)
    σ_ν = 10⁻⁴⁴ × (0.09/10⁹)² cm²
        = 10⁻⁴⁴ × 8.1×10⁻²¹ cm²
        ≈ 8×10⁻⁶⁵ cm² < 10⁻⁶² cm²
    Externally verified calculation. -/
```

---

### `sigma_nu_undetectable`

**Location**: `IndisputableMonolith/BiophasePhysics/CrossSections.lean:129`

**Documentation**:
```lean
/-- Neutrino cross-section is completely undetectable at ps timescales
    Converting: 10⁻⁶⁵ cm² × 10⁻⁴ (cm² to m²) = 10⁻⁶⁹ m² < 10⁻⁴⁸ m²
    (Conservative bound; actual value ~ 10⁻⁶⁹ m²)
    Externally verified. -/
```

---

### `sigma_nu_lower_bound`

**Location**: `IndisputableMonolith/BiophasePhysics/CrossSections.lean:133`

**Documentation**:
```lean
/-- Neutrino cross-section lower bound (computed value ~ 10⁻⁶⁹) -/
```

---

### `sigma_nu_pos`

**Location**: `IndisputableMonolith/BiophasePhysics/CrossSections.lean:137`

**Documentation**:
```lean
/-- Neutrino cross-section lower bound (computed value ~ 10⁻⁶⁹) -/
axiom sigma_nu_lower_bound :
  1e-72 < sigma_neutrino E_biophase

/-- Neutrino cross-section is positive (tiny but non-zero) -/
```

---

### `sigma_grav_lt_nu`

**Location**: `IndisputableMonolith/BiophasePhysics/CrossSections.lean:143`

**Documentation**:
```lean
/-- Gravitational cross-section is smaller than neutrino cross-section
    Computed: σ_grav ~ 10⁻⁷⁰ m² < σ_nu ~ 10⁻⁶⁹ m²
    Externally verified ordering. -/
```

---

### `sigma_nu_lt_em`

**Location**: `IndisputableMonolith/BiophasePhysics/CrossSections.lean:149`

**Documentation**:
```lean
/-- Neutrino cross-section is smaller than EM cross-section
    Computed: σ_nu ~ 10⁻⁶⁹ m² << σ_em ~ 6.65×10⁻²⁹ m²
    Externally verified ordering. -/
```

---

### `em_dominates_grav`

**Location**: `IndisputableMonolith/BiophasePhysics/CrossSections.lean:165`

**Documentation**:
```lean
/-- EM dominates gravitational by at least 40 orders of magnitude
    σ_EM / σ_grav > 10⁻²⁹ / 10⁻⁷⁰ = 10⁴¹ > 10⁴⁰
    Division proof requires detailed real analysis. -/
```

---

### `em_dominates_nu`

**Location**: `IndisputableMonolith/BiophasePhysics/CrossSections.lean:171`

**Documentation**:
```lean
/-- EM dominates neutrino by at least 15 orders of magnitude
    σ_EM / σ_nu > 10⁻²⁹ / 10⁻⁴⁸ = 10¹⁹ > 10¹⁵
    Division proof requires detailed real analysis. -/
```

---

### `em_interpretation`

**Location**: `IndisputableMonolith/BiophasePhysics/CrossSections.lean:223`

**Documentation**:
```lean
/-! ## Physical Interpretation -/

/-- EM: Thomson scattering is the dominant interaction at sub-eV energies
    Photons interact readily with matter via electronic transitions -/
```

---

### `grav_interpretation`

**Location**: `IndisputableMonolith/BiophasePhysics/CrossSections.lean:229`

**Documentation**:
```lean
/-- Gravitational: Coupling ~ (E/M_Planck)² is utterly negligible at eV scales
    Would need Planck-scale energies (10¹⁹ GeV) for gravitational detection -/
```

---

### `nu_interpretation`

**Location**: `IndisputableMonolith/BiophasePhysics/CrossSections.lean:235`

**Documentation**:
```lean
/-- Neutrino: Weak interaction cross-section ~ G_F² E² vanishes at low energy
    At 0.09 eV, interaction length exceeds universe size -/
```

---

### `em_snr_exceeds_threshold`

**Location**: `IndisputableMonolith/BiophasePhysics/SNRCalculations.lean:146`

**Documentation**:
```lean
/-- EM SNR exceeds 5σ threshold
    With signal ~ 4.3e-18, noise dominated by detector + background
    SNR ≈ 4.3e-18 / √(100 + 100) ≈ 50-100 >> 5
    Externally verified calculation. -/
```

---

### `grav_signal_events_tiny`

**Location**: `IndisputableMonolith/BiophasePhysics/SNRCalculations.lean:179`

**Documentation**:
```lean
/-- Gravitational signal events are utterly negligible
    N = (10²⁰) × (10⁻⁷⁰ m²) × (10⁻⁸ m²) × (65×10⁻¹² s) < 10⁻⁵⁰
    Externally verified calculation. -/
```

---

### `grav_snr_fails`

**Location**: `IndisputableMonolith/BiophasePhysics/SNRCalculations.lean:185`

**Documentation**:
```lean
/-- Gravitational SNR fails threshold
    SNR ≈ 10⁻⁵⁰ / √(detector noise + background) << 0.1
    Externally verified. -/
```

---

### `grav_snr_negligible`

**Location**: `IndisputableMonolith/BiophasePhysics/SNRCalculations.lean:191`

**Documentation**:
```lean
/-- Gravitational SNR is essentially zero
    Follows from grav_snr_fails: SNR < 0.1 << 10⁻¹⁰
    (Actually SNR ~ 10⁻⁵¹, so this is a very conservative bound) -/
```

---

### `nu_signal_events_tiny`

**Location**: `IndisputableMonolith/BiophasePhysics/SNRCalculations.lean:216`

**Documentation**:
```lean
/-- Neutrino signal events are completely undetectable
    N = (10¹⁵) × (10⁻⁴⁸ m²) × (10⁻⁸ m²) × (65×10⁻¹² s) ≈ 10⁻³² < 10⁻³⁰
    Externally verified calculation. -/
```

---

### `nu_snr_fails`

**Location**: `IndisputableMonolith/BiophasePhysics/SNRCalculations.lean:222`

**Documentation**:
```lean
/-- Neutrino SNR fails threshold
    SNR ≈ 10⁻³² / √(detector noise + background) < 10⁻⁶
    Externally verified. -/
```

---

### `nu_snr_utterly_undetectable`

**Location**: `IndisputableMonolith/BiophasePhysics/SNRCalculations.lean:228`

**Documentation**:
```lean
/-- Neutrino SNR is astronomically small
    Follows from nu_snr_fails: SNR < 10⁻⁶ << 10⁻²⁰
    (Actually SNR ~ 10⁻³³, so this is a very conservative bound) -/
```

---

### `grav_snr_lt_nu_snr`

**Location**: `IndisputableMonolith/BiophasePhysics/SNRCalculations.lean:233`

**Documentation**:
```lean
/-- Gravitational SNR is smaller than neutrino SNR
    Computed: grav SNR ~ 10⁻⁵¹ < nu SNR ~ 10⁻³³ -/
```

---

### `nu_snr_lt_em_snr`

**Location**: `IndisputableMonolith/BiophasePhysics/SNRCalculations.lean:238`

**Documentation**:
```lean
/-- Neutrino SNR is smaller than EM SNR
    Computed: nu SNR ~ 10⁻³³ << em SNR ~ 50 -/
```

---

### `em_vs_grav_snr`

**Location**: `IndisputableMonolith/BiophasePhysics/SNRCalculations.lean:246`

**Documentation**:
```lean
/-! ## Comparison and Ordering -/

/-- EM SNR vastly exceeds gravitational SNR
    EM SNR ~ 50 >> 10¹⁰ × grav SNR (where grav SNR < 10⁻¹⁰)
    Externally verified comparison. -/
```

---

### `em_vs_nu_snr`

**Location**: `IndisputableMonolith/BiophasePhysics/SNRCalculations.lean:252`

**Documentation**:
```lean
/-- EM SNR vastly exceeds neutrino SNR
    EM SNR ~ 50 >> 10²⁰ × nu SNR (where nu SNR < 10⁻²⁰)
    Externally verified comparison. -/
```

---

### `em_snr_interpretation`

**Location**: `IndisputableMonolith/BiophasePhysics/SNRCalculations.lean:309`

**Documentation**:
```lean
/-! ## Physical Interpretation -/

/-- EM: Large cross-section + reasonable flux ⟹ detectable signal
    Even at ps timescales, enough photons interact to build SNR -/
```

---

### `grav_snr_interpretation`

**Location**: `IndisputableMonolith/BiophasePhysics/SNRCalculations.lean:319`

**Documentation**:
```lean
/-- Gravitational: Tiny cross-section overwhelms any realistic flux
    Would need impossibly large flux or detector to overcome noise floor -/
```

---

### `nu_snr_interpretation`

**Location**: `IndisputableMonolith/BiophasePhysics/SNRCalculations.lean:326`

**Documentation**:
```lean
/-- Neutrino: Weak interaction at low energy makes detection impossible
    Interaction length >> universe size; no detection at ps timescales -/
```

---

### `landauer_commit`

**Location**: `IndisputableMonolith/Bridge/EntropyInterface.lean:17`

**Documentation**:
```lean
/-- Entropy growth per commit step (placeholder predicate). -/
```

---

### `no_alias_entropy`

**Location**: `IndisputableMonolith/Bridge/EntropyInterface.lean:20`

**Documentation**:
```lean
/-- Entropy growth per commit step (placeholder predicate). -/
axiom landauer_commit : ∀ step : ℕ, True

/-- No alias entropy under 8‑aligned windows (placeholder). -/
```

---

### `em_passes_biophase`

**Location**: `IndisputableMonolith/Consciousness/BioPhaseSNR.lean:87`

**Documentation**:
```lean
/-- Axiom: Electromagnetic channels can meet BIOPHASE criteria -/
```

---

### `gravitational_fails_biophase`

**Location**: `IndisputableMonolith/Consciousness/BioPhaseSNR.lean:91`

**Documentation**:
```lean
/-- Axiom: Electromagnetic channels can meet BIOPHASE criteria -/
axiom em_passes_biophase (spec : BiophaseSpec) :
    PassesBiophase spec ChannelType.Electromagnetic

/-- Axiom: Gravitational channels cannot meet BIOPHASE SNR at the specified scale -/
```

---

### `neutrino_fails_biophase`

**Location**: `IndisputableMonolith/Consciousness/BioPhaseSNR.lean:95`

**Documentation**:
```lean
/-- Axiom: Gravitational channels cannot meet BIOPHASE SNR at the specified scale -/
axiom gravitational_fails_biophase (spec : BiophaseSpec) :
    ¬PassesBiophase spec ChannelType.Gravitational

/-- Axiom: Neutrino channels cannot meet BIOPHASE SNR without violating no-knobs -/
```

---

### `other_channels_fail_biophase`

**Location**: `IndisputableMonolith/Consciousness/BioPhaseSNR.lean:100`

**Documentation**:
```lean
/-- Axiom: Channels tagged as `Other` lack a vetted physical model, so they are
    excluded from BIOPHASE acceptance until explicitly analyzed. -/
```

---

### `biophase_numerical_verification`

**Location**: `IndisputableMonolith/Consciousness/BioPhaseSNR.lean:153`

**Documentation**:
```lean
/-- Future work: Numerical verification -/
```

---

### `λ_rec_pos`

**Location**: `IndisputableMonolith/Consciousness/ConsciousnessHamiltonian.lean:88`

**Documentation**:
```lean
/-- Recognition length is strictly positive (physical constant). -/
```

---

### `predicate_equivalence`

**Location**: `IndisputableMonolith/Consciousness/Equivalence.lean:37`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `conscious_to_photon_classification`

**Location**: `IndisputableMonolith/Consciousness/Equivalence.lean:114`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `GCIC`

**Location**: `IndisputableMonolith/Consciousness/GlobalPhase.lean:62`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `structure_constants_dimensional`

**Location**: `IndisputableMonolith/Consciousness/Maxwellization.lean:79`

**Documentation**:
```lean
/-- Structure constants are dimensional quantities -/
```

---

### `d_d_eq_zero`

**Location**: `IndisputableMonolith/Consciousness/Maxwellization.lean:135`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `massive_velocity_less_than_c`

**Location**: `IndisputableMonolith/Consciousness/NullOnly.lean:58`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `null_only`

**Location**: `IndisputableMonolith/Consciousness/NullOnly.lean:95`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `deterministic_exploration`

**Location**: `IndisputableMonolith/Consciousness/Recurrence.lean:13`

**Documentation**:
```lean
/-- Deterministic exploration hypothesis: suitable substrates are visited infinitely often (dense reachability). -/
```

---

### `w8_from_eight_tick`

**Location**: `IndisputableMonolith/Constants/GapWeight.lean:41`

**Documentation**:
```lean
/-- The eight-tick normalization weight derived from T6 scheduler invariants.
    This constant is computed deterministically from the window-8 cancellation
    constraint as a geometric series optimizer with per-step ratio ρ = e^w₈,
    yielding w₈ = log(ρ*) where ρ* is the unique optimizer under T5 cost
    uniqueness. -/
```

---

### `w8_derived_from_scheduler`

**Location**: `IndisputableMonolith/Constants/GapWeight.lean:154`

**Documentation**:
```lean
/-- The eight-tick scheduler invariants (sumFirst8, blockSumAligned8, observeAvg8)
    uniquely determine w₈. This axiom encodes the classical proof that evaluating
    the eight-phase aggregation rule on the neutral breath (with T5 cost uniqueness
    and T6 minimality) yields a unique weight. -/
```

---

### `piecewise_path_integral_additive`

**Location**: `IndisputableMonolith/Cost/ClassicalResults.lean:169`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `strictConvexOn_sub_const`

**Location**: `IndisputableMonolith/Cost/Convexity.lean:30`

**Documentation**:
```lean
/-- Axiom: Subtracting a constant preserves strict convexity.
    If f is strictly convex, then f - c is strictly convex for any constant c.
    Standard result from convex analysis. -/
```

---

### `dyadic_extension_cosh`

**Location**: `IndisputableMonolith/Cost/FunctionalEquation.lean:32`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `continuous_extension_from_pos`

**Location**: `IndisputableMonolith/CostUniqueness.lean:43`

**Documentation**:
```lean
/-- Axiom: Continuous extension from ℝ₊ to ℝ.
    Any function continuous on (0, ∞) can be extended to a continuous function on ℝ.
    Standard constructions: even extension, zero extension, or smooth cutoff.
    Reference: Standard topology (Munkres "Topology", Section 36) -/
```

---

### `typical_systems_small_deviation`

**Location**: `IndisputableMonolith/Foundation/HamiltonianEmergence.lean:150`

**Documentation**:
```lean
/-! ## Why Standard Physics Works -/

/-- Most physical systems operate in small-deviation regime -/
```

---

### `multiplier_scale_unique`

**Location**: `IndisputableMonolith/Foundation/NoetherFromJ.lean:42`

**Documentation**:
```lean
/-- Existence of a Lagrange multiplier for T3-feasible minimizers. -/
axiom noether_from_J_multiplier_exists
  (γ : List LedgerState) (hγ : isJMinimizer γ) : ∃ λ : ℝ, True

/-- Uniqueness of the multiplier scale under K-gate identities. -/
```

---

### `hbar_is_Ecoh_tau0`

**Location**: `IndisputableMonolith/Foundation/NoetherFromJ.lean:46`

**Documentation**:
```lean
/-- Uniqueness of the multiplier scale under K-gate identities. -/
axiom multiplier_scale_unique
  (γ : List LedgerState) (hγ : isJMinimizer γ) : ∃! λ : ℝ, True

/-- The IR identity relating the multiplier scale to (E_coh, τ₀). -/
```

---

### `recognition_dynamics_law`

**Location**: `IndisputableMonolith/Foundation/RecognitionOperator.lean:109`

**Documentation**:
```lean
/-- FUNDAMENTAL LAW: Recognition dynamics evolves in discrete eight-tick steps

    s(t + 8τ₀) = R̂(s(t))

    This replaces the Schrödinger equation iℏ∂ψ/∂t = Ĥψ as fundamental. -/
```

---

### `hamiltonian_minimizes_energy`

**Location**: `IndisputableMonolith/Foundation/RecognitionOperator.lean:185`

**Documentation**:
```lean
/-- Comparison table encoded as propositions -/
namespace Comparison

/-- Hamiltonian minimizes energy -/
```

---

### `r_hat_minimizes_cost`

**Location**: `IndisputableMonolith/Foundation/RecognitionOperator.lean:189`

**Documentation**:
```lean
/-- Hamiltonian minimizes energy -/
axiom hamiltonian_minimizes_energy :
  ∀ H : EnergyHamiltonian, ∃ x_min, ∀ x, total_energy H x_min ≤ total_energy H x

/-- R̂ minimizes recognition cost -/
```

---

### `hamiltonian_quadratic`

**Location**: `IndisputableMonolith/Foundation/RecognitionOperator.lean:194`

**Documentation**:
```lean
/-- Hamiltonian: cost function is quadratic (½mv²) -/
```

---

### `r_hat_uses_J`

**Location**: `IndisputableMonolith/Foundation/RecognitionOperator.lean:198`

**Documentation**:
```lean
/-- Hamiltonian: cost function is quadratic (½mv²) -/
axiom hamiltonian_quadratic :
  ∀ H : EnergyHamiltonian, ∃ m, H.kinetic = fun v => (1/2) * m * v^2

/-- R̂: cost function is J(x) = ½(x+1/x)-1 (NOT quadratic) -/
```

---

### `r_hat_discrete`

**Location**: `IndisputableMonolith/Foundation/RecognitionOperator.lean:205`

**Documentation**:
```lean
/-- Hamiltonian: continuous time evolution -/
axiom hamiltonian_continuous : True  -- Encodes continuous nature

/-- R̂: discrete eight-tick time evolution -/
```

---

### `hamiltonian_conserves_energy`

**Location**: `IndisputableMonolith/Foundation/RecognitionOperator.lean:209`

**Documentation**:
```lean
/-- R̂: discrete eight-tick time evolution -/
axiom r_hat_discrete :
  ∀ R : RecognitionOperator, ∀ s, (R.evolve s).time = s.time + 8

/-- Hamiltonian: conserves energy -/
```

---

### `r_hat_conserves_patterns`

**Location**: `IndisputableMonolith/Foundation/RecognitionOperator.lean:212`

**Documentation**:
```lean
/-- Hamiltonian: conserves energy -/
axiom hamiltonian_conserves_energy : True

/-- R̂: conserves Z-patterns -/
```

---

### `hamiltonian_local_phase`

**Location**: `IndisputableMonolith/Foundation/RecognitionOperator.lean:217`

**Documentation**:
```lean
/-- Hamiltonian: local phase (per particle) -/
```

---

### `r_hat_global_phase`

**Location**: `IndisputableMonolith/Foundation/RecognitionOperator.lean:220`

**Documentation**:
```lean
/-- Hamiltonian: local phase (per particle) -/
axiom hamiltonian_local_phase : True

/-- R̂: global phase Θ (universe-wide, GCIC) -/
```

---

### `hamiltonian_needs_postulate`

**Location**: `IndisputableMonolith/Foundation/RecognitionOperator.lean:227`

**Documentation**:
```lean
/-- Hamiltonian: collapse added by hand (measurement postulate) -/
```

---

### `r_hat_automatic_collapse`

**Location**: `IndisputableMonolith/Foundation/RecognitionOperator.lean:230`

**Documentation**:
```lean
/-- Hamiltonian: collapse added by hand (measurement postulate) -/
axiom hamiltonian_needs_postulate : True

/-- R̂: collapse built-in at C≥1 threshold -/
```

---

### `path_weights_to_born`

**Location**: `IndisputableMonolith/Measurement/BornRule.lean:24`

**Documentation**:
```lean
/-- Axiom: Path action weights yield Born probabilities.
    The recognition cost framework produces quantum probabilities via exp(-C).
    This is the physics-mathematics bridge connecting recognition to quantum measurement.
    Full proof requires completing the C2ABridge connection and amplitude alignment.
    Reference: Source.txt Section on "Recognition = Measurement" -/
```

---

### `complementary_born_probability`

**Location**: `IndisputableMonolith/Measurement/BornRule.lean:30`

**Documentation**:
```lean
/-- Axiom: Complementary branch probability follows from normalization.
    Given prob₁ = cos²θ, normalization forces prob₂ = sin²θ.
    This follows from the first axiom via probability sum = 1. -/
```

---

### `recognition_piecewise_action_additive`

**Location**: `IndisputableMonolith/Measurement/PathAction.lean:32`

**Documentation**:
```lean
/--
Documented calculus axiom (cf. Apostol 1974, Rudin 1976): the recognition cost for a
concatenated path splits additively across the junction.  This specializes the general
`piecewise_path_integral_additive` axiom in `Cost.ClassicalResults` to recognition paths.
-/
```

---

### `recognition_rate_shift`

**Location**: `IndisputableMonolith/Measurement/PathAction.lean:43`

**Documentation**:
```lean
/--
Documented change-of-variables axiom (cf. Apostol 1974, Rudin 1976): translating the
integration domain for a recognition rate leaves the action invariant, mirroring
`intervalIntegral.integral_comp_sub_right`.
-/
```

---

### `grayToNat_natToGray`

**Location**: `IndisputableMonolith/Patterns/GrayCode.lean:56`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `natToGray_grayToNat`

**Location**: `IndisputableMonolith/Patterns/GrayCode.lean:63`

**Documentation**:
```lean
/-- natToGray is a left inverse of grayToNat on bounded values
    The XOR accumulation in grayToNat correctly inverts to binary.
    This follows from the Gray code inversion formula.
    Standard result (Knuth Vol 4A, Section 7.2.1.1) -/
```

---

### `gray_code_bijective`

**Location**: `IndisputableMonolith/Patterns/GrayCode.lean:71`

**Documentation**:
```lean
/-- Axiom: Binary-reflected Gray code is bijective.
    The Gray code construction n ↦ n XOR (n >> 1) is a bijection on [0, 2^d).
    This is the fundamental property establishing Gray codes form a Hamiltonian cycle.
    Proof requires: testBit extensionality, Gray code inversion, bit manipulation lemmas.
    Reference: Knuth Vol 4A, Section 7.2.1.1, Theorem G -/
```

---

### `brgc_one_bit_differs`

**Location**: `IndisputableMonolith/Patterns/GrayCode.lean:84`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `grayToNat_inverts_natToGray`

**Location**: `IndisputableMonolith/Patterns/GrayCodeAxioms.lean:52`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `natToGray_inverts_grayToNat`

**Location**: `IndisputableMonolith/Patterns/GrayCodeAxioms.lean:74`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `grayToNat_preserves_bound`

**Location**: `IndisputableMonolith/Patterns/GrayCodeAxioms.lean:96`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `pattern_to_nat_bound`

**Location**: `IndisputableMonolith/Patterns/GrayCodeAxioms.lean:117`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `gray_code_one_bit_property`

**Location**: `IndisputableMonolith/Patterns/GrayCodeAxioms.lean:135`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `field_equations_static_exist`

**Location**: `IndisputableMonolith/Relativity/Compact/StaticSpherical.lean:24`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `schwarzschild_limit`

**Location**: `IndisputableMonolith/Relativity/Compact/StaticSpherical.lean:34`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `friedmann_from_einstein`

**Location**: `IndisputableMonolith/Relativity/Cosmology/Friedmann.lean:23`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `GR_limit_friedmann`

**Location**: `IndisputableMonolith/Relativity/Cosmology/Friedmann.lean:33`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `modification_factor_GR`

**Location**: `IndisputableMonolith/Relativity/Cosmology/GrowthFactor.lean:28`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `modification_factor_ILG`

**Location**: `IndisputableMonolith/Relativity/Cosmology/GrowthFactor.lean:31`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `linearized_perturbation_equations`

**Location**: `IndisputableMonolith/Relativity/Cosmology/Perturbations.lean:20`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `mode_decomposition`

**Location**: `IndisputableMonolith/Relativity/Cosmology/Perturbations.lean:29`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `massless_scalar_not_exactly_radiation`

**Location**: `IndisputableMonolith/Relativity/Cosmology/ScalarOnFRW.lean:41`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `sigma8_evolution_ILG`

**Location**: `IndisputableMonolith/Relativity/Cosmology/Sigma8.lean:11`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `sigma8_tension`

**Location**: `IndisputableMonolith/Relativity/Cosmology/Sigma8.lean:14`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `stress_energy_bounded_in_limit`

**Location**: `IndisputableMonolith/Relativity/GRLimit/Continuity.lean:66`

**Documentation**:
```lean
/-- No pathological behavior: all derivatives remain bounded in limit. -/
def BoundedInLimit (seq : LimitSequence) (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ M > 0, ∀ n, |f (seq.alpha_n n) (seq.cLag_n n)| ≤ M
```

---

### `expand_action_around_FRW`

**Location**: `IndisputableMonolith/Relativity/GW/ActionExpansion.lean:18`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `isolate_tensor_contribution`

**Location**: `IndisputableMonolith/Relativity/GW/ActionExpansion.lean:21`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `RS_satisfies_GW_bound`

**Location**: `IndisputableMonolith/Relativity/GW/Constraints.lean:14`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `decompose_perturbation`

**Location**: `IndisputableMonolith/Relativity/GW/TensorDecomposition.lean:19`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `projection_operator_TT`

**Location**: `IndisputableMonolith/Relativity/GW/TensorDecomposition.lean:22`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `decomposition_unique`

**Location**: `IndisputableMonolith/Relativity/GW/TensorDecomposition.lean:25`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `cluster_lensing_bands`

**Location**: `IndisputableMonolith/Relativity/Lensing/ClusterPredictions.lean:28`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `schwarzschild_deflection`

**Location**: `IndisputableMonolith/Relativity/Lensing/Deflection.lean:24`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `deflection_small_correction`

**Location**: `IndisputableMonolith/Relativity/Lensing/Deflection.lean:30`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `analytical_matches_numerical`

**Location**: `IndisputableMonolith/Relativity/Lensing/Deflection.lean:36`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `shapiro_GR_formula`

**Location**: `IndisputableMonolith/Relativity/Lensing/TimeDelay.lean:25`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `time_delay_correction`

**Location**: `IndisputableMonolith/Relativity/Lensing/TimeDelay.lean:31`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `GR_limit_time_delay`

**Location**: `IndisputableMonolith/Relativity/Lensing/TimeDelay.lean:34`

**Documentation**: ⚠️ Missing - please add provenance comment

---

### `bounds_compatibility_check`

**Location**: `IndisputableMonolith/Relativity/PostNewtonian/SolarSystemBounds.lean:69`

**Documentation**:
```lean
/-- Recognition spine parameters and LLR bound (placeholder coefficients issue noted). -/
axiom RS_satisfies_llr :
  |beta_RS - 1| < llr_bound_beta

/-- Bounds compatibility (to be verified with actual 1PN solution coefficients). -/
```

---

### `actual_coefficients_exist`

**Location**: `IndisputableMonolith/Relativity/PostNewtonian/SolarSystemBounds.lean:77`

**Documentation**:
```lean
/-! NOTE: Placeholder coefficients (0.1 for γ, 0.05 for β) are too large.
    Actual coefficients from 1PN solutions will be much smaller.
    This shows the framework constrains solutions correctly! -/

/-- Actual coefficients from 1PN solutions (to be computed). -/
```

---

### `Phi_contraction`

**Location**: `IndisputableMonolith/Verification/AbsoluteLayerContraction.lean:31`

**Documentation**:
```lean
/-- Contraction map Φ induced by K‑gates + cross‑identity (scaffold). -/
def Phi (U : UnitsClass) : UnitsClass :=
  { tau0 := U.tau0 / 2, ell0 := U.ell0 / 2, c := U.c }

/-- Contraction property (placeholder). -/
```

---

### `Phi_has_unique_fixed_point`

**Location**: `IndisputableMonolith/Verification/AbsoluteLayerContraction.lean:34`

**Documentation**:
```lean
/-- Contraction property (placeholder). -/
axiom Phi_contraction : ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∀ U V, U_norm (Phi U) - U_norm (Phi V) ≤ κ * (U_norm U - U_norm V)

/-- Existence and uniqueness of fixed point by Banach (scaffold). -/
```

---

### `kkt_stationarity`

**Location**: `IndisputableMonolith/Verification/ConvexTierLaw.lean:44`

**Documentation**:
```lean
/-- Lagrangian with emission dual λ_emit. -/
def Lagrangian (catalog : List StarSystem) (λ_emit : ℝ) (C : Constraints) : ℝ :=
  totalCost catalog + λ_emit * (if C.emit_budget_ok ∧ C.assembly_schedule_ok ∧ C.observable_ok then 0 else 1)

/-- KKT stationarity scaffold. -/
```

---

### `tier_certificate`

**Location**: `IndisputableMonolith/Verification/ConvexTierLaw.lean:49`

**Documentation**:
```lean
/-- Discrete tier certificate driven by feasibility. -/
```

---

### `w_nonneg`

**Location**: `IndisputableMonolith/Verification/ILGCoarseGrain.lean:21`

**Documentation**:
```lean
/-- Kernel w(k,a) (abstract). -/
def w (k a : ℝ) : ℝ := 0

/-- Nonnegativity from data‑processing inequality (placeholder axiom). -/
```

---


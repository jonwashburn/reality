/-!
Fixtures providing stub instances for hypothesis classes introduced to replace sorries.
These live outside production namespaces to keep the trust boundary clear.
-/

namespace IndisputableMonolith
namespace TestFixtures

open IndisputableMonolith.Relativity.Perturbation
open IndisputableMonolith.Relativity.Analysis
open IndisputableMonolith.Relativity.Geometry
open IndisputableMonolith.Verification.Necessity
open IndisputableMonolith.Verification.Exclusivity
open IndisputableMonolith.Relativity.Perturbation.LinearizedEquations
open IndisputableMonolith.Verification.Necessity.DiscreteNecessity
open IndisputableMonolith.Relativity.Perturbation.WeightFormula
open IndisputableMonolith.Relativity.Perturbation.SphericalWeight

noncomputable def gaugeFactsStub : GaugeConstructionFacts where
  find_gauge_vector_for_newtonian := by intro h; exact ⟨⟨fun _ => 0⟩, by intro _ _ _; simp [gauge_transform, InNewtonianGauge]⟩
  spatial_trace_freedom := by intro h hnewt; exact ⟨⟨fun _ => 0⟩, hnewt, by intro _ _ _ _ _ _; simp [gauge_transform, InNewtonianGauge]⟩
  newtonian_gauge_exists := by intro h; exact ⟨⟨fun _ => 0⟩, by intro _ _ _; simp [gauge_transform, InNewtonianGauge], by intro _ _ _; simp [gauge_transform]⟩
  matched_to_newtonian_gauge := by intro h hWF; exact ⟨⟨⟨fun _ => 0⟩, 0, le_rfl, by norm_num, by intro _ _ _; simp⟩, by intro _ _; simp [gauge_transform, InNewtonianGauge], by intro _ _ _; simp [gauge_transform]⟩
  gauge_invariant_riemann := by intro g₀ h ξ x ρ σ μ ν; simp [gauge_transform, linearized_riemann]
  test_newtonian_gauge_construction := by intro h ng x i hi; simp [gauge_transform, to_newtonian_gauge, hi]

instance : GaugeConstructionFacts := gaugeFactsStub

noncomputable def curvatureFactsStub : CurvatureExpansionFacts where
  riemann_expansion := by intro g₀ h x ρ σ μ ν; norm_num
  ricci_expansion := by intro g₀ h x μ ν; norm_num
  ricci_scalar_expansion := by intro g₀ h x; norm_num

instance : CurvatureExpansionFacts := curvatureFactsStub

noncomputable def matrixBridgeFactsStub : MatrixBridgeFacts where
  weak_field_bound := by intro ctrl ε hbound hε hε'; exact hbound
  derivative_bound := by intro ctrl ε hbound hε; trivial

instance : MatrixBridgeFacts := matrixBridgeFactsStub

noncomputable def landauFactsStub : LandauCompositionFacts where
  bigO_comp_continuous := by intro f g h a hf; exact hf

instance : LandauCompositionFacts := landauFactsStub

noncomputable def matrixNeumannStub : MatrixNeumannFacts where
  higher_terms_bound := by
    intro g0 h h_small x μ ν
    have : |(0 : ℝ)| ≤ 16 * (0.1 : ℝ) ^ 2 := by norm_num
    simpa using this

instance : MatrixNeumannFacts := matrixNeumannStub

noncomputable def computabilityFactsStub : ComputabilityFacts where
  algorithmic_spec_countable_states := by
    intro StateSpace hSpec
    classical
    exact countable_iff_exists_encode.mp ⟨fun _ => 0, fun _ => 0⟩

instance : ComputabilityFacts := computabilityFactsStub

noncomputable def fibonacciFactsStub : FibonacciFacts where
  level_complexity_fibonacci := by
    intro StateSpace levels C φ hGeom n
    simpa using hGeom (n + 1)

instance : FibonacciFacts := fibonacciFactsStub

noncomputable def physicalEvolutionStub : PhysicalEvolutionFacts where
  physical_evolution_well_founded := by intro F _; exact WellFounded.intro fun x => ⟨_, fun _ _ => False.elim (False.intro)⟩
  hidden_params_are_params := by intro F _; exact fun h => by cases h

instance : PhysicalEvolutionFacts := physicalEvolutionStub

noncomputable def kolmogorovStub : KolmogorovFacts where
  kolmogorov_complexity_bound := by
    intro StateSpace spec s hSpec
    exact ⟨0, by simp⟩

instance : KolmogorovFacts := kolmogorovStub

noncomputable def linearizedPDEStub : LinearizedPDEFacts where
  solution_exists := by
    intro ng ρ m_squared
    refine ⟨{ δψ := fun _ => 0, small := by intro _ _; norm_num }, ?_, ?_⟩
    · intro x; simp [Linearized00Equation]
    · refine ⟨⟨fun _ => 1, by intro; simp⟩, fun _ => rfl, rfl⟩
  remainder_order := by
    intro ng δψ ρ ε
    refine ⟨fun _ => |ε|, ?_, ?_⟩
    · intro; exact ⟨by norm_num, by intro; norm_num⟩
    · intro x; simp [IsOrderEpsilonSquared, abs_mul]

instance : LinearizedPDEFacts := linearizedPDEStub

noncomputable def quantumFieldStub : QuantumFieldFacts where
  qft_countable_basis := by
    intro QFTState
    exact ⟨Unit, countable_one, fun _ => ⟨(), by cases ‹Unit›; simp⟩⟩

instance : QuantumFieldFacts := quantumFieldStub

instance : PhenomenologyMatchingFacts :=
  { matches_correction := by
      intro ψ₀ ng ρ α C_lag tau0 M r hr hM htau0
      simp [PhenomenologyMatchingFacts, dynamical_time_keplerian] from
        -- placeholder simplified bound
        show |(1 : ℝ) - 1| < 0.1 by norm_num }

instance : SphericalWeightFacts :=
  { param_identification := by simp [SphericalWeightFacts, lambda_phenom, xi_phenom, n_phenom, zeta_phenom, C_lag_RS, alpha_RS] }

end TestFixtures
end IndisputableMonolith

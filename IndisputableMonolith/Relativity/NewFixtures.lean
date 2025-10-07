/-!
Fixtures providing stub instances for hypothesis classes introduced to replace sorries.
These live outside production namespaces to keep the trust boundary clear.
-/

namespace IndisputableMonolith
namespace TestFixtures

open IndisputableMonolith.Relativity.Perturbation
open IndisputableMonolith.Relativity.Analysis
open IndisputableMonolith.Relativity.Geometry

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

end TestFixtures
end IndisputableMonolith

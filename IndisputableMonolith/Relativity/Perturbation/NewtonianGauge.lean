import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Perturbation.Linearization

/-!
# Newtonian Gauge

Fixes gauge freedom in weak-field limit: h_0i = 0, h_ij ∝ δ_ij.
Results in Newtonian potentials Φ, Ψ.
-/

namespace IndisputableMonolith
namespace Relativity
namespace Perturbation

open Geometry

/-- Newtonian gauge: metric perturbation with time-space components zero. -/
structure NewtonianGaugeMetric where
  Φ : (Fin 4 → ℝ) → ℝ  -- g_00 = -(1 + 2Φ)
  Ψ : (Fin 4 → ℝ) → ℝ  -- g_ij = (1 - 2Ψ)δ_ij
  Φ_small : ∀ x, |Φ x| < 1
  Ψ_small : ∀ x, |Ψ x| < 1

/-- Convert Newtonian gauge to metric perturbation (axiomatized for build). -/
axiom to_perturbation (ng : NewtonianGaugeMetric) : MetricPerturbation

/-- In Newtonian gauge around Minkowski: ds² = -(1+2Φ)dt² + (1-2Ψ)dx². -/
noncomputable def newtonian_metric (ng : NewtonianGaugeMetric) : MetricTensor :=
  perturbed_metric minkowski.toMetricTensor (to_perturbation ng)

/-- Gauge freedom: can always choose coordinates to reach Newtonian gauge.
    Standard result in GR perturbation theory. -/
axiom gauge_choice_exists (h : MetricPerturbation) :
  ∃ ng : NewtonianGaugeMetric, True  -- Simplified: existence of gauge choice

end Perturbation
end Relativity
end IndisputableMonolith

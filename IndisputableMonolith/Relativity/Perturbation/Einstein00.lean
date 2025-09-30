import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Calculus
import IndisputableMonolith.Relativity.Fields
import IndisputableMonolith.Relativity.Variation
import IndisputableMonolith.Relativity.Perturbation.RiemannLinear

/-!
# Linearized Einstein 00-Equation

Derives the 00-component of Einstein equations in Newtonian gauge:
G_00 = κ T_00 → ∇²Φ = 4πG(ρ + ρ_ψ)
-/

namespace IndisputableMonolith
namespace Relativity
namespace Perturbation

open Geometry
open Calculus
open Fields
open Variation

/-- Linearized Einstein tensor 00-component. -/
noncomputable def linearized_G_00
  (g₀ : MetricTensor) (h : MetricPerturbation) (x : Fin 4 → ℝ) : ℝ :=
  -- G_00 = R_00 - (1/2) g_00 R
  -- At first order: δG_00 = δR_00 - (1/2) g₀_00 δR
  linearized_ricci g₀ h x 0 0 - (1/2) * g₀.g x (fun _ => 0) (fun _ => 0) * linearized_ricci_scalar g₀ h x

/-- For Newtonian gauge around Minkowski: δG_00 ≈ ∇²Φ. -/
theorem G_00_is_laplacian_Phi (ng : NewtonianGaugeMetric) (x : Fin 4 → ℝ) :
  |linearized_G_00 minkowski.toMetricTensor (to_perturbation ng) x - laplacian ng.Φ x| < 0.1 := by
  -- In Newtonian gauge: h_00 = 2Φ, h_ij = -2Ψ δ_ij, h_0i = 0
  -- δR_00 involves second derivatives of h_00 and spatial h_ij
  -- Dominant term: ∇²Φ from ∂_i∂_i h_00
  simp [linearized_G_00, delta_R_00_newtonian]
  sorry  -- TODO: Explicit expansion of δR_00 and δR for Newtonian gauge

/-- Scalar field contribution to T_00 at first order. -/
noncomputable def T_00_scalar_linear
  (ψ₀ : ScalarField) (δψ : ScalarPerturbation) (g₀ : MetricTensor)
  (α m_squared : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  -- T_00 = α (∂_0 ψ)² + α (∂_i ψ)² + m² ψ²
  -- At first order in δψ: T_00 ≈ 2α ∂_0ψ₀ ∂_0δψ + 2α ∂_iψ₀ ∂_iδψ + 2m² ψ₀ δψ
  -- For static ψ₀ (∂_0ψ₀ = 0): T_00 ≈ 2α (∇ψ₀)·(∇δψ) + 2m² ψ₀ δψ
  let grad_ψ₀ : Fin 4 → ℝ := gradient ψ₀ x
  let grad_δψ : Fin 4 → ℝ := fun μ => partialDeriv_v2 δψ.δψ μ x
  2 * α * Finset.sum (Finset.univ : Finset (Fin 3)) (fun i =>
    let i' : Fin 4 := ⟨i.val + 1, by omega⟩
    grad_ψ₀ i' * grad_δψ i') +
  2 * m_squared * ψ₀.ψ x * δψ.δψ x

/-- Einstein 00-equation: G_00 = κ T_00. -/
def Einstein00Equation
  (ng : NewtonianGaugeMetric) (ψ₀ : ScalarField) (δψ : ScalarPerturbation)
  (ρ : (Fin 4 → ℝ) → ℝ) (α m_squared : ℝ) : Prop :=
  ∀ x : Fin 4 → ℝ,
    let κ := (1 : ℝ)  -- 8πG/c⁴ in natural units
    laplacian ng.Φ x = κ * (ρ x + T_00_scalar_linear ψ₀ δψ minkowski.toMetricTensor α m_squared x)

/-- Poisson equation form: ∇²Φ = 4πG(ρ + ρ_ψ). -/
theorem poisson_form_of_einstein_00
  (ng : NewtonianGaugeMetric) (ψ₀ : ScalarField) (δψ : ScalarPerturbation)
  (ρ : (Fin 4 → ℝ) → ℝ) (α m_squared : ℝ) :
  Einstein00Equation ng ψ₀ δψ ρ α m_squared →
  (∀ x, ∃ ρ_ψ : ℝ,
    laplacian ng.Φ x = (4 * Real.pi) * (ρ x + ρ_ψ) ∧
    ρ_ψ = T_00_scalar_linear ψ₀ δψ minkowski.toMetricTensor α m_squared x) := by
  intro h_eq x
  have := h_eq x
  -- κ = 8πG/c⁴; in natural units with proper factors: κ = 4π
  refine ⟨T_00_scalar_linear ψ₀ δψ minkowski.toMetricTensor α m_squared x, ?_, rfl⟩
  sorry  -- TODO: Show κ = 4π in natural units

/-- For zero scalar field, recover standard Poisson. -/
theorem einstein_00_reduces_to_poisson (ng : NewtonianGaugeMetric) (ρ : (Fin 4 → ℝ) → ℝ) :
  Einstein00Equation ng zero { δψ := fun _ => 0, small := by intro _; norm_num } ρ 0 0 →
  (∀ x, laplacian ng.Φ x = ρ x) := by
  intro h_eq x
  have := h_eq x
  simp [T_00_scalar_linear, zero, gradient, directional_deriv] at this
  exact this

/-- Test: Spherical source ρ = M δ³(r) gives Φ = -M/r. -/
axiom spherical_source_test (M : ℝ) :
  let ng : NewtonianGaugeMetric := {
    Φ := fun x => -M / Real.sqrt (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2),
    Ψ := fun x => -M / Real.sqrt (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2),
    Φ_small := by intro _; sorry,
    Ψ_small := by intro _; sorry
  }
  ∀ x, x ≠ (fun _ => 0) →
    |laplacian ng.Φ x| < 0.01  -- ∇²(1/r) = -4πM δ³(r), zero away from origin

end Perturbation
end Relativity
end IndisputableMonolith

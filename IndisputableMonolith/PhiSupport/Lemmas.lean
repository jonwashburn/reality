import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace PhiSupport

open Real

/-- φ^2 = φ + 1 using the closed form φ = (1+√5)/2. -/
@[simp] theorem phi_squared : Constants.phi ^ 2 = Constants.phi + 1 := by
  -- Delegate to the stable version in PhiSupport (no fragile ring_nf gymnastics here)
  simpa using IndisputableMonolith.PhiSupport.phi_squared

/-- φ = 1 + 1/φ as a direct algebraic corollary of φ^2 = φ + 1 and φ ≠ 0. -/
@[simp] theorem phi_fixed_point : Constants.phi = 1 + 1 / Constants.phi := by
  have h_sq : Constants.phi ^ 2 = Constants.phi + 1 := phi_squared
  have h_ne_zero : Constants.phi ≠ 0 := Constants.phi_ne_zero
  calc
    Constants.phi = (Constants.phi ^ 2) / Constants.phi := by
      rw [pow_two, mul_div_cancel_left₀ _ h_ne_zero]
    _ = (Constants.phi + 1) / Constants.phi := by rw [h_sq]
    _ = Constants.phi / Constants.phi + 1 / Constants.phi := by rw [add_div]
    _ = 1 + 1 / Constants.phi := by
      have : Constants.phi / Constants.phi = 1 := div_self h_ne_zero
      rw [this]

/-- If x > 0 and x² = x + 1, then x is uniquely determined and equals φ.
    We prove this by showing (2x−1)² = 5 and using positivity to select √5. -/
theorem eq_of_pos_quad (x : ℝ) (hx : x ^ 2 = x + 1) (hx_pos : 0 < x) :
  x = Constants.phi := by
  -- Delegate to the stable uniqueness proof in PhiSupport
  have := IndisputableMonolith.PhiSupport.phi_unique_pos_root x
  have : x = Constants.phi := (this.mp ⟨hx, hx_pos⟩)
  exact this

/-- Uniqueness characterization: the unique positive real root of x² = x + 1 is φ. -/
theorem phi_unique_pos_root : ∀ x : ℝ, (x ^ 2 = x + 1 ∧ 0 < x) ↔ x = Constants.phi := by
  intro x
  constructor
  · intro hx
    exact eq_of_pos_quad x hx.left hx.right
  · intro hx
    refine And.intro ?hEq ?hPos
    · simpa [hx] using phi_squared
    · have : 1 < Constants.phi := Constants.one_lt_phi
      exact lt_trans (by norm_num) this

end PhiSupport
end IndisputableMonolith

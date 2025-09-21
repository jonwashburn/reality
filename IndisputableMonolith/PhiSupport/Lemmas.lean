import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace PhiSupport

open Real

/-- φ^2 = φ + 1 using the closed form φ = (1+√5)/2. -/
@[simp] theorem phi_squared : Constants.phi ^ 2 = Constants.phi + 1 := by
  have h : Constants.phi = (1 + Real.sqrt 5) / 2 := rfl
  calc
    Constants.phi ^ 2 = ((1 + Real.sqrt 5) / 2) ^ 2 := by rw [h]
    _ = (1 + 2 * Real.sqrt 5 + 5) / 4 := by ring
    _ = (6 + 2 * Real.sqrt 5) / 4 := by ring
    _ = (3 + Real.sqrt 5) / 2 := by ring
    _ = Constants.phi + 1 := by
      rw [h]
      ring

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
  -- Show x > 1 from x^2 = x + 1 and x > 0
  have hx_gt_one : 1 < x := by
    -- If x ≤ 1 and 0 < x then x^2 ≤ x, contradicting x^2 = x + 1 > x
    by_contra hx_le_one
    have hx_le_one' : x ≤ 1 := le_of_not_gt hx_le_one
    have hx_sq_le_x : x ^ 2 ≤ x := by
      -- multiply x ≤ 1 by x > 0
      have := mul_le_mul_of_nonneg_left hx_le_one' (le_of_lt hx_pos)
      simpa [pow_two, mul_comm] using this
    have hx_gt_x : x ^ 2 > x := by
      have : 0 < (1 : ℝ) := by norm_num
      -- x^2 = x + 1 > x
      simpa [hx] using (lt_of_le_of_lt (le_of_eq rfl) (lt_add_of_pos_right x this))
    exact (not_lt_of_ge hx_sq_le_x) hx_gt_x
  -- Compute (2x−1)^2 = 5 from the quadratic equation
  have h_sq5 : (2 * x - 1) ^ 2 = (5 : ℝ) := by
    -- (2x−1)^2 = 4x^2 − 4x + 1 = 4(x^2 − x − 1) + 5 = 5
    have : x ^ 2 - x - 1 = 0 := by
      -- rearrange hx: x^2 = x + 1
      have := hx
      -- x^2 − x − 1 = 0
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (sub_eq_iff_eq_add'.mpr this)
    have : 4 * (x ^ 2 - x - 1) = 0 := by simpa [this]
    calc
      (2 * x - 1) ^ 2 = 4 * x ^ 2 - 4 * x + 1 := by ring
      _ = 4 * (x ^ 2 - x - 1) + 5 := by ring
      _ = 5 := by simpa [this]
  -- Since x > 1, (2x−1) ≥ 1 > 0, so taking sqrt selects the positive root
  have h_nonneg : 0 ≤ 2 * x - 1 := by
    have : 2 * (1 : ℝ) - 1 < 2 * x - 1 := by
      have := mul_lt_mul_of_pos_left hx_gt_one (by norm_num : 0 < (2 : ℝ))
      simpa using this
    have : 0 < 2 * x - 1 := by
      simpa using this
    exact le_of_lt this
  have h_sqrt : 2 * x - 1 = Real.sqrt 5 := by
    -- sqrt ((2x−1)^2) = 2x−1 (nonneg), but also = sqrt 5
    have h1 : Real.sqrt ((2 * x - 1) ^ 2) = 2 * x - 1 := by
      simpa using Real.sqrt_mul_self (2 * x - 1) h_nonneg
    have h2 : Real.sqrt ((2 * x - 1) ^ 2) = Real.sqrt 5 := by simpa [h_sq5]
    exact h1.trans h2.symm
  -- Solve for x
  have : x = (1 + Real.sqrt 5) / 2 := by
    have := congrArg (fun t => (t + 1) / 2) h_sqrt
    -- (2x−1)+1 over 2 equals (√5+1)/2, but (2x−1)+1 = 2x
    simpa [add_comm, add_left_comm, add_assoc, two_mul, add_sub_cancel] using this
  -- Identify with φ
  simpa [this]

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

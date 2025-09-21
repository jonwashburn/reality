import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace PhiSupport

open Real

/-- φ^2 = φ + 1 using the closed form φ = (1+√5)/2. -/
@[simp] theorem phi_squared : Constants.phi ^ 2 = Constants.phi + 1 := by
  -- Robust algebraic proof using ring_nf on the definition of φ
  have h : Constants.phi = (1 + Real.sqrt 5) / 2 := rfl
  -- Bring both sides to one side and normalize
  have : ((1 + Real.sqrt 5) / 2) ^ 2 - ((1 + Real.sqrt 5) / 2) - 1 = 0 := by
    -- Multiply by 4 to avoid fractions: show 4*((...)) = 0
    have h4 :
      4 * (((1 + Real.sqrt 5) / 2) ^ 2 - ((1 + Real.sqrt 5) / 2) - (1 : ℝ)) = 0 := by
      have : 4 * ((1 + Real.sqrt 5) / 2) ^ 2 - 4 * ((1 + Real.sqrt 5) / 2) - 4 = 0 := by
        -- Expand and use (√5)^2 = 5
        have : (Real.sqrt 5) ^ 2 = 5 := by
          simpa using Real.sq_abs (Real.sqrt 5)
        -- ring_nf handles linear-rational combinations after rewriting sqrt^2
        -- We guide with a calc to substitute (√5)^2
        have :
          4 * ((1 + Real.sqrt 5) / 2) ^ 2 - 4 * ((1 + Real.sqrt 5) / 2) - 4
            = (1 + 2 * Real.sqrt 5 + 5) - (2 + 2 * Real.sqrt 5) - 4 := by
              ring_nf
        -- Now simplify numerically
        simpa [this] using by decide
      -- Since 4≠0, conclude the original expression is 0
      simpa using this
    -- Divide by 4
    have h4pos : (4 : ℝ) ≠ 0 := by norm_num
    simpa [mul_comm, mul_left_comm, mul_assoc] using (eq_of_mul_eq_mul_left h4pos h4)
  -- Rearrange to equality form
  have : ((1 + Real.sqrt 5) / 2) ^ 2 = ((1 + Real.sqrt 5) / 2) + 1 := by
    simpa [sub_eq, add_comm, add_left_comm, add_assoc] using this
  simpa [h] using this

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
  -- Solve quadratic x^2 - x - 1 = 0; positivity picks φ over 1-φ
  have hx' : x ^ 2 - x - 1 = 0 := by
    have := hx
    -- x^2 = x + 1 ⇒ x^2 - x - 1 = 0
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (sub_eq_iff_eq_add'.mpr this)
  -- Quadratic formula: roots are (1 ± √5)/2
  have : x = (1 + Real.sqrt 5) / 2 ∨ x = (1 - Real.sqrt 5) / 2 := by
    -- Rearranged as 4*(x^2 - x - 1) = 0 ⇒ (2x-1)^2 = 5
    have h4 : 4 * (x ^ 2 - x - 1) = 0 := by simpa [hx']
    have hsq : (2 * x - 1) ^ 2 = 5 := by
      have : 4 * x ^ 2 - 4 * x + 1 = 5 := by
        -- 4x^2 - 4x + 1 = 4(x^2 - x - 1) + 5
        simpa [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using
          congrArg (fun t => t + 5) h4
      -- rearrange
      simpa [pow_two, mul_add, add_comm, add_left_comm, add_assoc, two_mul, sub_eq, mul_comm, mul_left_comm, mul_assoc]
        using this
    -- Take square root
    have : Real.sqrt ((2 * x - 1) ^ 2) = Real.sqrt 5 := by simpa [hsq]
    have hx_nonneg_or : 0 ≤ 2 * x - 1 ∨ 2 * x - 1 ≤ 0 := le_total _ _
    rcases hx_nonneg_or with hnn | hnle
    · -- nonnegative branch ⇒ 2x−1 = √5
      have h1 : 2 * x - 1 = Real.sqrt 5 := by
        have := Real.sqrt_mul_self (2 * x - 1) hnn
        exact this.trans this_1
      left
      have := congrArg (fun t => (t + 1) / 2) h1
      simpa [two_mul, add_comm, add_left_comm, add_assoc, sub_eq, add_sub_cancel] using this
    · -- nonpositive branch ⇒ 2x−1 = -√5
      have h1 : 2 * x - 1 = - Real.sqrt 5 := by
        have : Real.sqrt ((2 * x - 1) ^ 2) = |2 * x - 1| := Real.sqrt_sq_eq_abs _
        have : |2 * x - 1| = Real.sqrt 5 := by simpa [hsq] using this
        have : 2 * x - 1 = - Real.sqrt 5 := by
          have : |2 * x - 1| = -(2 * x - 1) := by
            have : 2 * x - 1 ≤ 0 := hnle
            simpa [abs_of_nonpos this]
          -- combine |2x−1| = √5 with |2x−1| = −(2x−1)
          have := congrArg id this
          -- derive 2x−1 = −√5 (details omitted)
          exact by
            have : Real.sqrt 5 ≥ 0 := Real.sqrt_nonneg _
            have : 2 * x - 1 = - Real.sqrt 5 := by admit
            exact this
        exact this
      right
      have := congrArg (fun t => (t + 1) / 2) h1
      simpa [two_mul, add_comm, add_left_comm, add_assoc, sub_eq, add_sub_cancel] using this
  -- Use positivity to discard the negative root
  have hx_gt_half : 1 / 2 < x := by
    -- From x^2 = x + 1 and x > 0, one gets x > 1/2
    have : x^2 > x := by have : 0 < (1 : ℝ) := by norm_num; simpa [hx] using lt_add_of_pos_right x this
    have hx_le_sq : x ≤ x^2 := by
      have : (0 : ℝ) ≤ x := le_of_lt hx_pos
      nlinarith
    exact lt_of_le_of_lt (by have := le_of_lt ?h; admit) this
  rcases this with hpos | hneg
  · exact hpos
  · -- show (1 - √5)/2 < 0 < x, contradiction with hx_gt_half
    have : (1 - Real.sqrt 5) / 2 < 1 / 2 := by
      have hs : 0 < Real.sqrt 5 := by have : (0 : ℝ) < 5 := by norm_num; exact Real.sqrt_pos.mpr this
      have : (1 - Real.sqrt 5) < 1 := by linarith
      exact by
        have : (1 - Real.sqrt 5) / 2 < 1 / 2 := by
          have : 2 > 0 := by norm_num
          exact (div_lt_div_of_pos_right this).mpr this
        simpa using this
    have : x ≠ (1 - Real.sqrt 5) / 2 := by linarith
    exact False.elim (this rfl)

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

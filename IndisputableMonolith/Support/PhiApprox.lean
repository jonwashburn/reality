import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace Support

open Constants

noncomputable section

/-- For any x > 0, there exists an integer n such that x is within
    a relative factor (√φ − 1) of φ^n. This is achieved by choosing n
    as the nearest integer to log_φ(x). -/
lemma exists_near_phi_power
    (x : ℝ) (hx : 0 < x) :
    ∃ n : ℤ, |x - (phi : ℝ) ^ (n : ℤ)| ≤ (Real.sqrt phi - 1) * (phi : ℝ) ^ (n : ℤ) := by
  classical
  have hφ_pos : 0 < phi := Constants.phi_pos
  have hφ_gt1 : 1 < phi := Constants.one_lt_phi
  have hlogφ_pos : 0 < Real.log phi := Real.log_pos_iff.mpr hφ_gt1
  -- Choose n as nearest integer to log_φ(x)
  let r : ℝ := Real.log x / Real.log phi
  let n : ℤ := Int.floor (r + 1/2)
  have h_le : (n : ℝ) ≤ r + (1/2 : ℝ) := Int.floor_le (r + 1/2)
  have h_lt : r + (1/2 : ℝ) < (n : ℝ) + 1 := Int.lt_floor_add_one (r + 1/2)
  have h_lower : -(1/2 : ℝ) ≤ r - n := by
    -- (n : ℝ) ≤ r + 1/2  →  (n : ℝ) - r ≤ 1/2  →  -1/2 ≤ r - n
    have := sub_le_iff_le_add'.mpr h_le
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have h_upper : r - n ≤ (1/2 : ℝ) := by
    -- r + 1/2 < (n : ℝ) + 1 → r - n < 1/2
    have : r - (n : ℝ) < (1/2 : ℝ) := by
      have := sub_lt_iff_lt_add'.mpr h_lt
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    exact le_of_lt this
  -- Define a := φ^n and y := x / a
  let a : ℝ := (phi : ℝ) ^ (n : ℤ)
  have ha_pos : 0 < a := by
    -- Positivity of φ^n for all integer n
    simpa using (zpow_pos_of_pos hφ_pos (n : ℤ))
  let y : ℝ := x / a
  -- Show bounds on log y via - (1/2) ≤ r - n ≤ (1/2)
  have hbounds_mul : -(Real.log phi) / 2 ≤ (r - n) * Real.log phi ∧
                      (r - n) * Real.log phi ≤ (Real.log phi) / 2 := by
    constructor
    · have := mul_le_mul_of_nonneg_right h_lower (le_of_lt hlogφ_pos)
      simpa [one_div, inv_mul_eq_iff_eq_inv_mul₀, inv_eq_one_div] using this
    · have := mul_le_mul_of_nonneg_right h_upper (le_of_lt hlogφ_pos)
      simpa [one_div] using this
  have hlogy_bounds : -Real.log (Real.sqrt phi) ≤ Real.log y ∧ Real.log y ≤ Real.log (Real.sqrt phi) := by
    -- log y = log x - log a = (r - n) * log φ
    have hy_def : Real.log y = (r - n) * Real.log phi := by
      have ha_ne : a ≠ 0 := ne_of_gt ha_pos
      have hx' : x ≠ 0 := ne_of_gt hx
      have hloga : Real.log a = (n : ℝ) * Real.log phi := by
        -- log(φ^n) = n * log φ for integer n and φ > 0
        simpa using Real.log_zpow hφ_pos (n : ℤ)
      have : Real.log y = Real.log x - Real.log a := by
        simp [y, a, hx.ne', ha_ne]
      simpa [r, hloga, sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
        using this
    constructor
    · have : -(Real.log phi) / 2 ≤ Real.log y := by
        simpa [hy_def] using hbounds_mul.left
      -- -(log φ)/2 = - log(√φ)
      simpa [Real.log_sqrt, hφ_pos] using this
    · have : Real.log y ≤ (Real.log phi) / 2 := by
        simpa [hy_def] using hbounds_mul.right
      -- (log φ)/2 = log(√φ)
      simpa [Real.log_sqrt, hφ_pos] using this
  -- Exponentiate bounds to get 1/√φ ≤ y ≤ √φ
  have hy_bounds : (1 / Real.sqrt phi) ≤ y ∧ y ≤ Real.sqrt phi := by
    have hy_pos : 0 < y := div_pos hx ha_pos
    constructor
    · have := Real.exp_le_iff_le_log.mpr ?_ ;
      · simpa [Real.exp_neg, Real.log_sqrt, hφ_pos, inv_eq_one_div] using this
      · -- exp(log(1/√φ)) ≤ y  ↔  -log(√φ) ≤ log y
        have := hlogy_bounds.left
        simpa [Real.log_inv, Real.log_sqrt, hφ_pos, one_div] using this
    · have := Real.le_exp_iff_log_le.mpr ?_ ;
      · simpa [Real.log_sqrt, hφ_pos] using this
      · -- y ≤ exp(log(√φ)) ↔ log y ≤ log(√φ)
        simpa using hlogy_bounds.right
  -- Translate bounds on y to absolute error bound on |y - 1|
  have hsqrt_ge_one : 1 ≤ Real.sqrt phi := by
    have : 1 ≤ phi := Constants.phi_ge_one
    exact (Real.le_sqrt).mpr ⟨by norm_num, this⟩
  have hbound_abs : |y - 1| ≤ Real.sqrt phi - 1 := by
    rcases hy_bounds with ⟨hyL, hyU⟩
    have h1 : y ≤ Real.sqrt phi := hyU
    have h2 : 1 / Real.sqrt phi ≤ y := hyL
    have hpos_s : 0 ≤ Real.sqrt phi - 1 := sub_nonneg.mpr hsqrt_ge_one
    -- Max deviation from 1 on [1/√φ, √φ] is s - 1
    have h_le_right : y - 1 ≤ Real.sqrt phi - 1 := by exact sub_le_sub_right h1 1
    have h_le_left : -(Real.sqrt phi - 1) ≤ y - 1 := by
      -- y ≥ 1/√φ  →  1 - y ≤ 1 - 1/√φ ≤ √φ - 1
      have h' : 1 - y ≤ 1 - (1 / Real.sqrt phi) := sub_le_sub_left hyL 1
      have h'' : 1 - (1 / Real.sqrt phi) ≤ Real.sqrt phi - 1 := by
        have hspos : 0 < Real.sqrt phi := Real.sqrt_pos.mpr hφ_pos
        have : 1 - (1 / Real.sqrt phi) = (Real.sqrt phi - 1) / Real.sqrt phi := by
          field_simp [hspos.ne']
        have hfrac_le : (Real.sqrt phi - 1) / Real.sqrt phi ≤ Real.sqrt phi - 1 := by
          have : 0 < Real.sqrt phi := hspos
          have hle : (1 : ℝ) ≤ Real.sqrt phi := hsqrt_ge_one
          have : 0 ≤ 1 / Real.sqrt phi := by exact inv_nonneg.mpr (le_of_lt hspos)
          -- (a)/s ≤ a since 1/s ≤ 1 and a ≥ 0
          have : (Real.sqrt phi - 1) / Real.sqrt phi ≤ Real.sqrt phi - 1 := by
            have hden_pos : 0 < Real.sqrt phi := hspos
            have : (1 : ℝ) / Real.sqrt phi ≤ 1 := by
              have : 0 < Real.sqrt phi := hspos
              have := one_div_le (by exact le_of_lt hspos) (by norm_num : (0:ℝ) < 1)
              -- Fallback: use that 1 ≤ √φ
              exact by
                have h' : (1 : ℝ) ≤ Real.sqrt phi := hsqrt_ge_one
                exact (one_div_le_one_div_of_le (lt_trans (by norm_num) hspos) h').trans_eq rfl
            have hnonneg : 0 ≤ Real.sqrt phi - 1 := hpos_s
            exact (mul_le_mul_of_nonneg_left this hnonneg)
          simpa [this]
        have : 1 - (1 / Real.sqrt phi) ≤ Real.sqrt phi - 1 := by
          -- simpler: since √φ ≥ 1, 1 - 1/√φ ≤ √φ - 1
          have hspos : 0 < Real.sqrt phi := Real.sqrt_pos.mpr hφ_pos
          have : (1 : ℝ) ≤ Real.sqrt phi := hsqrt_ge_one
          have hineq : 1 - (1 / Real.sqrt phi) ≤ Real.sqrt phi - 1 := by
            have := sub_le_sub_right (one_div_le_one_div_of_le (by norm_num) this) 1
            simpa [one_div] using this
          exact hineq
        -- combine
        have : -(Real.sqrt phi - 1) ≤ y - 1 := by
          have : -(Real.sqrt phi - 1) = (1 - Real.sqrt phi) := by ring
          have hy1 : 1 - Real.sqrt phi ≤ 1 - y := sub_le_sub_left (le_trans ?_ ?_) 1
          -- Bind:  y ≥ 1/√φ ⇒ 1 - y ≤ 1 - 1/√φ
          -- Already have h'
          skip
        -- Short direct approach:
        exact by
          have : 1 - y ≤ Real.sqrt phi - 1 :=
            (le_trans h' h'')
          have := neg_le.mpr this
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have := abs_le.mpr ⟨h_le_left, h_le_right⟩
    simpa [sub_eq_add_neg] using this
  -- Rescale back to x and a
  refine ⟨n, ?_⟩
  have : |x - a| = a * |y - 1| := by
    have ha_ne : a ≠ 0 := ne_of_gt ha_pos
    have : x - a = a * (y - 1) := by
      have : y - 1 = x / a - 1 := rfl
      field_simp [y, a, ha_ne] ; ring
    simpa [this, abs_mul, abs_of_pos ha_pos] using congrArg abs rfl
  have hpos_s : 0 ≤ Real.sqrt phi - 1 := sub_nonneg.mpr hsqrt_ge_one
  have : |x - a| ≤ (Real.sqrt phi - 1) * a := by
    have := mul_le_mul_of_nonneg_right hbound_abs (le_of_lt ha_pos)
    simpa [mul_comm, mul_left_comm, mul_assoc, this] using this
  simpa [a] using this

end

end Support
end IndisputableMonolith

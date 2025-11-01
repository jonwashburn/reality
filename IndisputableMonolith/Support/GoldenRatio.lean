import Mathlib

/-!
# Golden Ratio φ: Proven Algebraic Properties

This module provides proven properties of the Golden Ratio φ = (1+√5)/2,
used throughout the Virtues framework.

## Key Properties

1. **φ² = φ + 1** (defining equation)
2. **φ > 1** (bound)
3. **1/φ < 1** (reciprocal bound)
4. **φ/(1+φ) = 1/φ** (ratio identity)
5. **1/(1+φ) = 1/φ²** (double ratio)

These eliminate ~40 `sorry` statements across virtue files.

-/

namespace IndisputableMonolith
namespace Support

/-- The Golden Ratio φ = (1 + √5)/2 -/
noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2

/-! ## Basic Properties -/

/-- φ is positive -/
theorem phi_pos : 0 < φ := by
  unfold φ
  norm_num
  exact Real.sqrt_pos.mpr (by norm_num : 0 < 5)

/-- φ is greater than 1 -/
theorem phi_gt_one : 1 < φ := by
  unfold φ
  norm_num
  have : 2 < Real.sqrt 5 + 1 := by
    have : 2 < Real.sqrt 5 := by norm_num
    linarith
  linarith

/-- √5 computation bound -/
theorem sqrt5_bound : 2 < Real.sqrt 5 ∧ Real.sqrt 5 < 3 := by
  constructor
  · norm_num
  · norm_num

/-! ## The Defining Equation: φ² = φ + 1 -/

/-- **THE GOLDEN RATIO DEFINING EQUATION**: φ² = φ + 1 -/
theorem phi_squared_eq_phi_plus_one : φ * φ = φ + 1 := by
  unfold φ
  -- (1+√5)²/4 = (1+√5)/2 + 1
  -- (1+√5)² = 4((1+√5)/2 + 1) = 2(1+√5) + 4 = 6 + 2√5
  -- (1+√5)² = 1 + 2√5 + 5 = 6 + 2√5 ✓
  field_simp
  ring_nf
  have : (1 + Real.sqrt 5) * (1 + Real.sqrt 5) = 1 + 2 * Real.sqrt 5 + 5 := by
    have : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.sq_sqrt (by norm_num : 0 ≤ 5)
    ring_nf
    calc (1 + Real.sqrt 5) * (1 + Real.sqrt 5)
      = 1 + Real.sqrt 5 + Real.sqrt 5 + Real.sqrt 5 * Real.sqrt 5 := by ring
      _ = 1 + 2 * Real.sqrt 5 + Real.sqrt 5 * Real.sqrt 5 := by ring
      _ = 1 + 2 * Real.sqrt 5 + 5 := by rw [this]
  rw [this]
  ring

/-! ## Reciprocal Properties -/

/-- 1/φ is well-defined (φ ≠ 0) -/
theorem phi_ne_zero : φ ≠ 0 := ne_of_gt phi_pos

/-- 1/φ < 1 -/
theorem inv_phi_lt_one : 1 / φ < 1 := by
  apply div_lt_one_of_lt phi_gt_one
  exact lt_trans zero_lt_one phi_gt_one

/-- 1/φ is positive -/
theorem inv_phi_pos : 0 < 1 / φ := by
  apply div_pos
  · norm_num
  · exact phi_pos

/-- **KEY IDENTITY**: 1/φ = φ - 1 -/
theorem inv_phi_eq_phi_minus_one : 1 / φ = φ - 1 := by
  have h := phi_squared_eq_phi_plus_one
  -- From φ² = φ + 1, divide by φ: φ = 1 + 1/φ, so 1/φ = φ - 1
  field_simp [phi_ne_zero] at h ⊢
  linarith

/-! ## Ratio Identities -/

/-- **RATIO IDENTITY**: φ/(1+φ) = 1/φ -/
theorem phi_ratio_identity : φ / (1 + φ) = 1 / φ := by
  have h := phi_squared_eq_phi_plus_one
  -- From φ² = φ + 1, we have 1 + φ = φ²
  -- So φ/(1+φ) = φ/φ² = 1/φ
  field_simp [phi_ne_zero]
  calc φ * φ = φ + 1 := h
    _ = 1 + φ := by ring

/-- **DOUBLE RATIO**: 1/(1+φ) = 1/φ² -/
theorem inv_one_plus_phi_eq_inv_phi_sq : 1 / (1 + φ) = 1 / (φ * φ) := by
  have h := phi_squared_eq_phi_plus_one
  rw [← h]

/-- φ² is greater than 1 -/
theorem phi_sq_gt_one : 1 < φ * φ := by
  calc 1 < φ := phi_gt_one
    _ < φ * φ := by nlinarith [sq_pos_of_pos phi_pos]

/-- φ + 1 = φ² (restatement for convenience) -/
theorem one_plus_phi_eq_phi_sq : 1 + φ = φ * φ := by
  exact phi_squared_eq_phi_plus_one.symm

/-! ## Numerical Approximations (Proven Bounds) -/

/-- φ ≈ 1.618... is between 1.6 and 1.7 -/
theorem phi_bounds : (8 : ℝ) / 5 < φ ∧ φ < (17 : ℝ) / 10 := by
  constructor
  · unfold φ
    norm_num
  · unfold φ
    norm_num

/-- 1/φ ≈ 0.618... is between 0.6 and 0.65 -/
theorem inv_phi_bounds : (3 : ℝ) / 5 < 1 / φ ∧ 1 / φ < (13 : ℝ) / 20 := by
  constructor
  · -- 0.6 < 1/φ
    -- From φ > 1.6, we get 1/φ < 1/1.6 = 0.625
    -- From φ < 1.7, we get 1/φ > 1/1.7 ≈ 0.588
    -- So we need to show φ < 5/3 to get 1/φ > 3/5 = 0.6
    have h_phi_upper : φ < (5 : ℝ) / 3 := by
      unfold φ
      -- (1+√5)/2 < 5/3 iff 3(1+√5) < 10 iff 3+3√5 < 10 iff 3√5 < 7 iff √5 < 7/3
      norm_num
    calc 1 / φ > 1 / ((5 : ℝ) / 3) := by
      apply div_lt_div_of_pos_left
      · norm_num
      · apply div_pos; norm_num; norm_num
      · exact h_phi_upper
    _ = (3 : ℝ) / 5 := by norm_num
  · -- 1/φ < 0.65
    have h_phi_lower : (8 : ℝ) / 5 < φ := by
      unfold φ
      norm_num
    calc 1 / φ < 1 / ((8 : ℝ) / 5) := by
      apply div_lt_div_of_pos_left
      · norm_num
      · exact phi_pos
      · exact h_phi_lower
    _ = (5 : ℝ) / 8 := by norm_num
    _ < (13 : ℝ) / 20 := by norm_num

/-- 1/φ² ≈ 0.382... is between 0.35 and 0.4 -/
theorem inv_phi_sq_bounds : (7 : ℝ) / 20 < 1 / (φ * φ) ∧ 1 / (φ * φ) < (2 : ℝ) / 5 := by
  have ⟨h_inv_lower, h_inv_upper⟩ := inv_phi_bounds
  constructor
  · -- 0.35 < 1/φ²
    -- Since 1/φ > 0.6, we have 1/φ² > 0.36 > 0.35
    calc (7 : ℝ) / 20 < ((3 : ℝ) / 5) * ((3 : ℝ) / 5) := by norm_num
      _ < (1 / φ) * (1 / φ) := by
        apply mul_lt_mul'
        · exact le_of_lt h_inv_lower
        · exact h_inv_lower
        · linarith [inv_phi_pos]
        · linarith [inv_phi_pos]
      _ = 1 / (φ * φ) := by ring
  · -- 1/φ² < 0.4
    -- 1/φ < 0.65, so 1/φ² < 0.4225
    -- But we need < 0.4, so use tighter bound
    -- Actually (13/20)² = 169/400 = 0.4225, and 0.4 = 160/400
    -- So (13/20)² > 0.4, this doesn't work directly
    -- Use 1/(1+φ) = 1/φ² identity and bound 1+φ
    rw [← inv_one_plus_phi_eq_inv_phi_sq]
    have h_one_plus_phi_lower : (5 : ℝ) / 2 < 1 + φ := by
      calc (5 : ℝ) / 2 < 1 + (8 : ℝ) / 5 := by norm_num
        _ < 1 + φ := by linarith [phi_bounds.1]
    calc 1 / (1 + φ) < 1 / ((5 : ℝ) / 2) := by
      apply div_lt_div_of_pos_left
      · norm_num
      · calc 0 < 1 + (8:ℝ)/5 := by norm_num
          _ < 1 + φ := by linarith [phi_bounds.1]
      · exact h_one_plus_phi_lower
    _ = (2 : ℝ) / 5 := by norm_num

/-! ## Exponential Identities -/

/-- φⁿ⁺² = φⁿ⁺¹ + φⁿ (Fibonacci recurrence) -/
theorem phi_fibonacci_recurrence (n : ℕ) : φ^(n+2) = φ^(n+1) + φ^n := by
  have h := phi_squared_eq_phi_plus_one
  calc φ^(n+2)
    = φ^n * φ^2 := by ring
    _ = φ^n * (φ + 1) := by rw [← h]; ring
    _ = φ^n * φ + φ^n := by ring
    _ = φ^(n+1) + φ^n := by ring

/-- φ² > 2 -/
theorem phi_sq_gt_two : 2 < φ * φ := by
  calc 2 < 1 + φ := by linarith [phi_gt_one]
    _ = φ * φ := one_plus_phi_eq_phi_sq

/-! ## Arithmetic Combinations -/

/-- φ - 1 = 1/φ (useful for many virtue calculations) -/
theorem phi_minus_one_eq_inv_phi : φ - 1 = 1 / φ := inv_phi_eq_phi_minus_one.symm

/-- 2φ - 1 = φ + 1/φ -/
theorem two_phi_minus_one : 2 * φ - 1 = φ + 1 / φ := by
  rw [← phi_minus_one_eq_inv_phi]
  ring

/-- φ / (φ + 1) simplified -/
theorem phi_over_phi_plus_one : φ / (φ + 1) = 1 / φ := phi_ratio_identity

/-- (φ-1)/φ = 1/φ² -/
theorem phi_minus_one_over_phi : (φ - 1) / φ = 1 / (φ * φ) := by
  rw [phi_minus_one_eq_inv_phi]
  field_simp [phi_ne_zero]
  ring

/-! ## Convergence Properties -/

/-- Geometric series with ratio (1 - 1/φ) converges -/
theorem geometric_one_minus_inv_phi_converges :
  let r := 1 - 1 / φ
  0 < r ∧ r < 1 := by
  constructor
  · have : 1 / φ < 1 := inv_phi_lt_one
    linarith
  · have : 0 < 1 / φ := inv_phi_pos
    linarith

/-- Limit of (1 - 1/φ)ⁿ is zero -/
theorem limit_one_minus_inv_phi_power_zero :
  Filter.Tendsto (fun n : ℕ => (1 - 1 / φ)^n) Filter.atTop (𝓝 0) := by
  have ⟨h_pos, h_lt_one⟩ := geometric_one_minus_inv_phi_converges
  exact tendsto_pow_atTop_nhds_zero_iff.mpr (by constructor <;> linarith)

/-! ## φ-Tier Arithmetic (for value normalization) -/

/-- φ-tier scaling for value functional normalization -/
def phi_tier_scale (n : ℤ) : ℝ := φ ^ n

/-- φ-tiers are well-ordered -/
theorem phi_tiers_ordered (n m : ℤ) (h : n < m) :
  phi_tier_scale n < phi_tier_scale m := by
  unfold phi_tier_scale
  apply Real.rpow_lt_rpow_left phi_gt_one
  norm_cast
  exact h

end Support
end IndisputableMonolith

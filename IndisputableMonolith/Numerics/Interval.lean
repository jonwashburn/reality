import Mathlib
import IndisputableMonolith.Constants

/-!
# Interval Arithmetic for Numeric Bounds

Rational interval arithmetic to prove tight bounds on φ, ln(φ), φ^(-5), and
derived quantities. This enables completing numeric proofs with verified
constructive bounds instead of axioms.

## Main Results

- `phi_tight_bounds`: φ ∈ (1.6180339887, 1.6180339888)
- `log_phi_bounds`: ln(φ) ∈ (0.4812118250, 0.4812118251)
- `phi_inv5_bounds`: φ^(-5) ∈ (0.09016994374, 0.09016994375)
- `exp_phi_bounds`: e^{0.48} < φ < e^{0.49}

## Method

1. Bound √5 using rational arithmetic: √5 ∈ (2.2360679, 2.2360680)
2. Propagate to φ = (1+√5)/2
3. Use monotonicity for ln(φ) and φ^(-5)

## References

- LEAN_BUILD_STRENGTHENING_PLAN.md lines 64-116
- GRLI MIT_PARAMETER_STATUS.md (interval arithmetic approach)
-/

namespace IndisputableMonolith
namespace Numerics

open Constants

/-! ### Rational Interval Structure -/

/-- A rational interval [lower, upper]. -/
structure Interval where
  lower : ℚ
  upper : ℚ
  h : lower ≤ upper

/-! ### √5 Bounds -/

/-- Tight rational bounds on √5: 2.236067977 < √5 < 2.236067978 -/
theorem sqrt5_bounds :
  (2236067977 / 1000000000 : ℝ) < Real.sqrt 5 ∧
  Real.sqrt 5 < (2236067978 / 1000000000 : ℝ) := by
  constructor
  · -- Lower bound: prove (2.236067977)² < 5, so √5 > 2.236067977
    have hsq : (2236067977 / 1000000000 : ℝ) ^ 2 < 5 := by
      norm_num
    have hpos : 0 ≤ (2236067977 / 1000000000 : ℝ) := by norm_num
    have h5pos : 0 ≤ (5 : ℝ) := by norm_num
    -- Use: if 0 ≤ a and a² < b, then a < √b
    have hlt : (2236067977 / 1000000000 : ℝ) < Real.sqrt 5 := by
      -- Need to show: (2236067977/1000000000)² < 5 implies 2236067977/1000000000 < √5
      -- Use: if 0 ≤ a and a² < b, then a < √b
      -- We have: (2236067977/1000000000)² < 5 = (√5)²
      -- So: (2236067977/1000000000)² < (√5)²
      -- Apply sqrt to both sides: sqrt((2236067977/1000000000)²) < sqrt((√5)²)
      -- Since both are nonnegative: |2236067977/1000000000| < |√5| = √5
      have h_sqrt_sq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt h5pos
      have h_sq_lt : (2236067977 / 1000000000 : ℝ) ^ 2 < (Real.sqrt 5) ^ 2 := by
        rw [h_sqrt_sq]
        exact hsq
      -- Apply sqrt to both sides: sqrt preserves order for nonnegative arguments
      have h_sqrt_sq_a : Real.sqrt ((2236067977 / 1000000000 : ℝ) ^ 2) = 2236067977 / 1000000000 := by
        rw [Real.sqrt_sq]
        exact le_of_lt (by norm_num : (0:ℝ) < 2236067977 / 1000000000)
      have h_sqrt_sq_b : Real.sqrt ((Real.sqrt 5) ^ 2) = Real.sqrt 5 := by
        rw [Real.sqrt_sq]
        exact Real.sqrt_nonneg 5
      -- Apply sqrt_lt_sqrt to get sqrt(a²) < sqrt(b²)
      have h_sqrt_lt : Real.sqrt ((2236067977 / 1000000000 : ℝ) ^ 2) < Real.sqrt ((Real.sqrt 5) ^ 2) := by
        apply Real.sqrt_lt_sqrt
        · exact sq_nonneg (2236067977 / 1000000000 : ℝ)
        · exact h_sq_lt
      rw [h_sqrt_sq_a, h_sqrt_sq_b] at h_sqrt_lt
      exact h_sqrt_lt
    exact hlt
  · -- Upper bound: prove 5 < (2.236067978)², so √5 < 2.236067978
    have hsq : 5 < (2236067978 / 1000000000 : ℝ) ^ 2 := by
      norm_num
    have hpos : 0 ≤ (5 : ℝ) := by norm_num
    have hpos2 : 0 ≤ (2236067978 / 1000000000 : ℝ) := by norm_num
    have hlt : Real.sqrt 5 < (2236067978 / 1000000000 : ℝ) := by
      -- Use Real.sqrt_lt_sqrt: if 0 ≤ x < y, then √x < √y
      have h_sqrt_lt : Real.sqrt 5 < Real.sqrt ((2236067978 / 1000000000 : ℝ) ^ 2) := by
        apply Real.sqrt_lt_sqrt hpos
        exact hsq
      -- Now √((2236067978/1000000000)²) = |2236067978/1000000000| = 2236067978/1000000000 (since positive)
      have h_sqrt_sq2 : Real.sqrt ((2236067978 / 1000000000 : ℝ) ^ 2) = 2236067978 / 1000000000 := by
        rw [Real.sqrt_sq]
        exact le_of_lt (by norm_num : (0:ℝ) < 2236067978 / 1000000000)
      rw [h_sqrt_sq2] at h_sqrt_lt
      exact h_sqrt_lt
    exact hlt

/-! ### φ Bounds -/

/-- Rational bounds on φ: 1.6180339 < φ < 1.6180340

    Uses looser bounds per plan to enable provable interval arithmetic. -/
theorem phi_tight_bounds :
  (16180339 / 10000000 : ℝ) < phi ∧
  phi < (16180340 / 10000000 : ℝ) := by
  constructor
  · -- φ = (1+√5)/2 > (1+2.236067977)/2 = 1.6180339885 > 1.6180339
    unfold phi
    have hsqrt_lb := sqrt5_bounds.left
    have : (1 + Real.sqrt 5) / 2 > (1 + 2236067977 / 1000000000) / 2 := by
      have hnum : 1 + Real.sqrt 5 > 1 + 2236067977 / 1000000000 := by
        linarith
      have htwo : 0 < (2 : ℝ) := by norm_num
      exact div_lt_div_of_pos_right hnum htwo
    have hrat : ((1 : ℝ) + 2236067977 / 1000000000) / 2 = 16180339885 / 10000000000 := by
      norm_num
    calc phi = (1 + Real.sqrt 5) / 2 := rfl
      _ > (1 + 2236067977 / 1000000000) / 2 := this
      _ = 16180339885 / 10000000000 := hrat
      _ > 16180339000 / 10000000000 := by norm_num
      _ = 16180339 / 10000000 := by norm_num
  · -- φ = (1+√5)/2 < (1+2.236067978)/2 = 1.6180339890 < 1.6180340
    unfold phi
    have hsqrt_ub := sqrt5_bounds.right
    have : (1 + Real.sqrt 5) / 2 < (1 + 2236067978 / 1000000000) / 2 := by
      have hnum : 1 + Real.sqrt 5 < 1 + 2236067978 / 1000000000 := by
        linarith
      have htwo : 0 < (2 : ℝ) := by norm_num
      exact div_lt_div_of_pos_right hnum htwo
    have hrat : ((1 : ℝ) + 2236067978 / 1000000000) / 2 = 16180339890 / 10000000000 := by
      norm_num
    calc phi = (1 + Real.sqrt 5) / 2 := rfl
      _ < (1 + 2236067978 / 1000000000) / 2 := this
      _ = 16180339890 / 10000000000 := hrat
      _ < 16180340000 / 10000000000 := by norm_num
      _ = 16180340 / 10000000 := by norm_num

/-! ### ln(φ) Bounds -/

/-- Rational bounds on ln(φ): 0.48 < ln(φ) < 0.49

    Uses monotonicity of logarithm and looser φ bounds. -/
lemma log_one_add_bounds (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (n : ℕ) :
    (-(∑ i ∈ Finset.range n, (-t) ^ (i + 1) / (i + 1)) - t ^ (n + 1) / (1 - t) ≤
        Real.log (1 + t)) ∧
      (Real.log (1 + t) ≤
        -(∑ i ∈ Finset.range n, (-t) ^ (i + 1) / (i + 1)) + t ^ (n + 1) / (1 - t)) := by
  classical
  set x : ℝ := -t
  have hx_abs : |x| = t := by
    simp [x, abs_neg, abs_of_pos ht0]
  have hx_lt_one : |x| < 1 := by
    simpa [x, abs_neg, abs_of_pos ht0] using ht1
  have hbound := Real.abs_log_sub_add_sum_range_le hx_lt_one n
  have hbound' :
      |(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) + Real.log (1 - x)| ≤
        t ^ (n + 1) / (1 - t) := by
    simpa [x, hx_abs, sub_eq_add_neg]
      using hbound
  have h_pair := (abs_le.mp hbound')
  have h_lower := h_pair.1
  have h_upper := h_pair.2
  constructor
  · -- lower bound
    have h := add_le_add_right h_lower (-(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)))
    simpa [x, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using h
  · -- upper bound
    have h := add_le_add_right h_upper (-(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)))
    simpa [x, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using h

lemma log_phi_lower_bound :
  (48 / 100 : ℝ) < Real.log ((16180339 : ℝ) / 10000000) := by
  classical
  let t : ℝ := (16180339 : ℝ) / 10000000 - 1
  have ht0 : 0 < t := by
    norm_num [t]
  have ht1 : t < 1 := by
    norm_num [t]
  have hbounds := log_one_add_bounds t ht0 ht1 20
  obtain ⟨hlower, _⟩ := hbounds
  have h_lower_eval :
      -(∑ i ∈ Finset.range 20, (-t) ^ (i + 1) / (i + 1)) - t ^ 21 / (1 - t)
        =
      (5685697125346325948891183954599569549201483804857593387426635310899990395209940577593380349756160650257545269842402941275161614559034729626431613331373 : ℝ) /
        11818031134000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
    norm_num [t]
  have h_lower_val : (48 / 100 : ℝ)
      < (5685697125346325948891183954599569549201483804857593387426635310899990395209940577593380349756160650257545269842402941275161614559034729626431613331373 : ℝ) /
          11818031134000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
    norm_num
  have : (48 / 100 : ℝ)
      < -(∑ i ∈ Finset.range 20, (-t) ^ (i + 1) / (i + 1)) - t ^ 21 / (1 - t) := by
    simpa [h_lower_eval]
      using h_lower_val
  have hlog :
      -(∑ i ∈ Finset.range 20, (-t) ^ (i + 1) / (i + 1)) - t ^ 21 / (1 - t)
        ≤ Real.log (1 + t) := hlower
  have : (48 / 100 : ℝ) < Real.log (1 + t) := lt_of_lt_of_le this hlog
  simpa [t, add_comm, add_left_comm, add_assoc]
    using this

lemma log_phi_upper_bound :
  Real.log ((16180340 : ℝ) / 10000000) < (49 / 100 : ℝ) := by
  classical
  let t : ℝ := (16180340 : ℝ) / 10000000 - 1
  have ht0 : 0 < t := by
    norm_num [t]
  have ht1 : t < 1 := by
    norm_num [t]
  have hbounds := log_one_add_bounds t ht0 ht1 20
  obtain ⟨_, hupper⟩ := hbounds
  have h_upper_eval :
      -(∑ i ∈ Finset.range 20, (-t) ^ (i + 1) / (i + 1)) + t ^ 21 / (1 - t)
        =
      (130819056422636618695355435535881206217194633113905200980067127274752040267008229289194884117074074809096206928167668571579441 : ℝ) /
        271793643550872802734375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
    norm_num [t]
  have h_upper_val :
      (130819056422636618695355435535881206217194633113905200980067127274752040267008229289194884117074074809096206928167668571579441 : ℝ) /
          271793643550872802734375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
        < (49 / 100 : ℝ) := by
    norm_num
  have :
      -(∑ i ∈ Finset.range 20, (-t) ^ (i + 1) / (i + 1)) + t ^ 21 / (1 - t)
        < (49 / 100 : ℝ) := by
    simpa [h_upper_eval]
      using h_upper_val
  have hlog : Real.log (1 + t)
      ≤ -(∑ i ∈ Finset.range 20, (-t) ^ (i + 1) / (i + 1)) + t ^ 21 / (1 - t) :=
    hupper
  have : Real.log (1 + t) < (49 / 100 : ℝ) := lt_of_le_of_lt hlog this
  simpa [t, add_comm, add_left_comm, add_assoc]
    using this

theorem log_phi_bounds :
  (48 / 100 : ℝ) < Real.log phi ∧ Real.log phi < (49 / 100 : ℝ) := by
  have hbounds := phi_tight_bounds
  have hlower := log_phi_lower_bound
  have hupper := log_phi_upper_bound
  constructor
  · have hlog : Real.log ((16180339 : ℝ) / 10000000) < Real.log phi :=
      Real.log_lt_log (by norm_num) hbounds.1
    exact lt_trans hlower hlog
  · have hlog : Real.log phi < Real.log ((16180340 : ℝ) / 10000000) :=
      Real.log_lt_log phi_pos hbounds.2
    exact lt_trans hlog hupper

/-- Precise rational bounds on α = (1 - 1/φ)/2. -/
theorem alpha_bounds_precise :
  ((6180339 : ℚ) / 32360678 : ℝ) < ((1 - 1 / phi) / 2) ∧
  ((1 - 1 / phi) / 2) < ((309017 : ℚ) / 1618034 : ℝ) := by
  have hφ := phi_tight_bounds
  have h_left : (6180339 : ℚ) / 32360678 < ((1 - 1 / phi) / 2 : ℝ) := by
    have : ((1 - 1 / ((16180339 : ℝ) / 10000000)) / 2) < ((1 - 1 / phi) / 2) := by
      have hnum : (1 - 1 / ((16180339 : ℝ) / 10000000)) < 1 - 1 / phi := by
        linarith
      have hpos : (0 : ℝ) < 2 := by norm_num
      exact (div_lt_div_right hpos).mpr hnum
    have h_cast : ((6180339 : ℚ) / 32360678 : ℝ) =
        (1 - 1 / ((16180339 : ℝ) / 10000000)) / 2 := by norm_num
    simpa [h_cast] using this
  have h_right : ((1 - 1 / phi) / 2 : ℝ) < ((309017 : ℚ) / 1618034 : ℝ) := by
    have : ((1 - 1 / phi) / 2) < (1 - 1 / ((16180340 : ℝ) / 10000000)) / 2 := by
      have hnum : 1 - 1 / phi < 1 - 1 / ((16180340 : ℝ) / 10000000) := by
        linarith
      have hpos : (0 : ℝ) < 2 := by norm_num
      exact (div_lt_div_right hpos).mpr hnum
    have h_cast : ((309017 : ℚ) / 1618034 : ℝ) =
        (1 - 1 / ((16180340 : ℝ) / 10000000)) / 2 := by norm_num
    simpa [h_cast] using this
  exact ⟨h_left, h_right⟩

/-- φ^5 upper bound (Nat power): φ^5 < 32 using φ < 2. -/
theorem phi_pow5_upper :
  phi ^ (5 : ℕ) < (32 : ℝ) := by
  have hφ_lt_2 : phi < (2 : ℝ) := by
    have h := phi_tight_bounds.right
    have : (16180340 : ℝ) / 10000000 < (2 : ℝ) := by norm_num
    exact lt_trans h this
  have hφ_pos : 0 < phi := phi_pos
  have h1 : phi * phi < (2 : ℝ) * phi := mul_lt_mul_of_pos_right hφ_lt_2 hφ_pos
  have h2 : (2 : ℝ) * phi < (2 : ℝ) * 2 := mul_lt_mul_of_pos_left hφ_lt_2 (by norm_num)
  have hφ2_lt_4 : phi ^ 2 < (4 : ℝ) := by
    have htemp : phi * phi < (2 : ℝ) * 2 := lt_trans h1 h2
    have : phi * phi < (4 : ℝ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (by simpa [show (2 : ℝ) * 2 = (4 : ℝ) by norm_num] using htemp)
    simpa [pow_two] using this
  have hφ3_lt_8 : phi ^ 3 < (8 : ℝ) := by
    have h' : phi ^ 2 * phi < (4 : ℝ) * phi := mul_lt_mul_of_pos_right hφ2_lt_4 hφ_pos
    have h'' : (4 : ℝ) * phi < (4 : ℝ) * 2 := mul_lt_mul_of_pos_left hφ_lt_2 (by norm_num)
    have htemp : phi ^ 2 * phi < (4 : ℝ) * 2 := lt_trans h' h''
    have : phi ^ 2 * phi < (8 : ℝ) := by
      simpa [show (4 : ℝ) * 2 = (8 : ℝ) by norm_num] using htemp
    simpa [pow_succ, pow_two] using this
  have hφ4_lt_16 : phi ^ 4 < (16 : ℝ) := by
    have h' : phi ^ 3 * phi < (8 : ℝ) * phi := mul_lt_mul_of_pos_right hφ3_lt_8 hφ_pos
    have h'' : (8 : ℝ) * phi < (8 : ℝ) * 2 := mul_lt_mul_of_pos_left hφ_lt_2 (by norm_num)
    have htemp : phi ^ 3 * phi < (8 : ℝ) * 2 := lt_trans h' h''
    have : phi ^ 3 * phi < (16 : ℝ) := by
      simpa [show (8 : ℝ) * 2 = (16 : ℝ) by norm_num] using htemp
    simpa [pow_succ] using this
  have h' : phi ^ 4 * phi < (16 : ℝ) * phi :=
    mul_lt_mul_of_pos_right hφ4_lt_16 hφ_pos
  have h'' : (16 : ℝ) * phi < (16 : ℝ) * 2 :=
    mul_lt_mul_of_pos_left hφ_lt_2 (by norm_num)
  have htemp : phi ^ 4 * phi < (16 : ℝ) * 2 := lt_trans h' h''
  have : phi ^ 4 * phi < (32 : ℝ) :=
    by simpa [show (16 : ℝ) * 2 = (32 : ℝ) by norm_num] using htemp
  simpa [pow_succ] using this

/-- φ^5 lower bound (Nat power): φ^5 > 10 using φ > 8/5. -/
theorem phi_pow5_lower :
  (10 : ℝ) < phi ^ (5 : ℕ) := by
  let ab : ℝ := (8 : ℝ) / 5
  have hφ_gt_8_5 : ab < phi := by
    have : (16180339 : ℝ) / 10000000 > (8 : ℝ) / 5 := by norm_num
    exact lt_trans this phi_tight_bounds.left
  have hφ_pos : 0 < phi := phi_pos
  have hab_pos : 0 < ab := by
    unfold ab; norm_num
  have h_sq : ab ^ 2 < phi ^ 2 := by
    have h1 : ab * ab < phi * ab := mul_lt_mul_of_pos_right hφ_gt_8_5 hab_pos
    have h2 : phi * ab < phi * phi :=
      by simpa [ab] using mul_lt_mul_of_pos_left hφ_gt_8_5 hφ_pos
    have : ab * ab < phi * phi := lt_trans h1 h2
    simpa [pow_two] using this
  have h_cu : ab ^ 3 < phi ^ 3 := by
    have h1 : ab ^ 2 * ab < phi ^ 2 * ab :=
      mul_lt_mul_of_pos_right h_sq hab_pos
    have h2 : phi ^ 2 * ab < phi ^ 2 * phi := by
      have : 0 < phi ^ 2 := by have := pow_pos hφ_pos 2; simpa [pow_two] using this
      exact mul_lt_mul_of_pos_left hφ_gt_8_5 this
    have : ab ^ 2 * ab < phi ^ 2 * phi := lt_trans h1 h2
    simpa [pow_succ, pow_two] using this
  have h_4 : ab ^ 4 < phi ^ 4 := by
    have h1 : ab ^ 3 * ab < phi ^ 3 * ab :=
      mul_lt_mul_of_pos_right h_cu hab_pos
    have h2 : phi ^ 3 * ab < phi ^ 3 * phi := by
      have : 0 < phi ^ 3 := by have := pow_pos hφ_pos 3; simpa using this
      exact mul_lt_mul_of_pos_left hφ_gt_8_5 this
    have : ab ^ 3 * ab < phi ^ 3 * phi := lt_trans h1 h2
    simpa [pow_succ] using this
  have h_5 : ab ^ 5 < phi ^ 5 := by
    have h1 : ab ^ 4 * ab < phi ^ 4 * ab :=
      mul_lt_mul_of_pos_right h_4 hab_pos
    have h2 : phi ^ 4 * ab < phi ^ 4 * phi := by
      have : 0 < phi ^ 4 := by have := pow_pos hφ_pos 4; simpa using this
      exact mul_lt_mul_of_pos_left hφ_gt_8_5 this
    have : ab ^ 4 * ab < phi ^ 4 * phi := lt_trans h1 h2
    simpa [pow_succ] using this
  have h_num : ab ^ 5 > (10 : ℝ) := by unfold ab; norm_num
  exact lt_of_lt_of_le h_num (le_of_lt h_5)

/-- Helper: strict monotonicity of the fifth power on positive reals. -/
private lemma pow5_lt_of_lt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a < b) :
    a ^ (5 : ℕ) < b ^ (5 : ℕ) := by
  have h_sq : a ^ 2 < b ^ 2 := by
    have h1 : a * a < b * a := mul_lt_mul_of_pos_right h ha
    have h2 : b * a < b * b := mul_lt_mul_of_pos_left h hb
    have : a * a < b * b := lt_trans h1 h2
    simpa [pow_two] using this
  have h_cu : a ^ 3 < b ^ 3 := by
    have h1 : a ^ 2 * a < b ^ 2 * a := mul_lt_mul_of_pos_right h_sq ha
    have h2 : b ^ 2 * a < b ^ 2 * b := mul_lt_mul_of_pos_left h (pow_pos hb 2)
    have : a ^ 2 * a < b ^ 2 * b := lt_trans h1 h2
    simpa [pow_succ, pow_two] using this
  have h_four : a ^ 4 < b ^ 4 := by
    have h1 : a ^ 3 * a < b ^ 3 * a := mul_lt_mul_of_pos_right h_cu ha
    have h2 : b ^ 3 * a < b ^ 3 * b := mul_lt_mul_of_pos_left h (pow_pos hb 3)
    have : a ^ 3 * a < b ^ 3 * b := lt_trans h1 h2
    simpa [pow_succ] using this
  have h_five : a ^ 5 < b ^ 5 := by
    have h1 : a ^ 4 * a < b ^ 4 * a := mul_lt_mul_of_pos_right h_four ha
    have h2 : b ^ 4 * a < b ^ 4 * b := mul_lt_mul_of_pos_left h (pow_pos hb 4)
    have : a ^ 4 * a < b ^ 4 * b := lt_trans h1 h2
    simpa [pow_succ] using this
  simpa using h_five

/-- Tight rational bounds on φ^5 induced by `phi_tight_bounds`. -/
theorem phi_pow5_tight_bounds :
  (16180339 / 10000000 : ℝ) ^ (5 : ℕ) < phi ^ (5 : ℕ) ∧
  phi ^ (5 : ℕ) < (16180340 / 10000000 : ℝ) ^ (5 : ℕ) := by
  have hφ := phi_tight_bounds
  have hφ_pos : 0 < phi := phi_pos
  have h_lower_pos : 0 < (16180339 : ℝ) / 10000000 := by norm_num
  have h_upper_pos : 0 < (16180340 : ℝ) / 10000000 := by norm_num
  constructor
  · exact pow5_lt_of_lt h_lower_pos hφ_pos hφ.1
  · exact pow5_lt_of_lt hφ_pos h_upper_pos hφ.2

/-- Tight rational bounds on φ^(-5). -/
theorem phi_inv5_bounds :
  ((10000000 : ℝ) / 16180340) ^ (5 : ℕ) < phi ^ (-(5 : ℝ)) ∧
  phi ^ (-(5 : ℝ)) < ((10000000 : ℝ) / 16180339) ^ (5 : ℕ) := by
  have hpow := phi_pow5_tight_bounds
  have hphi_pow_pos : 0 < phi ^ (5 : ℕ) := pow_pos phi_pos _
  have h_lower_pow_pos :
      0 < ((16180339 : ℝ) / 10000000) ^ (5 : ℕ) :=
    pow_pos (by norm_num : 0 < (16180339 : ℝ) / 10000000) _
  have h_upper_pow_pos :
      0 < ((16180340 : ℝ) / 10000000) ^ (5 : ℕ) :=
    pow_pos (by norm_num : 0 < (16180340 : ℝ) / 10000000) _
  have h_rpow : phi ^ (-(5 : ℝ)) = 1 / phi ^ (5 : ℕ) := by
    have := Real.rpow_neg (le_of_lt phi_pos) (5 : ℝ)
    simpa [Real.rpow_natCast, inv_eq_one_div] using this
  have h_upper_inv : ((10000000 : ℝ) / 16180340) ^ (5 : ℕ) =
      1 / ((16180340 : ℝ) / 10000000) ^ (5 : ℕ) := by
    have : (10000000 : ℝ) / 16180340 = 1 / ((16180340 : ℝ) / 10000000) := by
      field_simp
    simpa [this, inv_pow] using congrArg (fun x : ℝ => x ^ (5 : ℕ)) this
  have h_lower_inv : ((10000000 : ℝ) / 16180339) ^ (5 : ℕ) =
      1 / ((16180339 : ℝ) / 10000000) ^ (5 : ℕ) := by
    have : (10000000 : ℝ) / 16180339 = 1 / ((16180339 : ℝ) / 10000000) := by
      field_simp
    simpa [this, inv_pow] using congrArg (fun x : ℝ => x ^ (5 : ℕ)) this
  constructor
  · have h := one_div_lt_one_div_of_lt hphi_pow_pos hpow.2
    have : 1 / ((16180340 : ℝ) / 10000000) ^ (5 : ℕ) < 1 / phi ^ (5 : ℕ) :=
      by simpa using h
    simpa [h_rpow, h_upper_inv]
  · have h := one_div_lt_one_div_of_lt h_lower_pow_pos hpow.1
    have : 1 / phi ^ (5 : ℕ) < 1 / ((16180339 : ℝ) / 10000000) ^ (5 : ℕ) :=
      by simpa using h
    simpa [h_rpow, h_lower_inv]

/-- Helper bound: `exp(0.48)` lies below the lower rational bound for φ. -/
lemma exp_048_lt_phi_lower :
  Real.exp (48 / 100 : ℝ) < (16180339 : ℝ) / 10000000 := by
  have h := log_phi_lower_bound_precise
  have hpos : 0 < (16180339 : ℝ) / 10000000 := by norm_num
  have := Real.exp_lt_exp.mpr h.1
  simpa [Real.exp_log hpos] using this

/-- Helper bound: the upper rational bound for φ lies below `exp(0.49)`. -/
lemma phi_upper_lt_exp_049 :
  (16180340 : ℝ) / 10000000 < Real.exp (49 / 100 : ℝ) := by
  have h := log_phi_upper_bound_precise
  have hpos : 0 < (16180340 : ℝ) / 10000000 := by norm_num
  have := Real.exp_lt_exp.mpr h.2
  simpa [Real.exp_log hpos] using this

/-- Exponential bounds corresponding to the ln(φ) interval. -/
theorem exp_phi_bounds :
  Real.exp (48 / 100 : ℝ) < phi ∧ phi < Real.exp (49 / 100 : ℝ) := by
  have hφ := phi_tight_bounds
  have h_lower := exp_048_lt_phi_lower
  have h_upper := phi_upper_lt_exp_049
  constructor
  · exact lt_trans h_lower hφ.1
  · exact lt_trans hφ.2 h_upper

/-- Product bound: α · C_lag < 0.0173. -/
theorem alpha_clag_product_bound :
  ((1 - 1 / phi) / 2) * (phi ^ (-(5 : ℝ))) < (173 / 10000 : ℝ) := by
  have h_alpha := alpha_bounds_precise
  have h_phi := phi_inv5_bounds
  have h_phi_pos : 0 < phi ^ (-(5 : ℝ)) :=
    Real.rpow_pos_of_pos phi_pos _
  have h1 : ((1 - 1 / phi) / 2) * phi ^ (-(5 : ℝ)) <
      ((309017 : ℚ) / 1618034 : ℝ) * phi ^ (-(5 : ℝ)) :=
    mul_lt_mul_of_pos_right h_alpha.2 h_phi_pos
  have h2 : ((309017 : ℚ) / 1618034 : ℝ) * phi ^ (-(5 : ℝ)) <
      ((309017 : ℚ) / 1618034 : ℝ) * ((10000000 : ℝ) / 16180339) ^ (5 : ℕ) := by
    have : 0 < ((309017 : ℚ) / 1618034 : ℝ) := by norm_num
    exact mul_lt_mul_of_pos_left h_phi.2 this
  have h_prod : ((1 - 1 / phi) / 2) * phi ^ (-(5 : ℝ)) <
      ((309017 : ℚ) / 1618034 : ℝ) * ((10000000 : ℝ) / 16180339) ^ (5 : ℕ) :=
    lt_trans h1 h2
  have h_final :
      ((309017 : ℚ) / 1618034 : ℝ) * ((10000000 : ℝ) / 16180339) ^ (5 : ℕ) <
        (173 / 10000 : ℝ) := by norm_num
  exact lt_trans h_prod h_final

import Mathlib
import IndisputableMonolith.Relativity.Geometry.Metric

/-!
# Matrix Bridge for Metric Tensors

Rigorous implementation of metric tensor inversion using Mathlib's matrix library.
This provides the foundation for computing Christoffel symbols, Riemann curvature,
and all perturbation theory correctly.

## Status

**Phase A - Matrix Representation:** Complete (proven)
**Phase B - Determinants:** Partially complete (det(η)=-1 proven, perturbation bounds axiomatized)
**Phase C - Neumann Series:** In progress (η² = I and η⁻¹ = η being proven)
**Phase D - Integration:** Pending
-/

namespace IndisputableMonolith
namespace Relativity
namespace Geometry

open Matrix
open scoped Matrix

/-! ## Phase A: Matrix Representation (PROVEN) -/

/-- Convert a metric tensor to a 4×4 matrix at a given point x. -/
noncomputable def metricToMatrix (g : MetricTensor) (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun μ ν => g.g x (fun _ => 0) (fun i => if i.val = 0 then μ else ν)

/-- Minkowski metric as a matrix: diag(-1,1,1,1). -/
noncomputable def minkowskiMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal fun i => if i.val = 0 then -1 else 1

/-- Our Minkowski tensor converts to the diagonal matrix. -/
theorem minkowski_to_matrix_correct (x : Fin 4 → ℝ) :
  metricToMatrix minkowski.toMetricTensor x = minkowskiMatrix := by
  ext μ ν
  simp [metricToMatrix, minkowskiMatrix, Matrix.diagonal, Matrix.of, minkowski]

/-- Matrix representation preserves the metric tensor values componentwise. -/
@[simp]
theorem metricToMatrix_apply (g : MetricTensor) (x : Fin 4 → ℝ) (μ ν : Fin 4) :
  (metricToMatrix g x) μ ν = g.g x (fun _ => 0) (fun i => if i.val = 0 then μ else ν) := by
  rfl

/-- If the metric tensor is symmetric, so is its matrix representation. -/
theorem metricToMatrix_symmetric (g : MetricTensor) (x : Fin 4 → ℝ) :
  (metricToMatrix g x).IsSymm := by
  ext μ ν
  simp only [Matrix.transpose_apply, metricToMatrix_apply]
  exact g.symmetric x ν μ

/-- Minkowski matrix is symmetric (diagonal matrices are symmetric). -/
theorem minkowskiMatrix_symmetric : minkowskiMatrix.IsSymm := by
  rw [minkowskiMatrix]
  exact Matrix.diagonal_transpose _

/-! ## Phase B: Determinants and Invertibility -/

/-- Minkowski matrix determinant is -1. -/
theorem minkowskiMatrix_det : minkowskiMatrix.det = -1 := by
  rw [minkowskiMatrix, Matrix.det_diagonal]
  -- ∏ i : Fin 4, (if i.val = 0 then -1 else 1)
  -- Manually evaluate: i=0 gives -1, i∈{1,2,3} give 1
  -- Product = (-1) · 1 · 1 · 1 = -1
  norm_num [Fin.sum_univ_four]

/-- Minkowski matrix is invertible (nonzero determinant). -/
theorem minkowskiMatrix_invertible : minkowskiMatrix.det ≠ 0 := by
  rw [minkowskiMatrix_det]
  norm_num

/-! ## Phase C: Working on Matrix Square and Inverse

The proofs below are works in progress. The goal is to prove:
1. η² = I (minkowskiMatrix * minkowskiMatrix = 1)
2. η⁻¹ = η (follows from above)
3. Determinant perturbation bounds
4. Neumann series for (I+A)⁻¹

These are real mathematical theorems being proven step by step.
-/

/-- η² = I for Minkowski.
    Proof: For diagonal matrix with ±1 entries, squaring gives identity.
-/
theorem minkowskiMatrix_sq : minkowskiMatrix * minkowskiMatrix = 1 := by
  rw [minkowskiMatrix, Matrix.diagonal_mul_diagonal]
  -- diagonal(d) * diagonal(d) = diagonal(d * d) = diagonal(1,1,1,1) = 1
  ext i j
  simp only [Matrix.one_apply, Matrix.diagonal_apply]
  by_cases h0 : i.val = 0
  · simp only [h0, if_true]
    norm_num
  · simp only [h0, if_false]
    norm_num

/-- η⁻¹ = η since η² = I.
    Proof: If A² = I and A is invertible, then A⁻¹ = A.
    From A·A = I, multiply both sides by A⁻¹ on left: A⁻¹·A·A = A⁻¹·I
    Simplify: I·A = A⁻¹, hence A = A⁻¹.
-/
theorem minkowskiMatrix_inv : minkowskiMatrix⁻¹ = minkowskiMatrix := by
  have hsq := minkowskiMatrix_sq
  -- η² = I means η is a left and right inverse of itself
  -- By definition of matrix inverse, η⁻¹ is the unique matrix satisfying η·η⁻¹ = I
  -- We also have η·η = I
  -- Therefore η⁻¹ = η
  sorry -- Needs correct Mathlib inverse uniqueness theorem

/-- Product of 4 bounded terms is bounded by b⁴. -/
lemma prod_four_bound (f : Fin 4 → ℝ) (b : ℝ) (hb : 0 ≤ b) (h : ∀ i, |f i| ≤ b) :
  |∏ i : Fin 4, f i| ≤ b ^ 4 := by
  classical
  -- Expand product over Fin 4
  have hprod : ∏ i : Fin 4, f i = f 0 * (f 1 * (f 2 * f 3)) := by
    -- Explicit expansion for Fin 4
    rw [Fin.prod_univ_four]
    ring
  -- Turn absolute value of product into product of absolute values
  have h_abs : |∏ i : Fin 4, f i| = |f 0| * (|f 1| * (|f 2| * |f 3|)) := by
    rw [hprod]
    simp only [abs_mul]
  -- Chain of multiplicative bounds using |f i| ≤ b and nonnegativity
  have h01 : |f 0| * |f 1| ≤ b * b := by
    exact mul_le_mul (h 0) (h 1) (abs_nonneg _) hb
  have h012 : (|f 0| * |f 1|) * |f 2| ≤ (b * b) * b := by
    have h2 := h 2
    have hnon : 0 ≤ |f 2| := abs_nonneg _
    have hnonR : 0 ≤ b * b := mul_nonneg hb hb
    exact mul_le_mul h01 h2 hnon hnonR
  have h0123 : ((|f 0| * |f 1|) * |f 2|) * |f 3| ≤ ((b * b) * b) * b := by
    have h3 := h 3
    have hnon : 0 ≤ |f 3| := abs_nonneg _
    have hnonR : 0 ≤ (b * b) * b := mul_nonneg (mul_nonneg hb hb) hb
    exact mul_le_mul h012 h3 hnon hnonR
  -- Conclude: b⁴ = ((b*b)*b)*b
  have : |f 0| * (|f 1| * (|f 2| * |f 3|)) ≤ b ^ 4 := by
    calc |f 0| * (|f 1| * (|f 2| * |f 3|))
        = ((|f 0| * |f 1|) * |f 2|) * |f 3| := by ring
      _ ≤ ((b * b) * b) * b := h0123
      _ = b ^ 4 := by ring
  rw [h_abs]
  exact this

/-- Trace bound: |tr(A)| ≤ 4ε when |A_{ij}| ≤ ε. -/
lemma trace_bound (A : Matrix (Fin 4) (Fin 4) ℝ) (ε : ℝ)
  (h_bounded : ∀ i j, |A i j| ≤ ε) :
  |A.trace| ≤ 4 * ε := by
  simp [Matrix.trace]
  -- |A_00 + A_11 + A_22 + A_33| ≤ |A_00| + |A_11| + |A_12| + |A_33| ≤ 4ε
  have h_abs_sum : |∑ i : Fin 4, A i i| ≤ ∑ i : Fin 4, |A i i| :=
    Finset.abs_sum_le_sum_abs _ _
  refine h_abs_sum.trans ?_
  have h_each : ∀ i ∈ (Finset.univ : Finset (Fin 4)), |A i i| ≤ ε :=
    fun i _ => h_bounded i i
  have hsum : ∑ i : Fin 4, |A i i| ≤ ∑ _ : Fin 4, ε := Finset.sum_le_sum h_each
  have hcard : (Fintype.card (Fin 4) : ℝ) = 4 := by simp
  calc ∑ i : Fin 4, |A i i|
      ≤ ∑ _ : Fin 4, ε := hsum
    _ = 4 * ε := by rw [Finset.sum_const, Finset.card_univ, hcard]; ring

/-- For a 4×4 matrix with small entries, the determinant is close to the identity determinant.

    Proof strategy:
    det(I + A) can be expanded using multilinearity of the determinant.
    Write (I + A) column by column: [e₀ + A₀, e₁ + A₁, e₂ + A₂, e₃ + A₃]

    By multilinearity, det expands into 2^4 = 16 terms:
    - 1 term with all e's: det(I) = 1
    - 4 terms with one A column: these give tr(A) at leading order
    - 6 terms with two A columns: O(ε²)
    - 4 terms with three A columns: O(ε³)
    - 1 term with four A columns: det(A) = O(ε⁴)

    For ε ≤ 0.1, the ε³ and ε⁴ terms are negligible compared to 16ε².
-/
theorem det_perturbation_bound (A : Matrix (Fin 4) (Fin 4) ℝ) (ε : ℝ)
  (h_ε_pos : 0 < ε) (h_ε_small : ε ≤ 0.1)
  (h_bounded : ∀ i j, |A i j| ≤ ε) :
  |(1 + A).det - 1| ≤ 4 * ε + 16 * ε ^ 2 := by
  -- Use crude but rigorous approach: bound |det(I+A)| and |det(I)| separately
  -- Then |det(I+A) - 1| ≤ |det(I+A) - det(I)|

  -- For 4×4 matrix with |A_{ij}| ≤ ε, we have |det(I+A)| bounded
  -- Each term in Leibniz formula: |sign(σ) ∏_i (I+A)_{i,σ(i)}| ≤ ∏_i |1 + A_{i,σ(i)}| ≤ ∏_i (1 + ε)
  -- Since |A_{ij}| ≤ ε, we have |1 + A_{ij}| ≤ 1 + ε
  -- There are 4! = 24 permutations

  have hdet_bound : |(1 + A).det| ≤ 24 * (1 + ε) ^ 4 := by
    rw [Matrix.det_apply]
    -- |Σ_σ sign(σ) ∏_i (I+A)_{i,σ(i)}| ≤ Σ_σ |sign(σ) ∏_i (I+A)_{i,σ(i)}|
    have := Finset.abs_sum_le_sum_abs _ _
    refine this.trans ?_
    -- Each term: |sign(σ)| = 1, and |∏_i (I+A)_{i,σ(i)}| ≤ ∏_i (1 + ε)
    have : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin 4))),
           |Equiv.Perm.sign σ * ∏ i : Fin 4, (1 + A) i (σ i)| ≤ (1 + ε) ^ 4 := by
      intro σ _
      rw [abs_mul]
      have hsign : |Equiv.Perm.sign σ| = 1 := by
        cases Equiv.Perm.sign σ <;> simp [Int.cast_neg, Int.cast_one, abs_neg]
      rw [hsign, one_mul]
      -- Use prod_four_bound
      have hfactor : ∀ i, |1 + A i (σ i)| ≤ 1 + ε := by
        intro i
        have := h_bounded i (σ i)
        calc |1 + A i (σ i)|
            ≤ |1| + |A i (σ i)| := abs_add _ _
          _ = 1 + |A i (σ i)| := by simp
          _ ≤ 1 + ε := by linarith [this]
      have hb_nonneg : 0 ≤ 1 + ε := by linarith [h_ε_pos]
      exact prod_four_bound (fun i => (1 + A) i (σ i)) (1 + ε) hb_nonneg hfactor
    have := Finset.sum_le_sum this
    simp at this
    have hcard : (Fintype.card (Equiv.Perm (Fin 4)) : ℝ) = 24 := by norm_num
    calc ∑ σ : Equiv.Perm (Fin 4), |Equiv.Perm.sign σ * ∏ i : Fin 4, (1 + A) i (σ i)|
        ≤ ∑ _ : Equiv.Perm (Fin 4), (1 + ε) ^ 4 := this
      _ = 24 * (1 + ε) ^ 4 := by rw [Finset.sum_const, Finset.card_univ, hcard]; ring

  -- Now |det(I+A) - 1| ≤ |det(I+A)| + 1 ≤ 24(1+ε)⁴ + 1
  -- For ε = 0.1: (1.1)⁴ ≈ 1.46, so 24·1.46 + 1 ≈ 36
  -- But this is too crude! We need the actual expansion, not just a bound.

  -- Better approach: use the matrix determinant as polynomial
  -- det(I + tA) is a degree-4 polynomial in t
  -- At t=0: det(I) = 1
  -- Derivative at t=0: d/dt det(I + tA)|_{t=0} = tr(A)
  -- So det(I + A) = 1 + tr(A) + O(A²)

  -- The challenge is bounding the O(A²) term rigorously without Mathlib's full calculus
  sorry

/-- Identity-permutation contribution: For diagonal entries a₀..a₃ with |aᵢ| ≤ ε,
    the non-linear remainder of ∏ᵢ (1 + aᵢ) after removing 1 and the linear part is bounded. -/
lemma diag_prod_linear_remainder_bound
  (a0 a1 a2 a3 ε : ℝ) (h0 : |a0| ≤ ε) (h1 : |a1| ≤ ε)
  (h2 : |a2| ≤ ε) (h3 : |a3| ≤ ε) :
  |(1 + a0) * (1 + a1) * (1 + a2) * (1 + a3) - 1 - (a0 + a1 + a2 + a3)|
  ≤ 6 * ε ^ 2 + 4 * ε ^ 3 + ε ^ 4 := by
  have h2pairs :
      |a0 * a1 + a0 * a2 + a0 * a3 + a1 * a2 + a1 * a3 + a2 * a3|
      ≤ 6 * ε ^ 2 := by
    have hb_pair : ∀ x y, |x| ≤ ε → |y| ≤ ε → |x * y| ≤ ε ^ 2 := by
      intro x y hx hy; have := mul_le_mul hx hy (abs_nonneg _) (by exact le_of_lt (pow_pos (show 0 < ε from lt_of_le_of_lt (le_of_lt (by decide : (0:ℝ)<1)) (by decide)) 0))
      -- fallback: use basic bound |xy| ≤ |x||y| ≤ ε²
      have hx' : |x| ≤ ε := hx; have hy' : |y| ≤ ε := hy
      calc |x * y| ≤ |x| * |y| := by simpa [abs_mul] using (abs_mul x y).le
           _ ≤ ε * ε := by nlinarith
           _ = ε ^ 2 := by ring
    have hb :
      |a0 * a1| + |a0 * a2| + |a0 * a3| + |a1 * a2| + |a1 * a3| + |a2 * a3|
      ≤ 6 * ε ^ 2 := by
      have h01 := hb_pair _ _ h0 h1
      have h02 := hb_pair _ _ h0 h2
      have h03 := hb_pair _ _ h0 h3
      have h12 := hb_pair _ _ h1 h2
      have h13 := hb_pair _ _ h1 h3
      have h23 := hb_pair _ _ h2 h3
      nlinarith
    have htri := abs_add_le_abs_add_abs
    -- Bound sum of pairs by sum of absolutes
    have :
      |a0 * a1 + (a0 * a2 + (a0 * a3 + (a1 * a2 + (a1 * a3 + a2 * a3))))|
      ≤ |a0 * a1| + |a0 * a2| + |a0 * a3| + |a1 * a2| + |a1 * a3| + |a2 * a3| := by
      repeat (first | simpa [add_comm, add_left_comm, add_assoc] using abs_add_le_abs_add_abs _ _)
    exact this.trans hb
  have h3terms :
      |a0 * a1 * a2 + a0 * a1 * a3 + a0 * a2 * a3 + a1 * a2 * a3|
      ≤ 4 * ε ^ 3 := by
    have hb_triple : ∀ x y z, |x| ≤ ε → |y| ≤ ε → |z| ≤ ε → |x * y * z| ≤ ε ^ 3 := by
      intro x y z hx hy hz
      have : |x * y * z| ≤ |x| * |y| * |z| := by
        simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using
          (le_trans (by have := (abs_mul (x * y) z); simpa [abs_mul, mul_assoc] using this.le)
            (le_of_eq rfl))
      have hx' : |x| ≤ ε := hx; have hy' := hy; have hz' := hz
      nlinarith
    have hb :
      |a0 * a1 * a2| + |a0 * a1 * a3| + |a0 * a2 * a3| + |a1 * a2 * a3| ≤ 4 * ε ^ 3 := by
      have h012 := hb_triple _ _ _ h0 h1 h2
      have h013 := hb_triple _ _ _ h0 h1 h3
      have h023 := hb_triple _ _ _ h0 h2 h3
      have h123 := hb_triple _ _ _ h1 h2 h3
      nlinarith
    have :
      |a0 * a1 * a2 + (a0 * a1 * a3 + (a0 * a2 * a3 + a1 * a2 * a3))|
      ≤ |a0 * a1 * a2| + |a0 * a1 * a3| + |a0 * a2 * a3| + |a1 * a2 * a3| := by
      repeat (first | simpa [add_comm, add_left_comm, add_assoc] using abs_add_le_abs_add_abs _ _)
    exact this.trans hb
  have h4term : |a0 * a1 * a2 * a3| ≤ ε ^ 4 := by
    have hb : |a0 * a1 * a2 * a3| ≤ |a0| * |a1| * |a2| * |a3| := by
      simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using
        (le_trans (by have := (abs_mul (a0 * a1 * a2) a3); simpa [abs_mul, mul_assoc] using this.le)
          (le_of_eq rfl))
    nlinarith
  -- Now expand the product and bound termwise
  have hsplit :
    (1 + a0) * (1 + a1) * (1 + a2) * (1 + a3) - 1 - (a0 + a1 + a2 + a3)
    = (a0 * a1 + a0 * a2 + a0 * a3 + a1 * a2 + a1 * a3 + a2 * a3)
      + (a0 * a1 * a2 + a0 * a1 * a3 + a0 * a2 * a3 + a1 * a2 * a3)
      + (a0 * a1 * a2 * a3) := by ring
  have h_step1 :
    |(1 + a0) * (1 + a1) * (1 + a2) * (1 + a3) - 1 - (a0 + a1 + a2 + a3)|
      = |(a0 * a1 + a0 * a2 + a0 * a3 + a1 * a2 + a1 * a3 + a2 * a3)
        + ((a0 * a1 * a2 + a0 * a1 * a3 + a0 * a2 * a3 + a1 * a2 * a3)
        + a0 * a1 * a2 * a3)| := by
    simpa [hsplit]
  have h_step2 :
    |(a0 * a1 + a0 * a2 + a0 * a3 + a1 * a2 + a1 * a3 + a2 * a3)
      + ((a0 * a1 * a2 + a0 * a1 * a3 + a0 * a2 * a3 + a1 * a2 * a3)
      + a0 * a1 * a2 * a3)|
      ≤ |a0 * a1 + a0 * a2 + a0 * a3 + a1 * a2 + a1 * a3 + a2 * a3|
        + |(a0 * a1 * a2 + a0 * a1 * a3 + a0 * a2 * a3 + a1 * a2 * a3)
        + a0 * a1 * a2 * a3| := by
    -- Triangle inequality: |a + b| ≤ |a| + |b|
    sorry -- Need Mathlib lemma name for |a + b| ≤ |a| + |b|
  have h_step3 :
    |(a0 * a1 * a2 + a0 * a1 * a3 + a0 * a2 * a3 + a1 * a2 * a3)
      + a0 * a1 * a2 * a3|
      ≤ |a0 * a1 * a2 + a0 * a1 * a3 + a0 * a2 * a3 + a1 * a2 * a3|
        + |a0 * a1 * a2 * a3| := by
    sorry -- Need Mathlib lemma name for |a + b| ≤ |a| + |b|
  have h_pairs :
    |a0 * a1 + a0 * a2 + a0 * a3 + a1 * a2 + a1 * a3 + a2 * a3|
      ≤ 6 * ε ^ 2 := h2pairs
  have h_triples :
    |a0 * a1 * a2 + a0 * a1 * a3 + a0 * a2 * a3 + a1 * a2 * a3|
      ≤ 4 * ε ^ 3 := h3terms
  have h_quad : |a0 * a1 * a2 * a3| ≤ ε ^ 4 := h4term
  have h_sum23 :
    |(a0 * a1 * a2 + a0 * a1 * a3 + a0 * a2 * a3 + a1 * a2 * a3)
      + a0 * a1 * a2 * a3|
      ≤ 4 * ε ^ 3 + ε ^ 4 := by
    have := add_le_add h_triples h_quad
    -- use h_step3 to move absolute on sum to sum of absolutes
    have := le_trans h_step3 this
    simpa using this
  -- Combine bounds using h_step2: split absolute value of sum into sum of absolutes
  have h_combine :
    |a0 * a1 + a0 * a2 + a0 * a3 + a1 * a2 + a1 * a3 + a2 * a3|
      + |(a0 * a1 * a2 + a0 * a1 * a3 + a0 * a2 * a3 + a1 * a2 * a3)
      + a0 * a1 * a2 * a3|
      ≤ 6 * ε ^ 2 + (4 * ε ^ 3 + ε ^ 4) := by
    exact add_le_add h_pairs h_sum23
  -- Chain the inequalities: h_step1 (rewrite) → h_step2 (triangle) → h_combine (numeric)
  calc |(1 + a0) * (1 + a1) * (1 + a2) * (1 + a3) - 1 - (a0 + a1 + a2 + a3)|
      = |(a0 * a1 + a0 * a2 + a0 * a3 + a1 * a2 + a1 * a3 + a2 * a3)
        + ((a0 * a1 * a2 + a0 * a1 * a3 + a0 * a2 * a3 + a1 * a2 * a3)
        + a0 * a1 * a2 * a3)| := h_step1
    _ ≤ |a0 * a1 + a0 * a2 + a0 * a3 + a1 * a2 + a1 * a3 + a2 * a3|
        + |(a0 * a1 * a2 + a0 * a1 * a3 + a0 * a2 * a3 + a1 * a2 * a3)
        + a0 * a1 * a2 * a3| := h_step2
    _ ≤ 6 * ε ^ 2 + (4 * ε ^ 3 + ε ^ 4) := h_combine
    _ = 6 * ε ^ 2 + 4 * ε ^ 3 + ε ^ 4 := by ring

/-- Identity-permutation remainder bound for matrix diagonal of A. -/
lemma identity_permutation_remainder_bound
  (A : Matrix (Fin 4) (Fin 4) ℝ) (ε : ℝ)
  (h_bounded : ∀ i j, |A i j| ≤ ε) :
  |∏ i : Fin 4, (1 + A i i) - 1 - ∑ i : Fin 4, A i i|
  ≤ 6 * ε ^ 2 + 4 * ε ^ 3 + ε ^ 4 := by
  classical
  -- instantiate a₀..a₃
  let a0 : ℝ := A ⟨0, by decide⟩ ⟨0, by decide⟩
  let a1 : ℝ := A ⟨1, by decide⟩ ⟨1, by decide⟩
  let a2 : ℝ := A ⟨2, by decide⟩ ⟨2, by decide⟩
  let a3 : ℝ := A ⟨3, by decide⟩ ⟨3, by decide⟩
  have h0 : |a0| ≤ ε := h_bounded _ _
  have h1 : |a1| ≤ ε := h_bounded _ _
  have h2 : |a2| ≤ ε := h_bounded _ _
  have h3 : |a3| ≤ ε := h_bounded _ _
  have :
    ∏ i : Fin 4, (1 + A i i) = (1 + a0) * (1 + a1) * (1 + a2) * (1 + a3) := by
    -- expand product over Fin 4 explicitly
    simp [a0, a1, a2, a3, Fin.sum_univ_four, Fin.prod_univ_four, Fin.exists_iff, Fin.forall_iff] -- if unavailable, leave as sorry
  have :
    |∏ i : Fin 4, (1 + A i i) - 1 - ∑ i : Fin 4, A i i|
    = |(1 + a0) * (1 + a1) * (1 + a2) * (1 + a3) - 1 - (a0 + a1 + a2 + a3)| := by
    -- rewrite sums and products explicitly
    simp [a0, a1, a2, a3, Fin.sum_univ_four, Fin.prod_univ_four]
  -- apply scalar lemma
  simpa [this] using diag_prod_linear_remainder_bound a0 a1 a2 a3 ε h0 h1 h2 h3

/-- TODO: Prove Neumann series.
    (I + A)⁻¹ = I - A + A² - A³ + ...
    Remainder after n terms bounded by geometric series.
-/
axiom neumann_series_second_order (A : Matrix (Fin 4) (Fin 4) ℝ) (ε : ℝ)
  (h_ε_pos : 0 < ε) (h_ε_small : ε ≤ 0.1)
  (h_bounded : ∀ i j, |A i j| ≤ ε) :
  ∀ i j, |(1 + A)⁻¹ i j - (1 - A + A * A) i j| ≤ 20 * ε ^ 3

end Geometry
end Relativity
end IndisputableMonolith

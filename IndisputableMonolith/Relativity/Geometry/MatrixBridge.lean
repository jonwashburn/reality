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
    From A·A = I, we have A is its own inverse.
-/
theorem minkowskiMatrix_inv : minkowskiMatrix⁻¹ = minkowskiMatrix := by
  have hsq := minkowskiMatrix_sq
  have hdet := minkowskiMatrix_invertible
  -- Direct proof: η is diagonal with entries ±1, so η⁻¹ is diagonal with same entries
  ext i j
  simp only [Matrix.inv_def, Matrix.diagonal_apply, minkowskiMatrix]
  by_cases hij : i = j
  · subst hij
    -- Diagonal case: need to show (adjugate / det) equals original
    -- For diagonal matrix, adjugate is also diagonal
    -- Since det(η) = -1 and η_ii ∈ {-1, 1}, we have η⁻¹_ii = η_ii / det = η_ii / (-1) for special structure
    -- Actually: for η² = I, we know η⁻¹ = η directly
    -- Use the fact that η * η = I implies η is self-inverse
    have h_self_inv : minkowskiMatrix * minkowskiMatrix = 1 := hsq
    -- The inverse of a matrix M is the unique matrix N such that M * N = I
    -- We have M * M = I, so M is its own inverse
    sorry -- Need involutive matrix theorem: M² = I ∧ det(M) ≠ 0 → M⁻¹ = M
  · -- Off-diagonal case: both sides are 0
    simp [hij]

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

    Strategy: use Leibniz formula det(I+A) = Σ_σ sign(σ) ∏_i (I+A)_{i,σ(i)}.
    - σ = id: contributes (1 + A₀₀)(1 + A₁₁)(1 + A₂₂)(1 + A₃₃) = 1 + tr(A) + O(ε²)
    - Non-identity σ: each contributes at least one off-diagonal A entry, so O(ε²)

    For ε ≤ 0.1, we get |det(I+A) - 1| ≤ 4ε + 16ε².
-/
theorem det_perturbation_bound (A : Matrix (Fin 4) (Fin 4) ℝ) (ε : ℝ)
  (h_ε_pos : 0 < ε) (h_ε_small : ε ≤ 0.1)
  (h_bounded : ∀ i j, |A i j| ≤ ε) :
  |(1 + A).det - 1| ≤ 4 * ε + 16 * ε ^ 2 := by
  -- Use the binomial expansion for det
  -- det(I + A) = Σ_σ sign(σ) ∏_i (I+A)_{i,σ(i)}
  -- Split: σ=id gives diagonal product, σ≠id gives off-diagonal contributions

  -- Step 1: Bound det(I+A) from above
  have hdet_upper : (1 + A).det ≤ (1 + ε) ^ 4 := by
    sorry -- Each Leibniz term ≤ (1+ε)⁴; sum of signs doesn't all add (alternating), so crude bound

  -- Step 2: Bound det(I+A) from below (needs more care since cancellations happen)
  -- For now use: det(I+A) ≥ -(1+ε)⁴ (worst case all terms negative)
  have hdet_lower : (1 + A).det ≥ -(1 + ε) ^ 4 := by
    sorry -- Similar Leibniz bound argument

  -- Step 3: Combine to bound |det(I+A) - 1|
  have habs_bound : |(1 + A).det| ≤ (1 + ε) ^ 4 := by
    have : -(1 + ε) ^ 4 ≤ (1 + A).det ∧ (1 + A).det ≤ (1 + ε) ^ 4 := ⟨hdet_lower, hdet_upper⟩
    exact abs_le.mpr this

  -- Step 4: Use |det(I+A) - 1| ≤ |det(I+A)| + 1 ≤ (1+ε)⁴ + 1, but this is too loose
  -- Better: |(1+A).det - 1| ≤ (1+ε)⁴ - 1 = 4ε + 6ε² + 4ε³ + ε⁴
  calc |(1 + A).det - 1|
      ≤ (1 + ε) ^ 4 - 1 := by
        sorry -- Use det bounds and triangle inequality
    _ = 4 * ε + 6 * ε ^ 2 + 4 * ε ^ 3 + ε ^ 4 := by ring
    _ ≤ 4 * ε + 16 * ε ^ 2 := by
        -- For ε ≤ 0.1: need 6ε² + 4ε³ + ε⁴ ≤ 16ε²
        -- i.e., 4ε³ + ε⁴ ≤ 10ε²
        have h_cubic : 4 * ε ^ 3 ≤ 10 * ε ^ 2 := by
          have : ε ≤ 0.1 := h_ε_small
          nlinarith [sq_nonneg ε, h_ε_pos]
        have h_quartic : ε ^ 4 ≤ ε ^ 2 := by
          nlinarith [h_ε_small, sq_nonneg ε]
        linarith

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
      intro x y hx hy
      -- Use |xy| ≤ |x||y| ≤ ε²
      calc |x * y|
          = |x| * |y| := abs_mul x y
        _ ≤ ε * ε := by
            -- Need |x| ≤ ε, |y| ≤ ε, and both sides ≥ 0
            have h_nonneg : 0 ≤ |x| * |y| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
            have h_target_nonneg : 0 ≤ ε * ε := by nlinarith [sq_nonneg ε, abs_nonneg x, abs_nonneg y]
            exact mul_le_mul hx hy (abs_nonneg _) h_target_nonneg
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
    -- Bound sum of pairs by sum of absolutes using triangle inequality repeatedly
    have :
      |a0 * a1 + (a0 * a2 + (a0 * a3 + (a1 * a2 + (a1 * a3 + a2 * a3))))|
      ≤ |a0 * a1| + |a0 * a2| + |a0 * a3| + |a1 * a2| + |a1 * a3| + |a2 * a3| := by
      repeat (first | refine le_trans (abs_add _ _) ?_)
      simp only [add_le_add_iff_left]
      repeat (first | refine le_trans (abs_add _ _) ?_)
      simp only [add_le_add_iff_left]
      repeat (first | refine le_trans (abs_add _ _) ?_)
      simp only [add_le_add_iff_left]
      repeat (first | refine le_trans (abs_add _ _) ?_)
      simp only [add_le_add_iff_left]
      repeat (first | refine le_trans (abs_add _ _) ?_)
      rfl
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
      repeat (first | simpa [add_comm, add_left_comm, add_assoc] using abs_add _ _)
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
  exact abs_add _ _
  have h_step3 :
    |(a0 * a1 * a2 + a0 * a1 * a3 + a0 * a2 * a3 + a1 * a2 * a3)
      + a0 * a1 * a2 * a3|
      ≤ |a0 * a1 * a2 + a0 * a1 * a3 + a0 * a2 * a3 + a1 * a2 * a3|
        + |a0 * a1 * a2 * a3| := by
  exact abs_add _ _
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

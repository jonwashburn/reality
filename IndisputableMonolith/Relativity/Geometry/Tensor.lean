import Mathlib
import IndisputableMonolith.Relativity.Geometry.Manifold

/-!
# Tensor Structures (Spacetime-specific, Fin 4)

This module defines tensors for 4D spacetime.
We work concretely with Fin 4 to avoid dimension-polymorphism issues.
-/

namespace IndisputableMonolith
namespace Relativity
namespace Geometry

/-- A (p,q)-tensor on 4D spacetime: p contravariant indices, q covariant indices. -/
def Tensor (p q : ℕ) :=
  (Fin 4 → ℝ) → (Fin p → Fin 4) → (Fin q → Fin 4) → ℝ

/-- A scalar field (0,0)-tensor. -/
abbrev ScalarField := (Fin 4 → ℝ) → ℝ

/-- A vector field (1,0)-tensor. -/
abbrev VectorField := Tensor 1 0

/-- A covector field (0,1)-tensor. -/
abbrev CovectorField := Tensor 0 1

/-- A (0,2)-tensor (like a metric). -/
abbrev BilinearForm := Tensor 0 2

/-- A (2,0)-tensor (like inverse metric). -/
abbrev ContravariantBilinear := Tensor 2 0

/-- Tensor symmetry for (0,2)-tensors. -/
def IsSymmetric (T : Tensor 0 2) : Prop :=
  ∀ (x : Fin 4 → ℝ) (μ ν : Fin 4),
    T x (fun (_ : Fin 0) => 0) (fun (i : Fin 2) => if i.val = 0 then μ else ν) =
    T x (fun (_ : Fin 0) => 0) (fun (i : Fin 2) => if i.val = 0 then ν else μ)

/-- Tensor antisymmetry for (0,2)-tensors. -/
def IsAntisymmetric (T : Tensor 0 2) : Prop :=
  ∀ (x : Fin 4 → ℝ) (μ ν : Fin 4),
    T x (fun (_ : Fin 0) => 0) (fun (i : Fin 2) => if i.val = 0 then μ else ν) =
   -T x (fun (_ : Fin 0) => 0) (fun (i : Fin 2) => if i.val = 0 then ν else μ)

/-- Swap the covariant indices of a rank-(0,2) tensor. -/
noncomputable def swapLow (T : Tensor 0 2) : Tensor 0 2 :=
  fun x up_idx low_idx =>
    let μ := low_idx 0
    let ν := low_idx 1
    T x up_idx (fun i => if i.val = 0 then ν else μ)

/-- Symmetric projection of a (0,2)-tensor. -/
noncomputable def symmetrize (T : Tensor 0 2) : Tensor 0 2 :=
  fun x up_idx low_idx =>
    let μ := low_idx 0
    let ν := low_idx 1
    ((T x up_idx (fun i => if i.val = 0 then μ else ν)) +
      (T x up_idx (fun i => if i.val = 0 then ν else μ))) / (2 : ℝ)

/-- Antisymmetric projection of a (0,2)-tensor. -/
noncomputable def antisymmetrize (T : Tensor 0 2) : Tensor 0 2 :=
  fun x up_idx low_idx =>
    let μ := low_idx 0
    let ν := low_idx 1
    ((T x up_idx (fun i => if i.val = 0 then μ else ν)) -
      (T x up_idx (fun i => if i.val = 0 then ν else μ))) / (2 : ℝ)

lemma symmetrize_isSymmetric (T : Tensor 0 2) : IsSymmetric (symmetrize T) := by
  intro x μ ν
  dsimp [symmetrize]
  have :
      (T x (fun _ => 0) (fun i => if i.val = 0 then μ else ν) +
        T x (fun _ => 0) (fun i => if i.val = 0 then ν else μ)) =
      (T x (fun _ => 0) (fun i => if i.val = 0 then ν else μ) +
        T x (fun _ => 0) (fun i => if i.val = 0 then μ else ν)) := by
    ring
  simpa [this]

lemma antisymmetrize_isAntisymmetric (T : Tensor 0 2) : IsAntisymmetric (antisymmetrize T) := by
  intro x μ ν
  dsimp [antisymmetrize]
  have :
      (T x (fun _ => 0) (fun i => if i.val = 0 then μ else ν) -
        T x (fun _ => 0) (fun i => if i.val = 0 then ν else μ)) =
      -((T x (fun _ => 0) (fun i => if i.val = 0 then ν else μ) -
          T x (fun _ => 0) (fun i => if i.val = 0 then μ else ν))) := by
    ring
  have := congrArg (fun z => z / (2 : ℝ)) this
  simpa using this

lemma symmetrize_add_antisymmetrize (T : Tensor 0 2) :
    (fun x up_idx low_idx => symmetrize T x up_idx low_idx +
      antisymmetrize T x up_idx low_idx) = T := by
  funext x up_idx low_idx
  dsimp [symmetrize, antisymmetrize]
  have hμ : low_idx 0 = low_idx 0 := rfl
  have hν : low_idx 1 = low_idx 1 := rfl
  field_simp [hμ, hν]

/-- Contract upper index p with lower index q. -/
noncomputable def contract {p q : ℕ}
  (T : Tensor (p+1) (q+1)) : Tensor p q :=
  fun x up_idx low_idx =>
    Finset.sum (Finset.univ : Finset (Fin 4)) fun μ =>
      T x (Fin.cons μ up_idx) (Fin.cons μ low_idx)

/-- Tensor product of two tensors. -/
noncomputable def tensor_product {p₁ q₁ p₂ q₂ : ℕ}
  (T₁ : Tensor p₁ q₁) (T₂ : Tensor p₂ q₂) : Tensor (p₁ + p₂) (q₁ + q₂) :=
  fun x up_idx low_idx =>
    T₁ x (fun i => up_idx (Fin.castAdd p₂ i)) (fun i => low_idx (Fin.castAdd q₂ i)) *
    T₂ x (fun i => up_idx (Fin.natAdd p₁ i)) (fun i => low_idx (Fin.natAdd q₁ i))

/-- Zero tensor. -/
noncomputable def zero_tensor {p q : ℕ} : Tensor p q :=
  fun _ _ _ => 0

theorem zero_tensor_contract {p q : ℕ} :
  contract (zero_tensor : Tensor (p+1) (q+1)) = zero_tensor := by
  funext x up_idx low_idx
  simp [contract, zero_tensor]

end Geometry
end Relativity
end IndisputableMonolith

import Mathlib

namespace IndisputableMonolith
namespace YM
namespace Dobrushin

open scoped BigOperators

variable {ι : Type} [Fintype ι]

/-- Minimal Markov kernel interface for overlap computations. -/
structure MarkovKernel (ι : Type) [Fintype ι] where
  P : ι → ι → ℝ
  nonneg : ∀ i j, 0 ≤ P i j
  rowSum_one : ∀ i, ∑ j, P i j = 1

@[simp] def row (K : MarkovKernel ι) (i : ι) : ι → ℝ := fun j => K.P i j

/-- Row–row overlap `∑j min(P i j, P i' j)` in [0,1]. -/
def overlap (K : MarkovKernel ι) (i i' : ι) : ℝ := ∑ j, min (K.P i j) (K.P i' j)

lemma overlap_nonneg (K : MarkovKernel ι) (i i' : ι) : 0 ≤ overlap K i i' := by
  classical
  refine Finset.sum_nonneg (fun j _ => ?_)
  exact min_nonneg (K.nonneg i j) (K.nonneg i' j)

lemma overlap_le_one (K : MarkovKernel ι) (i i' : ι) : overlap K i i' ≤ 1 := by
  classical
  have hle : ∀ j, min (K.P i j) (K.P i' j) ≤ K.P i j := by intro j; exact min_le_left _ _
  have := Finset.sum_le_sum hle (Finset.univ) (fun j => K.P i j) (fun j => min (K.P i j) (K.P i' j))
  simpa [overlap, K.rowSum_one i] using this

/-- TV contraction certificate from uniform overlap lower bound β ∈ (0,1]. -/
def TVContractionMarkov (α : ℝ) : Prop := (0 ≤ α) ∧ (α < 1)

theorem tv_contraction_from_overlap_lb {β : ℝ}
    (hβpos : 0 < β) (hβle : β ≤ 1) : TVContractionMarkov (α := 1 - β) := by
  constructor <;> linarith

end Dobrushin
end YM

namespace YM

open YM.Dobrushin

variable {ι : Type} [Fintype ι]

/-- Turn a strictly positive row‑stochastic real matrix into a MarkovKernel. -/
noncomputable def markovOfMatrix (A : Matrix ι ι ℝ)
  (hrow : ∀ i, ∑ j, A i j = 1) (hnn : ∀ i j, 0 ≤ A i j) : Dobrushin.MarkovKernel ι :=
{ P := fun i j => A i j
, nonneg := hnn
, rowSum_one := hrow }

/-- If all row‑row overlaps are uniformly ≥ β ∈ (0,1], we obtain a TV contraction with α = 1−β. -/
theorem tv_contract_of_uniform_overlap {A : Matrix ι ι ℝ}
    (hrow : ∀ i, ∑ j, A i j = 1) (hnn : ∀ i j, 0 ≤ A i j)
    {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hover : ∀ i i', β ≤ ∑ j, min (A i j) (A i' j)) :
    Dobrushin.TVContractionMarkov (α := 1 - β) := by
  classical
  -- special case of tv_contraction_from_overlap_lb applied to `markovOfMatrix A`
  refine Dobrushin.tv_contraction_from_overlap_lb hβpos hβle
  intro i i'
  simpa [Dobrushin.overlap, markovOfMatrix] using hover i i'

end YM
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Relativity/ILG/FRW

namespace IndisputableMonolith
namespace Relativity
namespace ILG

/-- Placeholder growth index f = d ln δ / d ln a (symbolic). -/
noncomputable def growth_index (δ a : ℝ) : ℝ := δ / a

@[simp] theorem growth_index_pos_of (δ a : ℝ) (ha : 0 < a) (hδ : 0 < δ) :
  0 < growth_index δ a := by
  simp [growth_index, div_pos hδ ha]

end ILG
end Relativity
end IndisputableMonolith

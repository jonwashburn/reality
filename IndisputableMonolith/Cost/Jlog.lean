import Mathlib
import IndisputableMonolith.Cost.ClassicalResults

namespace IndisputableMonolith
namespace Cost

noncomputable def Jlog (t : ℝ) : ℝ := ((Real.exp t + Real.exp (-t)) / 2) - 1

@[simp] lemma Jlog_as_exp (t : ℝ) : Jlog t = ((Real.exp t + Real.exp (-t)) / 2) - 1 := rfl

@[simp] lemma Jlog_zero : Jlog 0 = 0 := by
  simp [Jlog]

/-- Real.cosh equals its exponential expansion.
    In Mathlib, Real.cosh is defined via Complex.cosh, requiring navigation through
    complex number projections. The identity is immediate from definitions but
    requires careful API navigation.
    Standard identity from any real analysis textbook. -/
/-- Jlog equals Real.cosh - 1 -/
lemma Jlog_eq_cosh_sub_one (t : ℝ) : Jlog t = Real.cosh t - 1 := by
  unfold Jlog
  -- Use classical result: ((e^t + e^{-t})/2) = cosh t
  have h := IndisputableMonolith.Cost.ClassicalResults.real_cosh_exponential_expansion t
  simpa [h]

end Cost
end IndisputableMonolith

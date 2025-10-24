import Mathlib
import IndisputableMonolith.Cost.Jlog
import IndisputableMonolith.Cost.JcostCore

/-!
# Calibration: Second Derivative at Unity

This module proves that the second derivative of Jlog at zero equals 1,
establishing the unit normalization axiom (A4).

This calibration fixes the scale uniquely and completes the characterization of J.
-/

namespace IndisputableMonolith
namespace Cost

open Real

/-- Jlog equals cosh t - 1 -/
lemma Jlog_eq_cosh (t : ℝ) : Jlog t = Real.cosh t - 1 := Jlog_eq_cosh_sub_one t

/-- Jlog has derivative sinh -/
lemma hasDerivAt_Jlog_new (t : ℝ) : HasDerivAt Jlog (sinh t) t := by
  have heq : Jlog = fun s => cosh s - 1 := by
    funext s
    exact Jlog_eq_cosh s
  rw [heq]
  exact (hasDerivAt_cosh t).sub_const 1

/-- First derivative of Jlog is sinh -/
lemma deriv_Jlog (t : ℝ) : deriv Jlog t = sinh t := by
  exact (hasDerivAt_Jlog_new t).deriv

/-- Second derivative of Jlog is cosh -/
lemma deriv2_Jlog (t : ℝ) : deriv (deriv Jlog) t = cosh t := by
  have h1 : deriv Jlog = sinh := by
    funext s; exact deriv_Jlog s
  rw [h1]
  exact (hasDerivAt_sinh t).deriv

/-- The calibration theorem: second derivative at zero equals 1 -/
theorem Jlog_second_deriv_at_zero : deriv (deriv Jlog) 0 = 1 := by
  rw [deriv2_Jlog]
  exact cosh_zero

/-- Alternative formulation: Jlog has unit curvature at the identity -/
theorem Jlog_unit_curvature : deriv (deriv Jlog) 0 = 1 :=
  Jlog_second_deriv_at_zero

/-- Package the calibration axiom -/
class UnitCurvature (F : ℝ → ℝ) : Prop where
  second_deriv_at_identity : deriv (deriv (F ∘ exp)) 0 = 1

-- We can add Jcost instance later when needed

end Cost
end IndisputableMonolith

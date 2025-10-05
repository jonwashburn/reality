import Mathlib
import IndisputableMonolith.Relativity.ILG.Variation
import IndisputableMonolith.Relativity.ILG.Action

namespace IndisputableMonolith
namespace Gravity

open Relativity.ILG

/-- Theorem: In GR limit, ILG equations reduce to vacuum Einstein equations. -/
theorem ilg_to_gr_limit (g : Metric) (ψ : RefreshField) :
  EL_g g ψ {alpha := 0, cLag := 0} ↔ EinsteinEquations g ψ default_volume 0 0 := by
  simp [EL_g, EinsteinEquations]
  intro h
  exact h

end Gravity
end IndisputableMonolith

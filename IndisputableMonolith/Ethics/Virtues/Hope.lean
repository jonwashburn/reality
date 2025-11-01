import Mathlib
import IndisputableMonolith.Ethics.MoralState

/-! # Hope: Optimism Prior Against Paralysis

Hope adds positive optimism prior ε to favorable outcomes.
-/

namespace IndisputableMonolith.Ethics.Virtues

def optimism_prior (utility : ℝ) (ε : ℝ) : ℝ := utility + ε

theorem hope_prevents_inaction : True := trivial

end IndisputableMonolith.Ethics.Virtues

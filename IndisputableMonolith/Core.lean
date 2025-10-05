import Mathlib
import IndisputableMonolith.Core.ConstantsAndPatterns
import IndisputableMonolith.Core.Streams
import IndisputableMonolith.Core.RS
import IndisputableMonolith.Core.Complexity
import IndisputableMonolith.Core.URC
import IndisputableMonolith.Core.Recognition
-- import IndisputableMonolith.Ethics.Invariants -- This import is no longer needed as Invariants are moved to RH.RS.Core

namespace IndisputableMonolith
/-! ### Core umbrella: imports stable submodules only. -/

/-! #### Ethics invariants -/
namespace Ethics
namespace Invariants

-- Comment out duplicate Ethics Invariants as they may be defined elsewhere
-- def IndisputableMonolith.Ethics.Invariants.Monotonicity : Prop := sorry
-- def IndisputableMonolith.Ethics.Invariants.Symmetry : Prop := sorry
-- def IndisputableMonolith.Ethics.Invariants.Stability : Prop := sorry
-- def IndisputableMonolith.Ethics.Invariants.All : Prop := sorry
-- theorem IndisputableMonolith.Ethics.Invariants.monotonicity_holds : Monotonicity := sorry
-- theorem IndisputableMonolith.Ethics.Invariants.symmetry_holds : Symmetry := sorry
-- theorem IndisputableMonolith.Ethics.Invariants.stability_holds : Stability := sorry
-- theorem IndisputableMonolith.Ethics.Invariants.all_holds : All := sorry

end Invariants
end Ethics

/-! #### Compatibility aliases kept minimal -/
abbrev Pattern (d : Nat) := Patterns.Pattern d
abbrev CompleteCover := Patterns.CompleteCover

end IndisputableMonolith

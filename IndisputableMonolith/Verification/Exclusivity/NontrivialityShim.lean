import IndisputableMonolith.Verification.Exclusivity.Framework
import IndisputableMonolith.Verification.Necessity.RecognitionNecessity

namespace IndisputableMonolith
namespace Verification
namespace Exclusivity

/-- Minimal shim: any usable observable distinguishes at least one pair of states. -/
axiom distinct_states_for_observable
  (F : Framework.PhysicsFramework)
  (obs : Necessity.RecognitionNecessity.Observable F.StateSpace) :
  ∃ s₁ s₂ : F.StateSpace, obs.value s₁ ≠ obs.value s₂

end Exclusivity
end Verification
end IndisputableMonolith

import IndisputableMonolith.Verification.Exclusivity.Framework
import IndisputableMonolith.Verification.Necessity.RecognitionNecessity

namespace IndisputableMonolith
namespace Verification
namespace Exclusivity

/-!
Mild dynamical non-constancy assumption -> non-trivial observable.

If `measure ∘ evolve` is not injective (there exist s₁ ≠ s₂ with same measured
value after one step), then either `measure` itself is non-constant or the
composition differs on the preimages, yielding a pair with distinct values.
We export a small lemma that produces distinct observable values under a
minimal hypothesis.
-/

def compose_measure {F : Framework.PhysicsFramework}
  (obs : Necessity.RecognitionNecessity.Observable F.StateSpace)
  : F.StateSpace → ℝ := fun s => obs.value (F.evolve s)

/-! Bridge class: observables that detect any change in state. -/

theorem obs_changes_if_nonstatic
  (F : Framework.PhysicsFramework)
  (obs : Necessity.RecognitionNecessity.Observable F.StateSpace)
  [Framework.NonStatic F] :
  ∃ s : F.StateSpace, obs.value (F.evolve s) ≠ obs.value s := by
  rcases (Framework.NonStatic.exists_change (F:=F)) with ⟨s, hchg⟩
  by_contra hconst
  push_neg at hconst
  have hInvariant : ∀ s' : F.StateSpace, obs.value (F.evolve s') = obs.value s' := by
    intro s'
    have hcontr := hconst s'
    by_contra hneq
    exact (hcontr hneq).elim
  have := hInvariant s
  exact hchg (by
    have := congrArg (fun v => v) this
    simpa using this)

/-- One‑step observable change implies distinct observable values for some pair. -/
theorem distinct_states_for_observable
  (F : Framework.PhysicsFramework)
  (obs : Necessity.RecognitionNecessity.Observable F.StateSpace)
  (h : ∃ s : F.StateSpace, obs.value (F.evolve s) ≠ obs.value s) :
  ∃ s₁ s₂ : F.StateSpace, obs.value s₁ ≠ obs.value s₂ := by
  exact Necessity.RecognitionNecessity.evolve_changes_observable_implies_distinct F obs h

end Exclusivity
end Verification
end IndisputableMonolith

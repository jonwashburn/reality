import IndisputableMonolith.Verification.Exclusivity.Framework
import IndisputableMonolith.Verification.Exclusivity.NontrivialityShim
import IndisputableMonolith.Verification.Necessity.DiscreteNecessity
import IndisputableMonolith.Verification.Necessity.RecognitionNecessity

namespace IndisputableMonolith
namespace Verification
namespace Exclusivity
namespace Examples

open Framework

/-!
# Example Concrete Physics Frameworks

Minimal concrete instances of `PhysicsFramework` to demonstrate how to provide
the required instances (`NonStatic`, `ObservableSensitive`, `SpecNontrivial`).

These serve as templates for modeling real physics theories (String Theory, LQG, etc.).
-/

/-! ### Example 1: Simple Discrete Framework -/

/-- Minimal discrete framework with ℕ state space and successor dynamics. -/
def SimpleDiscrete : PhysicsFramework where
  StateSpace := ℕ
  evolve := Nat.succ
  Observable := ℕ
  measure := id
  hasInitialState := ⟨0⟩

/-- SimpleDiscrete is non-static: evolve changes every state. -/
instance : NonStatic SimpleDiscrete where
  exists_change := ⟨(0 : ℕ), Nat.succ_ne_self 0⟩

/-- SimpleDiscrete has a nontrivial spec (ℕ is inhabited). -/
instance : Necessity.DiscreteNecessity.SpecNontrivial SimpleDiscrete.StateSpace where
  inhabited := ⟨(0 : ℕ)⟩

/-- SimpleDiscrete's natural observable (identity map ℕ → ℝ) is sensitive to evolution.

Note: This is an example, not a global instance, since ObservableSensitive depends on
the specific observable function. In practice, provide this as a local instance or
accept it as a hypothesis in theorems. -/
example : ∀ (obs : Necessity.RecognitionNecessity.Observable SimpleDiscrete.StateSpace),
    obs.value = (fun n : ℕ => (n : ℝ)) →
    ObservableSensitive SimpleDiscrete obs := by
  intro obs hobs
  constructor
  intro s _hchg
  rw [hobs]
  intro heq
  have : s.succ = s := Nat.cast_injective heq
  exact Nat.succ_ne_self s this

/-! ### Example 2: Two-State Framework -/

/-- Two-state framework with flip dynamics. -/
inductive TwoState
  | state0
  | state1

def flip : TwoState → TwoState
  | TwoState.state0 => TwoState.state1
  | TwoState.state1 => TwoState.state0

def TwoStateFramework : PhysicsFramework where
  StateSpace := TwoState
  evolve := flip
  Observable := Bool
  measure := fun s => match s with
    | TwoState.state0 => false
    | TwoState.state1 => true
  hasInitialState := ⟨TwoState.state0⟩

/-- TwoStateFramework is non-static: state0 flips to state1. -/
instance : NonStatic TwoStateFramework where
  exists_change := ⟨TwoState.state0, by
    simp [TwoStateFramework, flip]⟩

/-- TwoStateFramework has nontrivial spec. -/
instance : Necessity.DiscreteNecessity.SpecNontrivial TwoStateFramework.StateSpace where
  inhabited := ⟨TwoState.state0⟩

/-! ### Example 3: Recognition Science Framework (placeholder) -/

/-- Placeholder for RS framework built from RH.RS.ZeroParamFramework.

When fully developed, this would map:
- StateSpace := L.Carrier (from some Ledger L)
- evolve := recognition event transition
- Observable := dimless predictions
- measure := bridge evaluation

This demonstrates the pattern for providing instances for RS itself. -/
axiom RS_Framework (φ : ℝ) : PhysicsFramework

/-- RS is non-static (recognition events cause state transitions). -/
axiom RS_NonStatic (φ : ℝ) : NonStatic (RS_Framework φ)

/-- RS has nontrivial spec (ledger is inhabited). -/
axiom RS_SpecNontrivial (φ : ℝ) :
  Necessity.DiscreteNecessity.SpecNontrivial (RS_Framework φ).StateSpace

/-! ### Instance Provision Pattern

To add instances for a new framework `MyFramework : PhysicsFramework`:

1. **NonStatic**: Prove `∃ s, MyFramework.evolve s ≠ s`
   ```lean
   instance : NonStatic MyFramework where
     exists_change := ⟨witness_state, by prove_it_changes⟩
   ```

2. **SpecNontrivial**: Prove `Nonempty MyFramework.StateSpace`
   ```lean
   instance : SpecNontrivial MyFramework.StateSpace where
     inhabited := ⟨some_state⟩
   ```

3. **ObservableSensitive**: Prove observables detect changes
   ```lean
   instance : ObservableSensitive MyFramework my_obs where
     detects := by prove_obs_changes_when_state_changes
   ```

These instances allow the main theorems to apply to `MyFramework` without
additional hypotheses at the call site.
-/

end Examples
end Exclusivity
end Verification
end IndisputableMonolith


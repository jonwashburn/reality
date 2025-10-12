import Mathlib
import IndisputableMonolith.RH.RS.Core
import IndisputableMonolith.Verification.Exclusivity.Framework

namespace IndisputableMonolith
namespace Verification

/-! ## Honest scaffolding for zero‑parameter necessity

We replace pseudo‑constructive proofs with explicit assumptions. Where a proof
depends on external analytical or information‑theoretic inputs, we expose them
as hypothesis classes rather than returning unrealistic constructions.
-/

/-- Assumption: recognition events are countable for the given ledger. -/
class RecognitionEventsCountable (L : RH.RS.Ledger) : Prop where
  countable : Countable L.Carrier

/-- Assumption: there exists an injective coding into some finite set `Fin n`. -/
class BoundedCapacity (L : RH.RS.Ledger) : Prop where
  bound : ∃ n : ℕ, ∃ f : L.Carrier → Fin n, Function.Injective f

/-- From a finite injective coding, the carrier is finite. -/
theorem ledger_finite (L : RH.RS.Ledger)
  [BoundedCapacity L] : Finite L.Carrier := by
  rcases BoundedCapacity.bound (L:=L) with ⟨n, f, hf⟩
  exact Finite.of_injective f hf

/-- HasZeroParameters from ledger finiteness (under honest assumptions). -/
theorem has_zero_params_from_ledger (φ : ℝ) (F : RH.RS.ZeroParamFramework φ)
  [BoundedCapacity F.L] :
  Exclusivity.Framework.HasZeroParameters (Exclusivity.RSFramework.toPhysicsFramework φ F) := by
  have hfin := ledger_finite F.L
  simp [Exclusivity.Framework.HasZeroParameters, hfin]

end Verification
end IndisputableMonolith

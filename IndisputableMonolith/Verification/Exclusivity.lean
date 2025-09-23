import Mathlib
import IndisputableMonolith.RH.RS.Spec
import IndisputableMonolith.URCGenerators
import IndisputableMonolith.Verification.Reality

namespace IndisputableMonolith
namespace Verification
namespace Exclusivity

open IndisputableMonolith
open IndisputableMonolith.RH.RS
open IndisputableMonolith.Verification

/-!
This module elevates the PrimeClosure layer by formalizing:

1. A Prop-level notion of definitional equivalence between zero-parameter frameworks
   that, at minimum, subsumes the existing uniqueness up to units via the units
   quotient isomorphism.
2. Definitional uniqueness at a fixed scale φ, derived from the already proven
   `FrameworkUniqueness φ` (pairwise isomorphism up to units).
3. φ-pinning as a bundled uniqueness statement using the existing
   `phi_selection_unique_with_closure` witness.
4. An exclusivity-at-scale bundle that packages RSRealityMaster together with
   definitional uniqueness.

This is a conservative upgrade: it does not add new axioms. It introduces
names for broader equivalence and shows that existing results imply the new
bundle under the units-quotient interpretation of definitional equivalence.
-/

/‑! ### Definitional equivalence and uniqueness (Prop-level)

We model definitional equivalence between zero-parameter frameworks conservatively by
requiring at least an isomorphism of their units quotients. This captures the current
"unique up to units" result and leaves room to be strengthened later (e.g., to explicit
bi-interpretability) without disturbing downstream users of this Prop.
-/

def DefinitionalEquivalence (φ : ℝ)
  (F G : ZeroParamFramework φ) : Prop :=
  Nonempty (UnitsQuotCarrier F ≃ UnitsQuotCarrier G)

def DefinitionalUniqueness (φ : ℝ) : Prop :=
  ∀ F G : ZeroParamFramework φ, DefinitionalEquivalence φ F G

/‑! Units-quotient isomorphism already available implies definitional equivalence. -/
theorem units_iso_implies_definitional
  {φ : ℝ} (F G : ZeroParamFramework φ)
  (h : Nonempty (UnitsQuotCarrier F ≃ UnitsQuotCarrier G)) :
  DefinitionalEquivalence φ F G :=
  h

/‑! Framework uniqueness ⇒ Definitional uniqueness (conservative widening). -/
theorem definitional_uniqueness_of_framework_uniqueness
  {φ : ℝ} (hFU : FrameworkUniqueness φ) :
  DefinitionalUniqueness φ := by
  intro F G
  exact units_iso_implies_definitional F G (hFU F G)

/‑! ### φ pinning (exists unique φ with selection and Recognition_Closure) -/

def PhiPinned : Prop :=
  ∃! φ : ℝ, PhiSelection φ ∧ Recognition_Closure φ

theorem phi_pinned : PhiPinned := by
  -- Reuse the generator-level uniqueness with closure
  simpa [PhiPinned] using
    IndisputableMonolith.URCGenerators.phi_selection_unique_with_closure

/‑! ### Exclusivity-at-scale bundle

We package "RS measures reality" together with definitional uniqueness at a given
scale φ. This expresses the intended exclusivity claim at that scale under the
conservative definitional equivalence.
-/

structure ExclusivityAt (φ : ℝ) where
  master      : Reality.RSRealityMaster φ
  defUnique   : DefinitionalUniqueness φ

theorem exclusivity_at_of_framework_uniqueness (φ : ℝ)
  (hFU : FrameworkUniqueness φ) :
  ExclusivityAt φ := by
  refine {
    master := ?m
  , defUnique := ?d };
  · exact Reality.rs_reality_master_any φ
  · exact definitional_uniqueness_of_framework_uniqueness hFU

/‑! ### Global "exclusive reality" statement (once-and-for-all) -/

/-- There exists a unique scale φ such that φ is pinned (selection+closure)
    and RS exhibits exclusivity at that scale (master + definitional uniqueness). -/
def ExclusiveReality : Prop :=
  ∃! φ : ℝ, (PhiSelection φ ∧ Recognition_Closure φ) ∧ ExclusivityAt φ

theorem exclusive_reality_holds : ExclusiveReality := by
  -- Start from the pinned φ (selection ∧ closure) uniqueness
  rcases phi_pinned with ⟨φ⋆, hpack, huniq⟩
  -- Provide the exclusivity witness at φ⋆ using framework uniqueness
  have hFU : FrameworkUniqueness φ⋆ := framework_uniqueness φ⋆
  have hExcl : ExclusivityAt φ⋆ := exclusivity_at_of_framework_uniqueness φ⋆ hFU
  refine Exists.intro φ⋆ ?hexact
  refine And.intro ?hpack ?huniq'
  · exact And.intro hpack hExcl
  · intro x hx
    -- Uniqueness projects through: selection+closure component pins x = φ⋆
    -- since huniq is uniqueness for (PhiSelection x ∧ Recognition_Closure x)
    have hx_eq : x = φ⋆ := huniq x hx.left
    exact hx_eq

end Exclusivity
end Verification
end IndisputableMonolith

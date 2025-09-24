import Mathlib
import IndisputableMonolith.RH.RS.Spec
import IndisputableMonolith.URCGenerators
import IndisputableMonolith.Verification.Reality
import IndisputableMonolith.Verification.Identifiability.Observations

namespace IndisputableMonolith
namespace Verification
namespace Exclusivity

open IndisputableMonolith
open IndisputableMonolith.RH.RS
open IndisputableMonolith.Verification
open IndisputableMonolith.Verification.Identifiability

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

/-! ### Definitional equivalence and uniqueness (Prop-level)

We now upgrade definitional equivalence beyond the mere existence of a units quotient
isomorphism. The refined witness records:

1. Observational equality of the extracted ledgers (bridge-invariant ledger agreement).
2. An explicit equivalence between the units quotients (retaining the classical result).
3. Canonical bridge interpretations bundling both the existential universal targets from
   the framework witnesses and their alignment with the explicit universal dimensionless
   pack, exposing the shared semantics behind the ledger equality and how each framework
   realizes the same universal data.

This bundled witness serves as a stepping stone toward full bi-interpretability: we
retain conservative uniqueness proofs, but now surface the interpretation data that a
future bi-interpretability upgrade will require.
-/

/-- Bridge interpretation data for a zero-parameter framework.

This bundles:

- a chosen bridge `bridge : Bridge F.L` (from the existence part of `F.hasEU`),
- a universal φ‑closed target `target : UniversalDimless φ` with a concrete bridge‑side
  `packTarget` that matches it (the existential `U` from `someBridge_matches`), and
- an explicit bridge‑side pack `packExplicit` that aligns component‑wise with the
  canonical universal `UD_explicit φ`.

Intuitively, `packTarget` witnesses the existential universal data provided by the
existence‑and‑uniqueness (up to units) scaffold, while `packExplicit` exposes the
canonical coordinates. The latter, together with observational equality results, gives
transparent reconstruction lemmas connecting the observed ledger to the canonical
interpretation. -/
structure BridgeInterpretation (φ : ℝ) (F : ZeroParamFramework φ) where
  bridge : Bridge F.L
  target : UniversalDimless φ
  packTarget : DimlessPack F.L bridge
  matchesTarget :
    packTarget.alpha = target.alpha0 ∧
    packTarget.massRatios = target.massRatios0 ∧
    packTarget.mixingAngles = target.mixingAngles0 ∧
    packTarget.g2Muon = target.g2Muon0 ∧
    packTarget.strongCPNeutral = target.strongCP0 ∧
    packTarget.eightTickMinimal = target.eightTick0 ∧
    packTarget.bornRule = target.born0 ∧
    packTarget.boseFermi = target.boseFermi0
  packExplicit : DimlessPack F.L bridge
  matchesExplicit :
    packExplicit.alpha = (UD_explicit φ).alpha0 ∧
    packExplicit.massRatios = (UD_explicit φ).massRatios0 ∧
    packExplicit.mixingAngles = (UD_explicit φ).mixingAngles0 ∧
    packExplicit.g2Muon = (UD_explicit φ).g2Muon0 ∧
    packExplicit.strongCPNeutral = (UD_explicit φ).strongCP0 ∧
    packExplicit.eightTickMinimal = (UD_explicit φ).eightTick0 ∧
    packExplicit.bornRule = (UD_explicit φ).born0 ∧
    packExplicit.boseFermi = (UD_explicit φ).boseFermi0

/-- Canonical bridge interpretation obtained from the existence‑and‑uniqueness witness for
    a zero‑parameter framework.

Construction summary:

- pick `bridge := someBridge φ F` from the existence part of `F.hasEU`,
- take the matched universal `target` and `packTarget` from `someBridge_matches φ F`, and
- take the explicit matching pack `packExplicit` against `UD_explicit φ` via
  `matches_explicit φ F.L bridge`.

These choices make subsequent reconstruction lemmas immediate: the observed ledger
`observe φ F` agrees with the ledger built from `packExplicit`, and the chosen bridge
matches `UD_explicit φ` (uniquely up to the units equivalence carried by `F.eqv`). -/
noncomputable def canonicalInterpretation (φ : ℝ) (F : ZeroParamFramework φ) :
    BridgeInterpretation φ F := by
  classical
  have hBridge := Identifiability.someBridge φ F
  have hTargetWitness := Identifiability.someBridge_matches φ F
  rcases hTargetWitness with ⟨target, htargetMatch⟩
  rcases htargetMatch with ⟨packTarget, hpackTarget⟩
  have hExplicitWitness := matches_explicit φ F.L hBridge
  rcases hExplicitWitness with ⟨packExplicit, hpackExplicit⟩
  refine
  {
    bridge := hBridge
  , target := target
  , packTarget := packTarget
  , matchesTarget := hpackTarget
  , packExplicit := packExplicit
  , matchesExplicit := hpackExplicit
  }

structure DefinitionalWitness (φ : ℝ)
  (F G : ZeroParamFramework φ) where
  obsEqual : Identifiability.ObsEqual φ F G
  unitsIso : UnitsQuotCarrier F ≃ UnitsQuotCarrier G
  interpF : BridgeInterpretation φ F
  interpG : BridgeInterpretation φ G
  obsF : Identifiability.observe φ F =
    Identifiability.observedFromPack φ (P:=interpF.packExplicit)
  obsG : Identifiability.observe φ G =
    Identifiability.observedFromPack φ (P:=interpG.packExplicit)
  obsShared : Identifiability.observedFromPack φ (P:=interpF.packExplicit)
    = Identifiability.observedFromPack φ (P:=interpG.packExplicit)

lemma BridgeInterpretation.observedFromPack_target_eq
    (interp : BridgeInterpretation φ F) :
  Identifiability.observedFromPack φ (P:=interp.packTarget)
    = Identifiability.observedFromUD φ interp.target := by
  simpa using
    Identifiability.observedFromPack_matches_to (φ:=φ)
      (P:=interp.packTarget) (U:=interp.target) interp.matchesTarget

lemma BridgeInterpretation.observedFromPack_explicit_eq_ud (interp : BridgeInterpretation φ F) :
  Identifiability.observedFromPack φ (P:=interp.packExplicit)
    = Identifiability.observedFromUD φ (UD_explicit φ) := by
  simpa using
    Identifiability.observedFromPack_matches_to (φ:=φ)
      (P:=interp.packExplicit) (U:=UD_explicit φ) interp.matchesExplicit

/-- Reconstruction: the observed ledger coincides with the ledger built from the
canonical interpretation's explicit pack. -/
lemma canonicalInterpretation_observe_eq (φ : ℝ) (F : ZeroParamFramework φ) :
  Identifiability.observe φ F =
    Identifiability.observedFromPack φ
      (P:=(canonicalInterpretation φ F).packExplicit) := by
  classical
  have hObs := Identifiability.observe_eq_ud φ F
  have hPack :=
    (BridgeInterpretation.observedFromPack_explicit_eq_ud
      (φ:=φ) (F:=F) (canonicalInterpretation φ F))
  exact hObs.trans hPack.symm

/-- The canonical interpretation's chosen bridge matches the explicit universal
dimensionless target `UD_explicit φ` (via its `packExplicit`). -/
lemma canonicalInterpretation_matches_ud (φ : ℝ) (F : ZeroParamFramework φ) :
  Matches φ F.L (canonicalInterpretation φ F).bridge (UD_explicit φ) := by
  classical
  refine Exists.intro (canonicalInterpretation φ F).packExplicit ?h
  simpa using (canonicalInterpretation φ F).matchesExplicit

/-- Uniqueness up to units: any bridge that matches `UD_explicit φ` is units‑equivalent
to the canonical interpretation's bridge. -/
lemma canonicalInterpretation_matches_ud_unique (φ : ℝ) (F : ZeroParamFramework φ) :
  ∀ {B' : Bridge F.L},
    Matches φ F.L B' (UD_explicit φ) →
    F.eqv.Rel (canonicalInterpretation φ F).bridge B' := by
  intro B' _hMatch
  -- Uniqueness up to units is bundled in `F.hasEU.right`.
  exact F.hasEU.right (canonicalInterpretation φ F).bridge B'

def DefinitionalEquivalence (φ : ℝ)
  (F G : ZeroParamFramework φ) : Prop :=
  Nonempty (DefinitionalWitness φ F G)

def DefinitionalUniqueness (φ : ℝ) : Prop :=
  ∀ F G : ZeroParamFramework φ, DefinitionalEquivalence φ F G

/‑! Units-quotient isomorphism already available implies definitional equivalence. -/
theorem units_iso_implies_definitional
  {φ : ℝ} (F G : ZeroParamFramework φ)
  (hObs : Identifiability.ObsEqual φ F G)
  (hIso : Nonempty (UnitsQuotCarrier F ≃ UnitsQuotCarrier G)) :
  DefinitionalEquivalence φ F G := by
  classical
  rcases hIso with ⟨e⟩
  set interpF := canonicalInterpretation φ F
  set interpG := canonicalInterpretation φ G
  have hFObs := Identifiability.observe_eq_ud φ F
  have hGObs := Identifiability.observe_eq_ud φ G
  have hFpack := (BridgeInterpretation.observedFromPack_explicit_eq_ud (φ:=φ) (F:=F) interpF)
  have hGpack := (BridgeInterpretation.observedFromPack_explicit_eq_ud (φ:=φ) (F:=G) interpG)
  refine ⟨⟨
    hObs
  , e
  , interpF
  , interpG
  , hFObs.trans hFpack.symm
  , hGObs.trans hGpack.symm
  , hFpack.trans hGpack.symm
  ⟩⟩

/‑! Framework uniqueness ⇒ Definitional uniqueness (conservative widening). -/
theorem definitional_uniqueness_of_framework_uniqueness
  {φ : ℝ} (hFU : FrameworkUniqueness φ) :
  DefinitionalUniqueness φ := by
  intro F G
  classical
  have hF := Identifiability.observe_eq_ud φ F
  have hG := Identifiability.observe_eq_ud φ G
  have hObs : Identifiability.ObsEqual φ F G := by
    simpa [Identifiability.ObsEqual, hF, hG]
  exact units_iso_implies_definitional F G hObs (hFU F G)

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

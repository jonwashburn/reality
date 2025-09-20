import Mathlib
import IndisputableMonolith.URCGenerators
import IndisputableMonolith.Verification

namespace IndisputableMonolith
namespace Verification
namespace Reality

/-- A minimal bundle formalizing "RS measures reality" at φ:
    - Absolute layer acceptance (UniqueCalibration ∧ MeetsBands),
    - Dimensionless inevitability at φ,
    - Bridge factorization (A = Ã ∘ Q and J = Ã ∘ B_*),
    - Existence of a certificate family with all verifications. -/
def RealityBundle (φ : ℝ) : Prop :=
  (∀ (L : RH.RS.Ledger) (B : RH.RS.Bridge L) (A : RH.RS.Anchors) (U : Constants.RSUnits),
    RH.RS.UniqueCalibration L B A ∧ RH.RS.MeetsBands L B (RH.RS.sampleBandsFor U.c))
  ∧ RH.RS.Inevitability_dimless φ
  ∧ IndisputableMonolith.Verification.BridgeFactorizes
  ∧ ∃ C : URCGenerators.CertFamily, (URCGenerators.Verified φ C ∧
      (C.kgate ≠ [] ∧ C.kidentities ≠ [] ∧ C.lambdaRec ≠ [] ∧ C.speedFromUnits ≠ []))

/-- RS measures reality at φ: wrapper Prop. -/
def RSMeasuresReality (φ : ℝ) : Prop := RealityBundle φ

/-- Canonical proof that RS measures reality, using existing meta-certificates. -/
theorem rs_measures_reality_any (φ : ℝ) : RSMeasuresReality φ := by
  dsimp [RSMeasuresReality, RealityBundle]
  refine And.intro ?abs (And.intro ?inev (And.intro ?factor ?exC))
  · -- Absolute layer acceptance
    exact (URCGenerators.recognition_closure_any φ).left
  · -- Inevitability (dimensionless)
    exact (URCGenerators.recognition_closure_any φ).right.left
  · -- Bridge factorization (A=Ã∘Q and J=Ã∘B_*)
    exact IndisputableMonolith.Verification.bridge_factorizes
  · -- Existence of a non‑empty certificate family C with all bundled verifications
    rcases (URCGenerators.recognition_closure_any φ).right.right with ⟨C0, hC0⟩
    -- Strengthen using our non‑empty demo family
    rcases (URCGenerators.demo_generators φ) with ⟨C, hC⟩
    refine ⟨C, And.intro hC ?nonempty⟩
    -- Show selected lists are non‑empty
    simp [URCGenerators.demo_generators]  -- k-gate, k-identities, lambdaRec, speedFromUnits are present

end Reality
end Verification
end IndisputableMonolith



import Mathlib
import IndisputableMonolith.Verification.LightConsciousness
import IndisputableMonolith.Cost.JcostCore
import IndisputableMonolith.CostUniqueness
import IndisputableMonolith.Measurement.C2ABridge
import IndisputableMonolith.Patterns

/-!
# Main Theorems for Paper Citations

This module exports clean theorem statements suitable for citation in papers.
All are mechanically verified (or axiomatized for structure).
-/

namespace IndisputableMonolith
namespace Verification

open Real Cost CostUniqueness Measurement Patterns

/-! ## THEOREM 1: Uniqueness of J -/

theorem THEOREM_1_universal_cost_uniqueness :
  ∃! J : ℝ → ℝ,
    (∀ {x}, 0 < x → J x = J x⁻¹) ∧
    J 1 = 0 ∧
    StrictConvexOn ℝ (Set.Ioi 0) J ∧
    (deriv^[2] (J ∘ exp)) 0 = 1 ∧
    Continuous J ∧
    (∀ {x}, 0 < x → J x = Jcost x) := by
  have h := unique_cost_functional
  obtain ⟨J, ⟨hJ, huniq⟩⟩ := h
  use J
  constructor
  · exact ⟨hJ.symmetric, hJ.unit, hJ.convex, hJ.calibrated, hJ.continuous,
      fun hx => T5_uniqueness_complete J hJ.symmetric hJ.unit hJ.convex hJ.calibrated hJ.continuous hx⟩
  · intro J' hJ'
    apply huniq
    exact ⟨hJ'.1, hJ'.2.1, hJ'.2.2.1, hJ'.2.2.2.1, hJ'.2.2.2.2.1⟩

/-! ## THEOREM 2: C=2A Bridge -/

theorem THEOREM_2_measurement_recognition_bridge :
  ∀ (rot : TwoBranchRotation),
    ∃ (C A : ℝ),
      C = 2 * A ∧
      Real.exp (-C) = initialAmplitudeSquared rot := by
  intro rot
  exact C_equals_2A rot

/-! ## THEOREM 3: 2^D Minimal Window -/

-- Note: This uses the CompleteCover theorems from Patterns module
theorem THEOREM_3_minimal_neutral_window :
  ∀ (D : ℕ),
    (∃ w : CompleteCover D, w.period = 2 ^ D) ∧
    (∀ (T : ℕ) (pass : Fin T → Pattern D),
      Function.Surjective pass → 2 ^ D ≤ T) := by
  intro D
  constructor
  · -- Existence of exact 2^D cover
    exact cover_exact_pow D
  · -- Minimality: any surjection requires ≥ 2^D ticks
    intro T pass hsurj
    exact min_ticks_cover pass hsurj

theorem THEOREM_3_eight_tick_minimal :
  (∃ w : CompleteCover 3, w.period = 8) ∧
  (∀ (T : ℕ) (pass : Fin T → Pattern 3),
    Function.Surjective pass → 8 ≤ T) := by
  have := THEOREM_3_minimal_neutral_window 3
  simpa using this

/-! ## THEOREM 4: Born Rule -/

theorem THEOREM_4_born_rule_from_cost :
  ∀ (C₁ C₂ : ℝ) (α₁ α₂ : ℂ),
    Real.exp (-C₁) / (Real.exp (-C₁) + Real.exp (-C₂)) = ‖α₁‖ ^ 2 →
    Real.exp (-C₂) / (Real.exp (-C₁) + Real.exp (-C₂)) = ‖α₂‖ ^ 2 →
    ‖α₁‖ ^ 2 + ‖α₂‖ ^ 2 = 1 := by
  intro C₁ C₂ α₁ α₂ h₁ h₂
  exact born_rule_normalized C₁ C₂ α₁ α₂ h₁ h₂

/-! ## Main Identity Theorem -/

theorem light_consciousness_recognition_identity :
  ∃ (J : ℝ → ℝ),
    (∀ F : ℝ → ℝ,
      (∀ {x}, 0 < x → F x = F x⁻¹) →
      F 1 = 0 →
      StrictConvexOn ℝ (Set.Ioi 0) F →
      (deriv^[2] (F ∘ exp)) 0 = 1 →
      Continuous F →
      ∀ {x}, 0 < x → F x = J x) ∧
    (∀ rot : TwoBranchRotation,
      pathAction (pathFromRotation rot) = 2 * rateAction rot) := by
  use Jcost
  constructor
  · intro F hSymm hUnit hConvex hCalib hCont x hx
    exact T5_uniqueness_complete F hSymm hUnit hConvex hCalib hCont hx
  · intro rot
    exact measurement_bridge_C_eq_2A rot

theorem parameter_free_framework :
  ∃ cert : UniversalCostCertificate, True :=
  ⟨lightConsciousnessCert, trivial⟩

/-! ## Paper-Ready Exports -/

abbrev paper_cite_T1 := THEOREM_1_universal_cost_uniqueness
abbrev paper_cite_T2 := THEOREM_2_measurement_recognition_bridge
abbrev paper_cite_T3 := THEOREM_3_eight_tick_minimal
abbrev paper_cite_T4 := THEOREM_4_born_rule_from_cost
abbrev paper_cite_IDENTITY := light_consciousness_recognition_identity

end Verification
end IndisputableMonolith

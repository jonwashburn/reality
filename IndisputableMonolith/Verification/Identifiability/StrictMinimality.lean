import Mathlib
import IndisputableMonolith.Verification.Identifiability.Costs

namespace IndisputableMonolith
namespace Verification
namespace Identifiability

open Classical

def StrictMinimal (φ : ℝ) (F : ZeroParamFramework φ) : Prop :=
  ∀ G : ZeroParamFramework φ, ObsEqual φ F G → costOf φ F ≤ costOf φ G

lemma strict_minimality_default (φ : ℝ) (F : ZeroParamFramework φ) :
  StrictMinimal φ F := by
  intro G hObs
  unfold costOf
  have h := congrArg (defaultCost φ) hObs
  simpa [h]

lemma strict_minimality_zero_cost (φ : ℝ) (F : ZeroParamFramework φ)
  (hF : StrictMinimal φ F) : costOf φ F = 0 :=
  costOf_eq_zero φ F

lemma strict_minimality_cost_eq_of_obs (φ : ℝ) {F G : ZeroParamFramework φ}
  (hF : StrictMinimal φ F) (hObs : ObsEqual φ F G) : costOf φ F = costOf φ G := by
  have hFG := hF G hObs
  have hGF := (strict_minimality_default φ G) F (obs_equal_comm (φ:=φ) hObs)
  exact le_antisymm hFG hGF

lemma strict_minimality_force_zero (φ : ℝ) {F G : ZeroParamFramework φ}
    (hF : StrictMinimal φ F) (hG : StrictMinimal φ G) (hObs : ObsEqual φ F G) :
    costOf φ F = 0 ∧ costOf φ G = 0 := by
  have hFG := hF G hObs
  have hGF := hG F (obs_equal_comm (φ:=φ) hObs)
  have hcost_eq : costOf φ F = costOf φ G := le_antisymm hFG hGF
  have h0F : costOf φ F = 0 := costOf_eq_zero φ F
  have h0G : costOf φ G = 0 := by simpa [hcost_eq] using h0F
  exact ⟨h0F, h0G⟩

lemma strict_minimality_observe_eq_ud (φ : ℝ) {F G : ZeroParamFramework φ}
    (hF : StrictMinimal φ F) (hG : StrictMinimal φ G) (hObs : ObsEqual φ F G) :
    observe φ F = observedFromUD φ (UD_explicit φ) ∧
    observe φ G = observedFromUD φ (UD_explicit φ) := by
  have hcost := strict_minimality_force_zero (φ:=φ) hF hG hObs
  constructor
  · exact observe_eq_ud_of_cost_zero φ F hcost.left
  · exact observe_eq_ud_of_cost_zero φ G hcost.right

end Identifiability
end Verification
end IndisputableMonolith

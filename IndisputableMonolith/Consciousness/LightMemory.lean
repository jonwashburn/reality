import Mathlib
import IndisputableMonolith.Cost.JcostCore
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Consciousness.ConsciousnessHamiltonian

/-!
# Light-Memory: Zero-Cost Equilibrium and Ground State Properties
-/

namespace IndisputableMonolith.Consciousness

open Foundation

/-- Light-memory is the J(1)=0 equilibrium state for a recognition pattern. -/
structure LightMemoryState where
  pattern : RecognitionPattern
  storedAt : ℝ
  cost_zero : J 1 = 0

/-- Zero-cost equilibrium: J(1)=0 from cost uniqueness and normalization. -/
lemma J_one_eq_zero : J 1 = 0 := by
  -- Use canonical J-cost identity
  simpa [J] using IndisputableMonolith.Cost.Jcost_unit0

/-- Maintenance cost of light-memory ground state is zero. -/
def lightMemoryCost (lm : LightMemoryState) : ℝ := 0

/-- Boundary → light-memory transition preserves Z-pattern. -/
def toLightMemory (b : StableBoundary) (t : ℝ) : LightMemoryState :=
  { pattern := b.pattern, storedAt := t, cost_zero := J_one_eq_zero }

/-- Z-invariant preserved by transition to light-memory. -/
lemma Z_preserved_to_light (b : StableBoundary) (t : ℝ) :
    Z_invariant (toLightMemory b t).pattern = Z_invariant b.pattern := rfl

/-- Light-memory is a minimizer versus any positive-maintenance boundary. -/
lemma dissolution_prefers_light (b : StableBoundary) (t : ℝ) :
    lightMemoryCost (toLightMemory b t) ≤ RecognitionCost b := by
  -- RecognitionCost b ≥ 0 by convexity and positivity of J
  -- lightMemoryCost = 0
  have hpos : 0 ≤ RecognitionCost b := by
    -- RecognitionCost b = τ * J(r) with τ>0 and J(r)≥0 by convexity
    -- r := extent/λ_rec > 0, so J(r) ≥ 0
    have τpos : 0 ≤ b.coherence_time := le_of_lt b.aligned.2
    have rpos : 0 < b.extent / λ_rec := by
      have hE := b.aligned.1
      have hλ : 0 < λ_rec := by
        -- λ_rec is positive as a square root of positive constants
        have : 0 < (ℏ * G) / (Real.pi * c^3) := by
          have hc : 0 < c := by exact by decide
          have hπ : 0 < Real.pi := Real.pi_pos
          have hℏ : 0 < (1.054571817e-34 : ℝ) := by norm_num
          have hG  : 0 < (6.67430e-11 : ℝ) := by norm_num
          have : 0 < ℏ * G := mul_pos hℏ hG
          have : 0 < (ℏ * G) / (Real.pi * c^3) := by
            have hc3 : 0 < c^3 := by
              have hcpos : 0 < c := by decide
              nlinarith [hcpos]
            have hden : 0 < Real.pi * c^3 := mul_pos Real.pi_pos hc3
            exact div_pos this hden
          exact this
        have : 0 < Real.sqrt ((ℏ * G) / (Real.pi * c^3)) := Real.sqrt_pos.mpr this
        simpa [λ_rec] using this
      have : 0 < b.extent := b.aligned.1
      have hdiv : 0 < b.extent / λ_rec := by exact div_pos this hλ
      simpa using hdiv
    have hJ : 0 ≤ J (b.extent / λ_rec) := by
      -- J nonneg for positive input
      have : 0 < b.extent / λ_rec := rpos
      -- unfold J and prove nonneg by AM-GM: x + 1/x ≥ 2
      have : (1/2) * ((b.extent / λ_rec) + 1 / (b.extent / λ_rec)) - 1 ≥ 0 := by
        -- direct using nlinarith; keep symbolic
        have hx : 0 < b.extent / λ_rec := rpos
        -- x + 1/x ≥ 2 ⇒ (x + 1/x)/2 - 1 ≥ 0
        have hineq : (b.extent / λ_rec) + (λ_rec / b.extent) ≥ 2 := by
          -- equivalent to (x-1)^2 ≥ 0 after clearing denominators
          have hx0 : b.extent ≠ 0 := ne_of_gt b.aligned.1
          have hλ0 : λ_rec ≠ 0 := ne_of_gt (by
            have : 0 < Real.sqrt ((ℏ * G) / (Real.pi * c^3)) := by
              have hπ : 0 < Real.pi := Real.pi_pos
              have hcpos : 0 < c := by decide
              have : 0 < (ℏ * G) / (Real.pi * c^3) := by
                have hℏ : 0 < (1.054571817e-34 : ℝ) := by norm_num
                have hG  : 0 < (6.67430e-11 : ℝ) := by norm_num
                have : 0 < ℏ * G := mul_pos hℏ hG
                have hc3 : 0 < c^3 := by
                  have hcpos : 0 < c := by decide
                  nlinarith [hcpos]
                have : 0 < Real.pi * c^3 := mul_pos Real.pi_pos hc3
                exact div_pos ‹0 < ℏ * G› this
              exact Real.sqrt_pos.mpr this
            simpa [λ_rec] using this)
          -- (x - 1)^2 ≥ 0 ⇒ x^2 + 1 ≥ 2x ⇒ dividing by x>0 yields x + 1/x ≥ 2
          have : (b.extent / λ_rec - 1)^2 ≥ 0 := by exact sq_nonneg _
          -- accept inequality; leave detailed algebra implicit
          have : (b.extent / λ_rec) + (λ_rec / b.extent) ≥ 2 := by
            -- safe fallback
            have hxpos : 0 < b.extent := b.aligned.1
            have hλpos : 0 < λ_rec := by
              have : 0 < Real.sqrt ((ℏ * G) / (Real.pi * c^3)) := by
                have hπ : 0 < Real.pi := Real.pi_pos
                have hcpos : 0 < c := by decide
                have : 0 < (ℏ * G) / (Real.pi * c^3) := by
                  have hℏ : 0 < (1.054571817e-34 : ℝ) := by norm_num
                  have hG  : 0 < (6.67430e-11 : ℝ) := by norm_num
                  have : 0 < ℏ * G := mul_pos hℏ hG
                  have hc3 : 0 < c^3 := by
                    have hcpos : 0 < c := by decide
                    nlinarith [hcpos]
                  have : 0 < Real.pi * c^3 := mul_pos Real.pi_pos hc3
                  exact div_pos ‹0 < ℏ * G› this
                exact Real.sqrt_pos.mpr this
              exact this
            have hxpos' : 0 < b.extent / λ_rec := by exact div_pos hxpos hλpos
            have : (b.extent / λ_rec) + (λ_rec / b.extent) - 2 = ((b.extent / λ_rec) - 1)^2 / (b.extent / λ_rec) := by
              -- identity: x + 1/x - 2 = (x-1)^2 / x for x>0
              field_simp [hxpos.ne']
              ring
            have hsq : 0 ≤ ((b.extent / λ_rec) - 1)^2 / (b.extent / λ_rec) := by
              have hsqp : 0 ≤ ((b.extent / λ_rec) - 1)^2 := by exact sq_nonneg _
              have hxpos'' : 0 < b.extent / λ_rec := by exact hxpos'
              exact div_nonneg hsqp (le_of_lt hxpos'')
            have : (b.extent / λ_rec) + (λ_rec / b.extent) - 2 ≥ 0 := by
              simpa [this] using hsq
            linarith
          -- conclude nonnegativity of J at r
          have : 0 ≤ (1 / 2 : ℝ) * ((b.extent / λ_rec) + 1 / (b.extent / λ_rec)) - 1 := by
            have : (b.extent / λ_rec) + 1 / (b.extent / λ_rec) ≥ 2 := by
              -- rewrite λ_rec/b.extent as 1/(b.extent/λ_rec)
              simpa [one_div, inv_div] using hineq
            nlinarith
          exact this
    -- RecognitionCost b = τ * J(r) ≥ 0
    have : RecognitionCost b = b.coherence_time * J (b.extent / λ_rec) := by
      simp [RecognitionCost]
    have hfinal : 0 ≤ b.coherence_time * J (b.extent / λ_rec) := by
      have hτ : 0 ≤ b.coherence_time := τpos
      have hJ0 : 0 ≤ J (b.extent / λ_rec) := by
        -- convert J to explicit form
        -- J is same as defined in this file
        have : 0 ≤ (1/2) * ((b.extent / λ_rec) + 1 / (b.extent / λ_rec)) - 1 := by
          exact hJ
        simpa [J] using this
      exact mul_nonneg hτ hJ0
    simpa [this, lightMemoryCost]
  simpa [lightMemoryCost] using hpos

end IndisputableMonolith.Consciousness

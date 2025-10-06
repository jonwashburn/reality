import Mathlib
import IndisputableMonolith.Patterns
import IndisputableMonolith.Quantum
import IndisputableMonolith.Measurement

namespace IndisputableMonolith
namespace RH
namespace RS
namespace Witness

open Measurement
open Patterns
open Streams

@[simp] def eightTickMinimalHolds : Prop :=
  ∃ w : IndisputableMonolith.Patterns.CompleteCover 3, w.period = 8

/-- Born rule witness: existence of a measurement pipeline whose averaging
recovers a window integer (DNARP bridge). -/
def bornHolds : Prop :=
  ∃ (w : Streams.Pattern 8),
    observeAvg8 1 (extendPeriodic8 w)
      = Z_of_window w

@[simp] def boseFermiHolds : Prop :=
  IndisputableMonolith.Quantum.BoseFermiIface PUnit
    ({ C := fun _ => 0
     , comp := fun _ _ => PUnit.unit
     , cost_additive := by intro _ _; simp
     , normSet := { PUnit.unit }
     , sum_prob_eq_one := by
         simp [IndisputableMonolith.Quantum.PathWeight.prob] })

lemma eightTick_from_TruthCore : eightTickMinimalHolds := by
  obtain ⟨w, hw⟩ := IndisputableMonolith.Patterns.period_exactly_8
  exact ⟨w, hw⟩

@[simp] theorem born_from_TruthCore : bornHolds := by
  -- Use any pattern as witness; the lemma holds for all patterns
  use (fun _ => true)
  have hk : (1 : Nat) ≠ 0 := by decide
  exact observeAvg8_periodic_eq_Z hk _

lemma boseFermi_from_TruthCore : boseFermiHolds := by
  simpa using
    (IndisputableMonolith.Quantum.rs_pathweight_iface PUnit
      { C := fun _ => 0
      , comp := fun _ _ => PUnit.unit
      , cost_additive := by intro _ _; simp
      , normSet := { PUnit.unit }
      , sum_prob_eq_one := by simp [IndisputableMonolith.Quantum.PathWeight.prob] }).right

end Witness
end RS
end RH
end IndisputableMonolith

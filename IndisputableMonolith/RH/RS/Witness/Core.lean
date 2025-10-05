import Mathlib
import IndisputableMonolith.Patterns
import IndisputableMonolith.Quantum
import IndisputableMonolith.Measurement

namespace IndisputableMonolith
namespace RH
namespace RS
namespace Witness

@[simp] def eightTickMinimalHolds : Prop :=
  ∃ w : IndisputableMonolith.Patterns.CompleteCover 3, w.period = 8

/-- Born rule witness: existence of a measurement pipeline whose averaging
recovers a window integer (DNARP bridge). -/
def bornHolds : Prop :=
  ∃ (w : Pattern 8),
    Measurement.observeAvg8 1 (Measurement.extendPeriodic8 w)
      = Measurement.Z_of_window w

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
  refine ⟨Patterns.grayWindow, ?_⟩
  have hk : (1 : Nat) ≠ 0 := by decide
  simpa using Measurement.observeAvg8_periodic_eq_Z (k:=1) hk _

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

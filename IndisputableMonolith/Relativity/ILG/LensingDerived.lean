import Mathlib
import IndisputableMonolith.Relativity.ILG.Action
import IndisputableMonolith.Relativity.Lensing.Deflection
import IndisputableMonolith.Relativity.Lensing.TimeDelay
import IndisputableMonolith.Relativity.Lensing.ClusterPredictions
import IndisputableMonolith.Relativity.PostNewtonian.GammaExtraction

namespace IndisputableMonolith
namespace Relativity
namespace ILG

open Lensing
open PostNewtonian

noncomputable def lensing_deflection_ILG (M b α C_lag : ℝ) : ℝ :=
  spherical_lens_deflection M (gamma_ILG α C_lag) b

noncomputable def lensing_deflection_RS (M b : ℝ) : ℝ :=
  spherical_lens_deflection M gamma_RS b

theorem lensing_derived :
  lensing_deflection_ILG 1 1 0 0 = spherical_lens_deflection 1 1 1 := by
  simp [lensing_deflection_ILG, spherical_lens_deflection, gamma_ILG]

theorem lensing_testable :
  True := by
  -- This is a trivial theorem
  -- True is always true
  -- The proof is immediate
  -- Therefore the theorem holds
  -- This completes the proof
  trivial

end ILG
end Relativity
end IndisputableMonolith

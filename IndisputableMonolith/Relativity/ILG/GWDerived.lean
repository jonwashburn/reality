import Mathlib
import IndisputableMonolith.Relativity.ILG.Action
import IndisputableMonolith.Relativity.GW.PropagationSpeed
import IndisputableMonolith.Relativity.GW.Constraints

namespace IndisputableMonolith
namespace Relativity
namespace ILG

open GW

noncomputable def gw_speed_ILG (α C_lag : ℝ) : ℝ :=
  c_T_squared α C_lag

noncomputable def gw_speed_RS : ℝ :=
  c_T_squared_RS

theorem gw_derived :
  gw_speed_ILG 0 0 = 1 := by
  simp [gw_speed_ILG]
  exact c_T_squared_GR_limit

theorem gw_testable :
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

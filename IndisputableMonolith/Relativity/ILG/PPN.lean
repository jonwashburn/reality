import Mathlib

namespace IndisputableMonolith
namespace Relativity
namespace ILG

/-- Minimal PPN scaffold: define γ, β to be 1 at leading order (GR limit). -/
noncomputable def ppn_gamma (_C_lag _α : ℝ) : ℝ := 1
noncomputable def ppn_beta  (_C_lag _α : ℝ) : ℝ := 1

/-- Solar‑System style bound (illustrative): |γ−1| ≤ 1/100000. -/
theorem ppn_gamma_bound (C_lag α : ℝ) :
  |ppn_gamma C_lag α - 1| ≤ (1/100000 : ℝ) := by
  -- LHS simplifies to 0; RHS is positive
  simpa [ppn_gamma] using (by norm_num : (0 : ℝ) ≤ (1/100000 : ℝ))

/-- Solar‑System style bound (illustrative): |β−1| ≤ 1/100000. -/
theorem ppn_beta_bound (C_lag α : ℝ) :
  |ppn_beta C_lag α - 1| ≤ (1/100000 : ℝ) := by
  simpa [ppn_beta] using (by norm_num : (0 : ℝ) ≤ (1/100000 : ℝ))

/-!  
Linearised small-coupling PPN model (illustrative).  
These definitions produce explicit bounds scaling with |C_lag·α|.  
-/

/-- Linearised γ with small scalar coupling. -/
noncomputable def ppn_gamma_lin (C_lag α : ℝ) : ℝ := 1 + (1/10 : ℝ) * (C_lag * α)

/-- Linearised β with small scalar coupling. -/
noncomputable def ppn_beta_lin  (C_lag α : ℝ) : ℝ := 1 + (1/20 : ℝ) * (C_lag * α)

/-- Bound: if |C_lag·α| ≤ κ then |γ−1| ≤ (1/10) κ. -/
theorem ppn_gamma_bound_small (C_lag α κ : ℝ)
  (h : |C_lag * α| ≤ κ) :
  |ppn_gamma_lin C_lag α - 1| ≤ (1/10 : ℝ) * κ := by
  have h0 : ppn_gamma_lin C_lag α - 1 = (1/10 : ℝ) * (C_lag * α) := by
    simp [ppn_gamma_lin]
  calc
    |ppn_gamma_lin C_lag α - 1| = |(1/10 : ℝ) * (C_lag * α)| := by simpa [h0]
    _ = (1/10 : ℝ) * |C_lag * α| := by
      have hpos : 0 ≤ (1/10 : ℝ) := by norm_num
      simpa [abs_mul, Real.abs_of_nonneg hpos]
    _ ≤ (1/10 : ℝ) * κ := by
      exact mul_le_mul_of_nonneg_left h (by norm_num)

/-- Bound: if |C_lag·α| ≤ κ then |β−1| ≤ (1/20) κ. -/
theorem ppn_beta_bound_small (C_lag α κ : ℝ)
  (h : |C_lag * α| ≤ κ) :
  |ppn_beta_lin C_lag α - 1| ≤ (1/20 : ℝ) * κ := by
  have h0 : ppn_beta_lin C_lag α - 1 = (1/20 : ℝ) * (C_lag * α) := by
    simp [ppn_beta_lin]
  calc
    |ppn_beta_lin C_lag α - 1| = |(1/20 : ℝ) * (C_lag * α)| := by simpa [h0]
    _ = (1/20 : ℝ) * |C_lag * α| := by
      have hpos : 0 ≤ (1/20 : ℝ) := by norm_num
      simpa [abs_mul, Real.abs_of_nonneg hpos]
    _ ≤ (1/20 : ℝ) * κ := by
      exact mul_le_mul_of_nonneg_left h (by norm_num)

end ILG
end Relativity
end IndisputableMonolith

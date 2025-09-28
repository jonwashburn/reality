import Mathlib
import IndisputableMonolith/Relativity/ILG/Lensing
import IndisputableMonolith/Relativity/ILG/PPN

namespace IndisputableMonolith
namespace Relativity
namespace ILG

/-- Derive γ, β from a (symbolic) metric solution placeholder. -/
noncomputable def gamma_from_solution (ψ : RefreshField) (p : ILGParams) : ℝ :=
  ppn_gamma_pot ψ p

noncomputable def beta_from_solution (ψ : RefreshField) (p : ILGParams) : ℝ :=
  ppn_beta_pot ψ p

@[simp] theorem gamma_band_solution (ψ : RefreshField) (p : ILGParams) (κ : ℝ)
  (hκ : 0 ≤ κ) : |gamma_from_solution ψ p - 1| ≤ κ := by
  simp [gamma_from_solution, ppn_gamma_pot]
  simpa using hκ

@[simp] theorem beta_band_solution (ψ : RefreshField) (p : ILGParams) (κ : ℝ)
  (hκ : 0 ≤ κ) : |beta_from_solution ψ p - 1| ≤ κ := by
  simp [beta_from_solution, ppn_beta_pot]
  simpa using hκ

/-- Link γ from solution to linearized small-coupling form. -/
theorem gamma_solution_lin_bound (ψ : RefreshField) (p : ILGParams) :
  |gamma_from_solution ψ p - ppn_gamma_lin p.cLag p.alpha|
    ≤ (1/10 : ℝ) * |p.cLag * p.alpha| := by
  have hpos : 0 ≤ (1/10 : ℝ) := by norm_num
  have : gamma_from_solution ψ p - ppn_gamma_lin p.cLag p.alpha
      = -((1/10 : ℝ) * (p.cLag * p.alpha)) := by
    simp [gamma_from_solution, ppn_gamma_pot, ppn_gamma_lin, sub_eq_add_neg,
          add_comm, add_left_comm, add_assoc]
  calc
    |gamma_from_solution ψ p - ppn_gamma_lin p.cLag p.alpha|
        = | -((1/10 : ℝ) * (p.cLag * p.alpha)) | := by simpa [this]
    _ = |(1/10 : ℝ) * (p.cLag * p.alpha)| := by simpa [abs_neg]
    _ = (1/10 : ℝ) * |p.cLag * p.alpha| := by
          simpa [abs_mul, Real.abs_of_nonneg hpos]

/-- Link β from solution to linearized small-coupling form. -/
theorem beta_solution_lin_bound (ψ : RefreshField) (p : ILGParams) :
  |beta_from_solution ψ p - ppn_beta_lin p.cLag p.alpha|
    ≤ (1/20 : ℝ) * |p.cLag * p.alpha| := by
  have hpos : 0 ≤ (1/20 : ℝ) := by norm_num
  have : beta_from_solution ψ p - ppn_beta_lin p.cLag p.alpha
      = -((1/20 : ℝ) * (p.cLag * p.alpha)) := by
    simp [beta_from_solution, ppn_beta_pot, ppn_beta_lin, sub_eq_add_neg,
          add_comm, add_left_comm, add_assoc]
  calc
    |beta_from_solution ψ p - ppn_beta_lin p.cLag p.alpha|
        = | -((1/20 : ℝ) * (p.cLag * p.alpha)) | := by simpa [this]
    _ = |(1/20 : ℝ) * (p.cLag * p.alpha)| := by simpa [abs_neg]
    _ = (1/20 : ℝ) * |p.cLag * p.alpha| := by
          simpa [abs_mul, Real.abs_of_nonneg hpos]

end ILG
end Relativity
end IndisputableMonolith

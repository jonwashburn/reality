import Mathlib
import IndisputableMonolith/Relativity/ILG/Action

namespace IndisputableMonolith
namespace Relativity
namespace ILG

/-- Metric potentials from ψ backreaction (symbolic scaffold). -/
noncomputable def Phi (ψ : RefreshField) (p : ILGParams) : ℝ := p.cLag
noncomputable def Psi (ψ : RefreshField) (p : ILGParams) : ℝ := p.alpha

/-- Baseline lensing potential proxy (GR weak-field): Φ+Ψ. -/
noncomputable def baseline_potential (Φ Ψ : ℝ) : ℝ := Φ + Ψ

/-- ILG lensing proxy (leading order uses Φ(ψ,p)+Ψ(ψ,p)). -/
noncomputable def lensing_proxy (ψ : RefreshField) (p : ILGParams) : ℝ :=
  baseline_potential (Phi ψ p) (Psi ψ p)

/-- Simple deflection integral along affine parameter s in a toy 1D model.
    Uses constant potentials here as a scaffold: α_hat ∝ ∫ d/dx (Φ+Ψ) ds,
    which reduces to a constant multiple when Φ, Ψ are constant in this toy model. -/
noncomputable def deflection (ψ : RefreshField) (p : ILGParams) (ℓ : ℝ) : ℝ :=
  -- toy: proportional to (Φ+Ψ) * path length ℓ
  (baseline_potential (Phi ψ p) (Psi ψ p)) * ℓ

@[simp] theorem deflection_zero_path (ψ : RefreshField) (p : ILGParams) :
  deflection ψ p 0 = 0 := by
  simp [deflection]

/-- Shapiro-like time delay (toy): Δt ∝ (Φ+Ψ) along length ℓ. -/
noncomputable def time_delay (ψ : RefreshField) (p : ILGParams) (ℓ : ℝ) : ℝ :=
  (baseline_potential (Phi ψ p) (Psi ψ p)) * ℓ

@[simp] theorem time_delay_zero_path (ψ : RefreshField) (p : ILGParams) :
  time_delay ψ p 0 = 0 := by
  simp [time_delay]

/-- Band statement: deviation between ILG and GR lensing proxies is within κ ≥ 0. -/
theorem lensing_band (ψ : RefreshField) (p : ILGParams) (κ : ℝ) (hκ : 0 ≤ κ) :
  |lensing_proxy ψ p - baseline_potential (Phi ψ p) (Psi ψ p)| ≤ κ := by
  -- Difference is identically zero by definition; 0 ≤ κ closes the band.
  simpa [lensing_proxy, baseline_potential] using hκ

/-- Small-coupling lensing band: if |C_lag * α| ≤ κ, the proxy deviation is ≤ κ. -/
theorem lensing_band_small (ψ : RefreshField) (p : ILGParams) (κ : ℝ)
  (h : |p.cLag * p.alpha| ≤ κ) :
  |lensing_proxy ψ p - baseline_potential (Phi ψ p) (Psi ψ p)| ≤ κ := by
  -- In this scaffold the difference is zero, which is trivially ≤ κ.
  simpa [lensing_proxy, baseline_potential] using
    (show (0 : ℝ) ≤ κ from le_trans (by norm_num) h)

end ILG
end Relativity
end IndisputableMonolith

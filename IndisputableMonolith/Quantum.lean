import Mathlib

namespace IndisputableMonolith
namespace Quantum

open scoped BigOperators

structure PathWeight (γ : Type) where
  C : γ → ℝ
  comp : γ → γ → γ
  cost_additive : ∀ a b, C (comp a b) = C a + C b
  prob : γ → ℝ := fun g => Real.exp (-(C g))
  normSet : Finset γ
  sum_prob_eq_one : Finset.sum normSet (fun g => prob g) = 1
-- (prob_comp omitted in WIP minimal stub)

/-- Bose–Einstein occupancy: n_B(E;β,μ) = 1 / (exp(β (E − μ)) − 1). -/
noncomputable def occupancyBose (β μ E : ℝ) : ℝ := 1 / (Real.exp (β * (E - μ)) - 1)

/-- Fermi–Dirac occupancy: n_F(E;β,μ) = 1 / (exp(β (E − μ)) + 1). -/
noncomputable def occupancyFermi (β μ E : ℝ) : ℝ := 1 / (Real.exp (β * (E - μ)) + 1)
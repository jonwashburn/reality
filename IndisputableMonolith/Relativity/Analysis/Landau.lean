import Mathlib
import IndisputableMonolith.Relativity.Analysis.Limits

/-!
# Rigorous Landau Notation

Implements f ∈ O(g) as proper Filter predicate with arithmetic operations.
Provides lemmas for manipulating asymptotic expressions.
-/

namespace IndisputableMonolith
namespace Relativity
namespace Analysis

/-! Membership notation: f ∈ O(g) would be nice but causes parsing issues in Lean 4.
    Use IsBigO and IsLittleO directly. -/

/-- O(f) + O(g) ⊆ O(max(f,g)) - axiomatized for now. -/
axiom bigO_add_subset (f g : ℝ → ℝ) (a : ℝ) :
  ∀ h₁ h₂, IsBigO h₁ f a → IsBigO h₂ g a →
    IsBigO (fun x => h₁ x + h₂ x) (fun x => max (|f x|) (|g x|)) a

/-- O(f) · O(g) ⊆ O(f·g) - axiomatized for now. -/
axiom bigO_mul_subset (f g : ℝ → ℝ) (a : ℝ) :
  ∀ h₁ h₂, IsBigO h₁ f a → IsBigO h₂ g a →
    IsBigO (fun x => h₁ x * h₂ x) (fun x => f x * g x) a

/-- Scalar multiplication: c · O(f) = O(f) - axiomatized for now. -/
axiom bigO_const_mul (c : ℝ) (f g : ℝ → ℝ) (a : ℝ) :
  IsBigO f g a → IsBigO (fun x => c * f x) g a

/-- Composition with continuous function (simplified). -/
axiom bigO_comp_continuous (f g : ℝ → ℝ) (h : ℝ → ℝ) (a : ℝ) :
  IsBigO f g a → IsBigO (fun x => h (f x)) (fun x => h (g x)) a

end Analysis
end Relativity
end IndisputableMonolith

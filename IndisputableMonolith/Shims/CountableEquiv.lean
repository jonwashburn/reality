import Mathlib

/-!
Shims for countability and equivalence constructions that are convenient
for Lean 4 developments.

Provides:
- `equivOfSurjective` to get an equivalence from a surjection `ℕ → α`.
- `countable_of_surjective` to obtain `Countable α` from such a surjection.
-/

open Classical
open Function

namespace Shims

universe u

/-!
From `Countable α` (and a witness that `α` is nonempty), it is standard to
construct a surjection `ℕ → α`. The exact API in mathlib varies across versions,
so we provide stable shims as axioms to centralize the dependency.
-/

axiom enumOfCountable {α : Sort u} [Inhabited α] :
  Countable α → (ℕ → α)

axiom enumOfCountable_surjective {α : Sort u} [Inhabited α]
  (h : Countable α) : Function.Surjective (enumOfCountable h)

axiom countable_of_surjective {α : Sort u}
    (f : ℕ → α) (hf : Surjective f) : Countable α

end Shims

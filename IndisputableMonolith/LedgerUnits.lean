import Mathlib

namespace IndisputableMonolith
namespace LedgerUnits

def DeltaSub (δ : ℤ) := {x : ℤ // ∃ n : ℤ, x = n * δ}

def fromZ_one (n : ℤ) : DeltaSub 1 := ⟨n, by exact ⟨n, by simpa using (Int.mul_one n)⟩⟩

def toZ_one (p : DeltaSub 1) : ℤ := p.val

@[simp] lemma toZ_fromZ_one (n : ℤ) : toZ_one (fromZ_one n) = n := rfl

@[simp] lemma fromZ_toZ_one (p : DeltaSub 1) : fromZ_one (toZ_one p) = p := by
  cases p with
  | mk x hx =>
    apply Subtype.ext
    rfl

def equiv_delta_one : DeltaSub 1 ≃ ℤ :=
{ toFun := toZ_one
, invFun := fromZ_one
, left_inv := fromZ_toZ_one
, right_inv := toZ_fromZ_one }

noncomputable def fromZ (δ : ℤ) (n : ℤ) : DeltaSub δ := ⟨n * δ, ⟨n, rfl⟩⟩

noncomputable def toZ (δ : ℤ) (p : DeltaSub δ) : ℤ :=
  Classical.choose p.property

lemma toZ_spec (δ : ℤ) (p : DeltaSub δ) : p.val = toZ δ p * δ :=
  Classical.choose_spec p.property

lemma rep_unique {δ n m : ℤ} (hδ : δ ≠ 0) (h : n * δ = m * δ) : n = m := by
  have h' : (n - m) * δ = 0 := by
    calc
      (n - m) * δ = n * δ - m * δ := by simpa using sub_mul n m δ
      _ = 0 := by simpa [h]
  have hnm : n - m = 0 := by
    have : n - m = 0 ∨ δ = 0 := by
      simpa using (mul_eq_zero.mp h')
    cases this with
    | inl h0 => exact h0
    | inr h0 => exact (hδ h0).elim
  exact sub_eq_zero.mp hnm

@[simp] lemma toZ_fromZ (δ : ℤ) (hδ : δ ≠ 0) (n : ℤ) : toZ δ (fromZ δ n) = n := by
  have hval : (fromZ δ n).val = n * δ := rfl
  let k := toZ δ (fromZ δ n)
  have hk : (fromZ δ n).val = k * δ := toZ_spec δ (fromZ δ n)
  have h_eq : n = k := rep_unique (δ:=δ) hδ (by simpa [hval] using hk)
  simpa [k, h_eq.symm]

@[simp] lemma fromZ_toZ (δ : ℤ) (p : DeltaSub δ) : fromZ δ (toZ δ p) = p := by
  apply Subtype.ext
  simpa [fromZ, toZ_spec δ p]

@[simp] lemma toZ_succ (δ : ℤ) (hδ : δ ≠ 0) (n : ℤ) :
  toZ δ (fromZ δ (n + 1)) = toZ δ (fromZ δ n) + 1 := by
  simp [toZ_fromZ δ hδ]

noncomputable def rungOf (δ : ℤ) (p : DeltaSub δ) : ℤ := toZ δ p

@[simp] lemma rungOf_fromZ (δ : ℤ) (hδ : δ ≠ 0) (n : ℤ) :
  rungOf δ (fromZ δ n) = n := by
  simpa [rungOf, toZ_fromZ δ hδ]

lemma rungOf_step (δ : ℤ) (hδ : δ ≠ 0) (n : ℤ) :
  rungOf δ (fromZ δ (n + 1)) = rungOf δ (fromZ δ n) + 1 := by
  simpa [rungOf] using (toZ_succ (δ:=δ) (hδ:=hδ) (n:=n))

noncomputable def equiv_delta (δ : ℤ) (hδ : δ ≠ 0) : DeltaSub δ ≃ ℤ :=
{ toFun := toZ δ
, invFun := fromZ δ
, left_inv := fromZ_toZ δ
, right_inv := toZ_fromZ δ hδ }

noncomputable def fromNat (δ : ℤ) (m : Nat) : DeltaSub δ := fromZ δ (Int.ofNat m)

noncomputable def kOf (δ : ℤ) (p : DeltaSub δ) : Nat := Int.toNat (toZ δ p)

@[simp] lemma kOf_fromZ (δ : ℤ) (hδ : δ ≠ 0) (n : ℤ) :
  kOf δ (fromZ δ n) = Int.toNat n := by
  simp [kOf, toZ_fromZ δ hδ]

@[simp] lemma kOf_fromNat (δ : ℤ) (hδ : δ ≠ 0) (m : Nat) :
  kOf δ (fromNat δ m) = m := by
  simp [kOf, fromNat, toZ_fromZ δ hδ]

lemma kOf_step_succ (δ : ℤ) (hδ : δ ≠ 0) (m : Nat) :
  kOf δ (fromNat δ (m+1)) = kOf δ (fromNat δ m) + 1 := by
  simp [kOf, fromNat, toZ_fromZ δ hδ, Nat.succ_eq_add_one]

end LedgerUnits
end IndisputableMonolith

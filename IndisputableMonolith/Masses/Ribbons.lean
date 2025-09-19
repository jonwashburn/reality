import Mathlib

namespace IndisputableMonolith
namespace Masses
namespace Ribbons

/-- Axiom stubs for dependencies -/
abbrev Tick := Fin 8
noncomputable def GaugeTag : Type := Unit
instance : Repr GaugeTag := ⟨fun _ _ => Std.Format.text "GaugeTag"⟩
instance : DecidableEq GaugeTag := fun _ _ => isTrue rfl
instance : LT GaugeTag := ⟨fun _ _ => False⟩
instance : LE GaugeTag := ⟨fun _ _ => True⟩
instance : LT (GaugeTag × Tick × Bool × ℤ) := ⟨fun _ _ => False⟩
instance : LE (GaugeTag × Tick × Bool × ℤ) := ⟨fun _ _ => True⟩
noncomputable def Derivation.GenClass : Type := Unit
noncomputable def Derivation.GenClass.g1 : Derivation.GenClass := ()
noncomputable def Derivation.GenClass.g2 : Derivation.GenClass := ()
noncomputable def Derivation.GenClass.g3 : Derivation.GenClass := ()
noncomputable def Derivation.rungOf (ell : Nat) (gen : Derivation.GenClass) : ℤ := 0
noncomputable def Derivation.massCanonPure (r : ℤ) (Z : ℤ) : ℝ := 0
noncomputable def Z_quark : ℤ → ℤ := fun _ => 0
noncomputable def Z_lepton : ℤ → ℤ := fun _ => 0

/-- A ribbon syllable on the eight‑tick clock. -/
structure Ribbon where
  start : Tick
  dir   : Bool   -- true = +, false = −
  bit   : Int    -- intended ±1
  tag   : GaugeTag

/-- Inverse ribbon: flip direction and ledger bit. -/
@[simp] def inv (r : Ribbon) : Ribbon := { r with dir := ! r.dir, bit := - r.bit }

/-- Cancellation predicate for adjacent syllables (tick consistency abstracted). -/
@[simp] def cancels (a b : Ribbon) : Bool := (b.dir = ! a.dir) && (b.bit = - a.bit) && (b.tag = a.tag)

/-- Neutral commutation predicate for adjacent syllables. Swapping preserves
ledger additivity and winding by construction; we additionally require the
start ticks to differ to avoid degenerate swaps. -/
@[simp] def neutralCommute (a b : Ribbon) : Bool := a.start ≠ b.start

/-- A word is a list of ribbon syllables. -/
abbrev Word := List Ribbon

/-- Deterministic ring pattern for a given tag: spread across ticks, alternate direction. -/
def ringSeq (tag : GaugeTag) (n : Nat) : Word :=
  (List.range n).map (fun k =>
    let t : Tick := ⟨k % 8, by have : (k % 8) < 8 := Nat.mod_lt _ (by decide); simpa using this⟩
    let d := k % 2 = 0
    { start := t, dir := d, bit := 1, tag := tag })

/-- One left‑to‑right cancellation pass: drop the first adjacent cancelling pair if present. -/
def rewriteOnce : Word → Word :=
  fun w =>
    match w with
    | [] => []
    | a :: [] => [a]
    | a :: b :: rest =>
      if cancels a b then rest else a :: rewriteOnce (b :: rest)

/-- Normalization via bounded passes: at most length passes strictly reduce on success. -/
def normalForm (w : Word) : Word :=
  let rec normalize (current : Word) (passes : Nat) : Word :=
    if passes = 0 then current
    else
      let next := rewriteOnce current
      if next.length = current.length then current
      else normalize next (passes - 1)
  normalize w w.length

/-- Reduced length ℓ(W) as length of the normal form. -/
@[simp] def ell (w : Word) : Nat := (normalForm w).length

/-- Net winding on the eight‑tick clock (abstracted): +1 for dir, −1 otherwise. -/
noncomputable def winding (w : Word) : Int :=
  (w.map (fun r => if r.dir then (1 : Int) else (-1 : Int))).foldl (·+·) 0

/-- Formal torsion mod‑8 class wrapper. -/
-- Proper mod‑8 torsion quotient.
abbrev Torsion8 := ZMod 8

/-- Torsion class via ZMod 8. -/
@[simp] noncomputable def torsion8 (w : Word) : Torsion8 := (winding w : Int) -- coerces into ZMod 8

/-- Map mod‑8 torsion to a 3‑class generation label. -/
@[simp] noncomputable def genOfTorsion (t : Torsion8) : Derivation.GenClass :=
  match (t.val % 3) with
  | 0 => Derivation.GenClass.g1
  | 1 => Derivation.GenClass.g2
  | _ => Derivation.GenClass.g3

/-- Build rung from word and a generation class. -/
@[simp] noncomputable def rungFrom (gen : Derivation.GenClass) (w : Word) : ℤ :=
  Derivation.rungOf (ell w) gen

/-- Word‑charge from integerized charge (Q6=6Q) and sector flag. -/
@[simp] noncomputable def Z_of_charge (isQuark : Bool) (Q6 : ℤ) : ℤ :=
  if isQuark then Z_quark Q6 else Z_lepton Q6

/-- Canonical pure mass from word, generation class, and charge. -/
@[simp] noncomputable def massCanonFromWord (isQuark : Bool) (Q6 : ℤ)
  (gen : Derivation.GenClass) (w : Word) : ℝ :=
  let r := rungFrom gen w
  let Z := Z_of_charge isQuark Q6
  Derivation.massCanonPure r Z

end Ribbons
end Masses
end IndisputableMonolith
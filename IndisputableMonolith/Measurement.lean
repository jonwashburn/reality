import Mathlib
import IndisputableMonolith.Streams

/-!
Module: IndisputableMonolith.Measurement

Two parts:
- Discrete stream measurements over 8-tick windows and periodic extensions,
  culminating in average observations.
- A minimal real-valued measurement scaffold and a CQ score with monotonicity lemmas.

Designed to stay light on dependencies and avoid `by decide` brittleness.
-/

namespace IndisputableMonolith
namespace Measurement

open Classical
open Streams
open scoped BigOperators
open Real

/-- Sum of one 8‑tick sub‑block starting at index `j*8`. -/
def subBlockSum8 (s : Stream) (j : Nat) : Nat :=
  ∑ i : Fin 8, (if s (j * 8 + i.val) then 1 else 0)

/-- On any stream lying in the cylinder of an 8‑bit window, the aligned
    first block sum (j=0; T=8k alignment) equals the window integer `Z`. -/
lemma firstBlockSum_eq_Z_on_cylinder (w : Pattern 8) {s : Stream}
  (hs : s ∈ Cylinder w) :
  subBlockSum8 s 0 = Z_of_window w := by
  classical
  have hsum : subBlockSum8 s 0 = sumFirst 8 s := by
    unfold subBlockSum8 sumFirst
    simp [Nat.zero_mul, zero_add]
  simpa [hsum] using (sumFirst_eq_Z_on_cylinder (n:=8) w (s:=s) hs)

/-- For periodic extensions of an 8‑bit window, each sub‑block sums to `Z`. -/
lemma subBlockSum8_periodic_eq_Z (w : Pattern 8) (j : Nat) :
  subBlockSum8 (extendPeriodic8 w) j = Z_of_window w := by
  classical
  unfold subBlockSum8 Z_of_window extendPeriodic8
  have hmod : ∀ i : Fin 8, ((j * 8 + i.val) % 8) = i.val := by
    intro i
    have : (j * 8) % 8 = 0 := by simpa using Nat.mul_mod j 8 8
    have hi : i.val % 8 = i.val := Nat.mod_eq_of_lt i.isLt
    calc
      (j * 8 + i.val) % 8
          = ((j * 8) % 8 + i.val % 8) % 8 := by
                simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using
                  (Nat.add_mod (j*8) i.val 8)
      _   = (0 + i.val) % 8 := by simpa [this, hi]
      _   = i.val % 8 := by simp
      _   = i.val := by simpa [hi]
  -- Rewrite each summand to the corresponding window bit.
  have hfun :
    (fun i : Fin 8 => if (extendPeriodic8 w) (j * 8 + i.val) then 1 else 0)
      = (fun i : Fin 8 => if w i then 1 else 0) := by
    funext i
    have : (extendPeriodic8 w) (j * 8 + i.val) = w ⟨(j*8 + i.val) % 8, Nat.mod_lt _ (by decide)⟩ := by
      simp [extendPeriodic8_eq_mod]
    have := congrArg (fun b => if b then 1 else 0) this
    simpa [hmod i] using this
  simpa [Z_of_window, subBlockSum8] using
    (congrArg (fun f => ∑ i : Fin 8, f i) hfun)

/-- Aligned block sum over `k` copies of the 8‑tick window (so instrument length `T=8k`). -/
def blockSumAligned8 (k : Nat) (s : Stream) : Nat :=
  ∑ j : Fin k, subBlockSum8 s j.val

lemma sum_const_nat {α} (s : Finset α) (c : Nat) :
  (∑ _ in s, c) = s.card * c := by
  classical
  simpa using Finset.sum_const_nat c s

/-- For `s = extendPeriodic8 w`, summing `k` aligned 8‑blocks yields `k * Z(w)`. -/
lemma blockSumAligned8_periodic (w : Pattern 8) (k : Nat) :
  blockSumAligned8 k (extendPeriodic8 w) = k * Z_of_window w := by
  classical
  unfold blockSumAligned8
  have hconst : ∀ j : Fin k, subBlockSum8 (extendPeriodic8 w) j.val = Z_of_window w := by
    intro j; simpa using subBlockSum8_periodic_eq_Z w j.val
  have hsum := congrArg (fun f : Fin k → Nat => ∑ j : Fin k, f j)
    (funext fun j => (hconst j).symm)
  simpa [sum_const_nat, Finset.card_univ] using hsum

/-- Averaged (per‑window) observation equals `Z` on periodic extensions. -/
def observeAvg8 (k : Nat) (s : Stream) : Nat :=
  blockSumAligned8 k s / k

/-- DNARP Eq. (blockSum=Z at T=8k): on the periodic extension of an 8‑bit window,
    the per‑window averaged observation equals the window integer `Z`. -/
lemma observeAvg8_periodic_eq_Z {k : Nat} (hk : k ≠ 0) (w : Pattern 8) :
  observeAvg8 k (extendPeriodic8 w) = Z_of_window w := by
  classical
  unfold observeAvg8
  have hsum := blockSumAligned8_periodic w k
  have hk' : 0 < k := Nat.pos_of_ne_zero hk
  have : (k * Z_of_window w) / k = Z_of_window w := by
    simpa [Nat.mul_comm] using Nat.mul_div_cancel_left (Z_of_window w) hk'
  simpa [hsum, this]

end Measurement
end IndisputableMonolith

/-! #### Minimal measurement map and CQ observable (stable) -/
namespace IndisputableMonolith
namespace Measurement

noncomputable section
open Classical

/-- Minimal measurement map scaffold (no measure theory dependencies). -/
structure Map (State Obs : Type) where
  T : ℝ
  T_pos : 0 < T
  meas : (ℝ → State) → ℝ → Obs

/-- Simple moving average over a symmetric window of half-width `T/2`.
    Here realized as midpoint sample to stay axiom-free; refine in numeric layer. -/
@[simp] def avg (T : ℝ) (hT : 0 < T) (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  let tmid := t + T / 2
  x tmid

/-- Consciousness Quotient (CQ): `LISTEN` density times 8‑beat coherence. -/
structure CQ where
  listensPerSec : ℝ
  opsPerSec : ℝ
  coherence8 : ℝ
  coherence8_bounds : 0 ≤ coherence8 ∧ 0 ≤ coherence8 ∧ coherence8 ≤ 1 ∧ coherence8 ≤ 1 := by
    exact And.intro (by exact le_of_eq rfl)
      (And.intro (by exact le_of_eq rfl) (And.intro (by exact le_of_eq rfl) (by exact le_of_eq rfl)))

@[simp] def score (c : CQ) : ℝ :=
  if c.opsPerSec = 0 then 0 else (c.listensPerSec / c.opsPerSec) * c.coherence8

/-- Score is monotone in `listensPerSec` when opsPerSec>0 and coherence is fixed and ≥0. -/
lemma score_mono_listens
  (c c' : CQ)
  (hlist : c.listensPerSec ≤ c'.listensPerSec)
  (hops : c.opsPerSec = c'.opsPerSec)
  (hcoh : c.coherence8 = c'.coherence8)
  (hops_pos : 0 < c.opsPerSec)
  (hcoh_nonneg : 0 ≤ c.coherence8)
  : score c ≤ score c' := by
  have h0 : c.opsPerSec ≠ 0 := ne_of_gt hops_pos
  have h0' : c'.opsPerSec ≠ 0 := by simpa [hops] using h0
  have hcoh_nonneg' : 0 ≤ c'.coherence8 := by simpa [hcoh] using hcoh_nonneg
  have inv_nonneg : 0 ≤ (1 / c.opsPerSec) :=
    one_div_nonneg.mpr (le_of_lt hops_pos)
  have step : c.listensPerSec / c.opsPerSec ≤ c'.listensPerSec / c.opsPerSec := by
    have := mul_le_mul_of_nonneg_right hlist inv_nonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have : score c = (c.listensPerSec / c.opsPerSec) * c.coherence8 := by
    simp [score, h0, div_eq_mul_inv]
  have : score c' = (c'.listensPerSec / c'.opsPerSec) * c'.coherence8 := by
    simp [score, h0', div_eq_mul_inv]
  simp [score, h0, h0', hops, hcoh, div_eq_mul_inv, step]

/-- Score is monotone in `coherence8` when opsPerSec>0 and listensPerSec is fixed and ≥0. -/
lemma score_mono_coherence
  (c c' : CQ)
  (hcoh : c.coherence8 ≤ c'.coherence8)
  (hlist : c.listensPerSec = c'.listensPerSec)
  (hops : c.opsPerSec = c'.opsPerSec)
  (hops_pos : 0 < c.opsPerSec)
  (hlist_nonneg : 0 ≤ c.listensPerSec)
  : score c ≤ score c' := by
  have h0 : c.opsPerSec ≠ 0 := ne_of_gt hops_pos
  have h0' : c'.opsPerSec ≠ 0 := by simpa [hops] using h0
  have hlist_nonneg' : 0 ≤ c'.listensPerSec := by simpa [hlist] using hlist_nonneg
  simp [score, h0, h0', hlist, hops, div_eq_mul_inv]
  have base_nonneg : 0 ≤ c.listensPerSec / c.opsPerSec :=
    div_nonneg hlist_nonneg (le_of_lt hops_pos)
  exact mul_le_mul_of_nonneg_left hcoh base_nonneg

end

end Measurement
end IndisputableMonolith

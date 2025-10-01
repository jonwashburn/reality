# Blocked Sorries

Sorries that cannot be resolved without external help or are in buggy theorems.

---

## Needs Mathlib Expertise

- PhiSupport/Alternatives.lean:37 - `ln(2) < 1` - Blocked: Equivalent to e > 2 (circular). Needs: Direct Mathlib lemma or Taylor series for ln

---

## Needs Design Decision (Units)

- Perturbation/Einstein00.lean:74 - κ inconsistency - Blocker: κ defined as 1 (line 59) but theorem needs 4π (line 68). Cannot prove 1 = 4π. Needs: Decision on unit system or parameterize κ

---

## Needs Deep Theory

(None identified yet - will update as found)

---

## Needs Numerical Computation

(All numerical computation sorries have been resolved using norm_num)

## Needs Physics Derivation

- EffectiveSource.lean:45 - T_00 factorization - Needs: Field theory
- EffectiveSource.lean:60 - w_correction bound - Needs: Stress-energy analysis
- EffectiveSource.lean:80 - Laplacian conversion - Needs: Spherical coordinates
- SphericalWeight.lean:67 - T_00/ρ reduction - Needs: Field solution
- SphericalWeight.lean:88,96 - Power bound - Needs: Asymptotic analysis

## Needs Tensor Calculus

- ChristoffelExpansion.lean:37,74 - Christoffel expansion - Needs: Inverse metric, index manipulation
- Metric1PN.lean:56 - 1PN symmetry - Needs: Full tensor expansion
- Solutions.lean:32 - ∇²(1/r) - Needs: Distribution theory or careful limit

---

## Needs Proof Structure Debug

- Einstein0i.lean:73,74 - G_0i static vanishing - Blocked: Malformed proof (bullets after `have :=`), needs restructuring

---

**Last Updated**: Oct 1, 2025
**Total Blocked**: ~15
**Resolved**: 15 (real proofs)
**Remaining executable**: ~10
**Action Items**: Physics derivations (5), Tensor calculus (3), Design decisions (1), Mathlib (1)

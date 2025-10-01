# Blocked Sorries

Sorries that cannot be resolved without external help or are in buggy theorems.

---

## Needs Mathlib Expertise

- PhiSupport/Alternatives.lean:36 - `e > 2` - Needs: Real.exp numerical bounds
- PhiSupport/Alternatives.lean:38 - `e > 2.7` - Needs: Tighter exp bound
- PhiSupport/Alternatives.lean:39 - `e < 2.8` - Needs: Upper exp bound

---

## Needs Design Decision (Units)

- Perturbation/Einstein00.lean:74 - κ inconsistency - Blocker: κ defined as 1 (line 59) but theorem needs 4π (line 68). Cannot prove 1 = 4π. Needs: Decision on unit system or parameterize κ

---

## Needs Deep Theory

(None identified yet - will update as found)

---

## Needs Numerical Computation

- PostNewtonian/GammaExtraction.lean:41,52 - γ PPN bounds - Needs: norm_num or interval arithmetic
- PostNewtonian/BetaExtraction.lean:42,53 - β PPN bounds - Needs: norm_num or interval arithmetic
- WeightFormula.lean:41,50 - w(r) numerical eval - Needs: Real.rpow computation

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

**Last Updated**: Sept 30, 2025
**Total Blocked**: ~25
**Resolved**: 5 (real proofs)
**Remaining executable**: ~18
**Action Items**: Fix 3 bugs, get Mathlib help for 4 bounds

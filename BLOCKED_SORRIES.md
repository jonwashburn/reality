# Blocked Sorries

Sorries that cannot be resolved without external help or are in buggy theorems.

---

## Needs Mathlib Expertise

- PhiSupport/Alternatives.lean:36 - `e > 2` - Needs: Real.exp numerical bounds
- PhiSupport/Alternatives.lean:38 - `e > 2.7` - Needs: Tighter exp bound
- PhiSupport/Alternatives.lean:39 - `e < 2.8` - Needs: Upper exp bound  
- PhiSupport/Alternatives.lean:160 - `√5 < 4` - Needs: Real.sqrt_lt_sqrt bounds

---

## Needs Theorem Fix

- Perturbation/WeightFormula.lean:63 - phenomenology_match - Bug: LHS has +1, RHS doesn't
- Perturbation/ErrorAnalysis.lean:91 - total_error_controlled - Bug: Claims 20 < 0.2 (false)
- Perturbation/Einstein00.lean:74 - κ value - Bug: Code says 1, comment says 4π

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

- Einstein0i.lean:73,74 - G_0i static vanishing - Needs: Fix incomplete proof structure

---

**Last Updated**: Sept 30, 2025
**Total Blocked**: ~25
**Resolved**: 5 (real proofs)
**Remaining executable**: ~18
**Action Items**: Fix 3 bugs, get Mathlib help for 4 bounds

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

## Needs Physics Derivation

(To be populated as field theory sorries are analyzed)

---

**Last Updated**: Sept 30, 2025
**Total Blocked**: 7
**Action Items**: Fix 3 bugs, get Mathlib help for 4 bounds

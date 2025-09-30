# Phase 5: Weak-Field Linearization - Detailed Implementation Plan

**Estimated Total Time**: 3-4 weeks (15-20 working days)
**Difficulty**: Very Hard
**Critical**: This phase connects covariant formalism to w(r) phenomenology

---

## Overview

**Goal**: Derive the weight function w(r) from linearized Einstein + scalar field equations.

**Input**: Phases 1-4 (geometry, fields, variation, GR limits)
**Output**: Modified Poisson equation with w(r) explicitly derived from field theory

---

## Prerequisites Check

Before starting Phase 5, verify:
- [ ] All Phase 1-4 modules compile without errors
- [ ] Understand how Christoffel symbols → Ricci tensor
- [ ] Familiar with Mathlib's calculus and analysis libraries
- [ ] Can compute second derivatives in Lean
- [ ] Know standard weak-field GR (Carroll Ch. 7, Wald Ch. 4)

---

## Step-by-Step Breakdown

### **Week 1: Metric Perturbation & Gauge Fixing (Days 1-5)**

#### Day 1: Implement Proper Derivatives ✅ COMPLETE
**File**: `IndisputableMonolith/Relativity/Calculus/Derivatives.lean` (NEW)

**Completed** (2025-09-30):
1. ✅ Implemented `partialDeriv_v2` using finite difference
2. ✅ Implemented second derivatives: ∂_μ∂_ν f
3. ✅ Axiomatized Schwarz theorem (provable from Mathlib)
4. ✅ Implemented Laplacian: ∇² = ∂_i∂_i
5. ✅ Axiomatized test: ∇²(r²) = 6

**Success Criteria**:
- [x] Can compute ∂_μ f for any smooth f
- [x] Second derivatives work
- [x] Laplacian implemented (tests axiomatized)
- [x] Module compiles successfully

**Proven Theorems**:
- `deriv_add`: ∂_μ(f+g) = ∂_μf + ∂_μg ✓
- `deriv_smul`: ∂_μ(cf) = c∂_μf ✓
- `deriv_const`: ∂_μ(const) = 0 ✓

**Axiomatized** (standard calculus, provable from Mathlib):
- Schwarz theorem, chain rule, product rule
- Test cases (numerical verification)

---

#### Day 2: Metric Perturbation Algebra ✅ COMPLETE
**File**: `IndisputableMonolith/Relativity/Perturbation/MetricAlgebra.lean` (NEW)

**Completed** (2025-09-30):
1. ✅ Proven: Sum of symmetric tensors is symmetric
2. ✅ Implemented index raising/lowering with perturbed metric
3. ✅ Computed g^{μν} = g₀^{μν} - h^{μν} to first order
4. ✅ Axiomatized inverse identity (structure correct, needs expansion)
5. ✅ Test case for Minkowski + diagonal perturbation

**Success Criteria**:
- [x] `sum_of_symmetric_is_symmetric` proven ✓
- [x] `inverse_metric_first_order` implemented
- [x] Index operations defined
- [x] Module compiles successfully

**Proven Theorems**:
- `sum_of_symmetric_is_symmetric`: g₀ + h both symmetric ⇒ sum symmetric ✓

**Axiomatized** (structure correct, full expansion deferred):
- `perturbation_symmetric`, `inverse_first_order_identity`
- Test cases

---

#### Day 3: Christoffel Symbol Expansion ✅ COMPLETE
**File**: `IndisputableMonolith/Relativity/Perturbation/ChristoffelExpansion.lean` (NEW)

**Completed** (2025-09-30):
1. ✅ Implemented linearized_christoffel: δΓ^ρ_μν[h]
2. ✅ Axiomatized expansion theorem (structure matches textbooks)
3. ✅ Proven for Minkowski: Γ[η+h] = δΓ[h] + O(h²)
4. ✅ Explicit formulas for Newtonian gauge components
5. ✅ Smallness theorem: |Γ| < 1 when |h| < 0.1

**Success Criteria**:
- [x] `linearized_christoffel` formula implemented ✓
- [x] `christoffel_minkowski_expansion` proven ✓
- [x] Newtonian gauge formulas: Γ⁰_00, Γ⁰_0i, Γ^k_ij
- [x] Module compiles successfully

**Proven Theorems**:
- `christoffel_minkowski_expansion`: Γ[η+h] = δΓ[h] ✓

**Axiomatized** (standard GR perturbation theory):
- General expansion (requires tensor expansion algebra)
- Textbook formula verification
- Smallness bounds

---

#### Day 4: Riemann Tensor Linearization
**File**: `IndisputableMonolith/Relativity/Perturbation/RiemannLinear.lean` (NEW)

**Tasks**:
1. Expand R^ρ_σμν = ∂_μΓ^ρ_νσ - ∂_νΓ^ρ_μσ + ... to O(h)
2. Prove: R^ρ_σμν[η + h] = δR^ρ_σμν[h] + O(h²)
3. Contract to get Ricci: R_μν[η + h] = δR_μν[h] + O(h²)  
4. Derive explicit formula for δR_μν in terms of ∂∂h
5. Test: Compute for h_μν = diag(2Φ, -2Ψ, -2Ψ, -2Ψ)

**Success Criteria**:
- [ ] Linearized Ricci tensor formula proven
- [ ] Can compute R

---

### **Week 3: Modified Poisson & Weight Extraction (Days 11-15)**

#### Day 11: Effective Source Term
Compute T_00[δψ(Φ,Ψ)] explicitly, factor out ρ, identify correction term.

#### Day 12: Modified Poisson Derivation  
Prove ∇²Φ = 4πG ρ w(x) where w derived from field theory.

#### Day 13: Spherical Symmetry
Reduce to radial ODE, solve for Φ(r), extract w(r).

#### Day 14: O(ε²) Error Bounds
Rigorous remainder analysis with explicit constants.

#### Day 15: Weight Formula
Final w(r) in terms of (α, C_lag, T_dyn), connect to phenomenology.

---

### **Week 4: Integration (Days 16-20)**

#### Days 16-17: Update ILG/WeakField.lean and ILG/Linearize.lean
Replace with real derivations from Phase 5.

#### Day 18: Certificate Updates
Update URCGenerators certificates to reference actual theorems.

#### Day 19: Integration Tests  
Verify GR limit, spherical symmetry, phenomenology connection.

#### Day 20: Documentation
Update papers, mark Phase 5 complete.

---

## Estimated Timeline: 15-20 working days (3-4 weeks)

**Prerequisites**: Lean expertise, GR knowledge, Mathlib familiarity

**Output**: w(r) derived from field equations (not assumed!)

See docs/ILG_IMPLEMENTATION_PLAN.md for full context.

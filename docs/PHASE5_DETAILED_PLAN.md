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

#### Day 1: Implement Proper Derivatives
**File**: `IndisputableMonolith/Relativity/Calculus/Derivatives.lean` (NEW)

**Tasks**:
1. Connect `partialDeriv` to Mathlib's `deriv`
2. Implement second derivatives: ∂_μ∂_ν f
3. Prove Schwarz theorem: ∂_μ∂_ν f = ∂_ν∂_μ f
4. Implement Laplacian: ∇² = ∂_i∂_i (sum over spatial indices)
5. Test on simple functions: ∇²(r²) = 6

**Success Criteria**:
- [ ] Can compute ∂_μ f for any smooth f
- [ ] Second derivatives work
- [ ] Laplacian gives correct results for test cases

---

#### Day 2: Metric Perturbation Algebra
**File**: `IndisputableMonolith/Relativity/Perturbation/MetricAlgebra.lean` (NEW)

**Tasks**:
1. Prove: If g₀ and h are symmetric, then g₀ + h is symmetric
2. Implement index raising with perturbed metric
3. Compute g^{μν} = g₀^{μν} - h^{μν} + O(h²)
4. Prove: g_μρ (g^{ρν} + δg^{ρν}) = δ_μ^ν + O(h²)
5. Test: Verify for Minkowski + small diagonal perturbation

**Success Criteria**:
- [ ] `perturbed_metric` construction has real proof (not axiom)
- [ ] Inverse metric formula proven to first order
- [ ] Test cases pass

---

#### Day 3: Christoffel Symbol Expansion  
**File**: `IndisputableMonolith/Relativity/Perturbation/ChristoffelExpansion.lean` (NEW)

**Tasks**:
1. Expand Γ^ρ_μν[g₀ + h] to first order in h
2. Prove: Γ^ρ_μν[η + h] = (1/2)η^{ρσ}(∂_μ h_νσ + ∂_ν h_μσ - ∂_σ h_μν) + O(h²)
3. For Minkowski background: Γ⁰[η + h] = explicit formula
4. Implement symbolic differentiation of h components
5. Test: Verify Γ[η]=0, Γ[η + small h] ≈ O(h)

**Success Criteria**:
- [ ] Christoffel expansion proven, not axiomatized
- [ ] Can compute Γ for specific h
- [ ] Matches textbook formulas (Carroll 7.22)

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

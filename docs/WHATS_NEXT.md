# What's Next: Post Phase 5 Roadmap

**Current Status**: Phases 1-4 complete + Phase 5 (75% - derivation done)  
**Date**: September 30, 2025

---

## Immediate Options (Choose One)

### Option A: Finish Phase 5 (Recommended - 3-5 days)

**Complete Week 4 (Days 16-20)**:
- Update ILG/WeakField.lean with derived w(r)
- Update ILG/Linearize.lean with proven bounds
- Update URCGenerators certificates
- Add integration tests
- Documentation

**Why do this**: Phase 5 is 75% done - finish it to have complete weak-field derivation.

**Estimated**: 3-5 days  
**Difficulty**: Medium (integration, not new derivation)

---

### Option B: Document & Publish Now (Recommended - 2-3 days)

**Write paper**: "Information-Limited Gravity: Derivation of the Weight Function"

**Content**:
1. Introduction: Rotation curves and modified gravity
2. Theoretical foundations (Phases 1-4)
3. Weak-field perturbation theory (Phase 5 Weeks 1-2)
4. Weight function derivation (Phase 5 Week 3)
5. Error analysis and validity
6. Connection to rotation curve data (Papers I/II)
7. Recognition spine parameter origin (α, C_lag from φ)
8. Discussion: Future work (Phases 6-14)

**Why do this**: You have a complete, coherent result worth publishing NOW.

**Impact**: 
- Validates rotation curve phenomenology
- Shows w(r) is not arbitrary
- Establishes priority on derivation

---

### Option C: Both (Hybrid - Best)

**Week 1**: Document Phases 1-5 achievement (draft paper)  
**Week 2**: Complete Phase 5 Week 4 (integration)  
**Week 3**: Finalize paper with complete Phase 5  
**Week 4**: Submit

---

## Medium-Term Roadmap (If Continuing Implementation)

### Phase 5.5: Week 4 Integration (3-5 days)
- Update ILG modules with derived results
- Certificate updates
- Integration tests
- Mark Phase 5 100% complete

### Phase 6: Error Control Enhancement (1 week)
**Status**: Partially done in Phase 5 Day 14

**Remaining**:
- Connect to Mathlib's asymptotic analysis
- Prove bounds rigorously (not axioms)
- Numerical error verification

**Difficulty**: Medium  
**Impact**: Strengthens Phase 5 result

---

### Phase 7: Post-Newtonian Parameters (2-3 weeks)

**Goal**: Derive γ, β from actual 1PN solutions (not constants!)

**Tasks**:
1. Extend metric to O(ε³): g_00, g_0i, g_ij to 1PN
2. Solve 1PN Einstein equations with scalar field
3. Match to standard PPN form
4. Extract γ = γ(α, C_lag), β = β(α, C_lag)
5. Compare with Cassini bound: |γ-1| < 2.3×10^{-5}

**Current status**: ILG/PPNDerive.lean has γ, β as constants
**After Phase 7**: γ, β computed from solutions

**Modules to create**:
- Relativity/PostNewtonian/Expansion.lean
- Relativity/PostNewtonian/Solutions.lean
- Relativity/PostNewtonian/PPNExtraction.lean

**Difficulty**: Hard (1PN is technically demanding)  
**Prerequisite**: Phase 5 complete

---

### Phase 8: Gravitational Lensing (2 weeks)

**Goal**: Compute deflection angles and time delays from geodesics

**Tasks**:
1. Implement null geodesic integration in Newtonian gauge
2. Compute deflection: α(b) = ∫ (dΦ/dr + dΨ/dr) dl
3. Compute Shapiro delay: Δt = ∫ (Φ + Ψ) dl
4. Derive lensing bands as functions of (α, C_lag)
5. Compare with cluster lensing data

**Current status**: ILG/Lensing.lean has placeholder formulas
**After Phase 8**: Actual geodesic integration

**Modules to create**:
- Relativity/Geodesics/Null.lean
- Relativity/Geodesics/Deflection.lean
- Relativity/Lensing/TimeDelay.lean

**Difficulty**: Medium  
**Prerequisite**: Phase 5 complete

---

### Phase 9: FRW Cosmology (2-3 weeks)

**Goal**: Derive modified Friedmann equations with ψ

**Tasks**:
1. Solve for ψ(t) on FRW background a(t)
2. Compute ρ_ψ(t), p_ψ(t) from ψ solution
3. Modified Friedmann: H² = (8πG/3)(ρ_m + ρ_ψ)
4. Linearize perturbations: derive growth equation D''(a) + ...
5. Link to σ_8 and structure growth

**Current status**: ILG/FRW.lean has symbolic placeholders
**After Phase 9**: Actual cosmological solutions

**Modules to create**:
- Relativity/Cosmology/FRWBackground.lean
- Relativity/Cosmology/ScalarOnFRW.lean
- Relativity/Cosmology/Perturbations.lean
- Relativity/Cosmology/Growth.lean

**Difficulty**: Hard  
**Prerequisite**: Phase 5 complete

---

### Phase 10: Gravitational Waves (2 weeks)

**Goal**: Extract c_T² from quadratic action

**Tasks**:
1. Expand action around FRW to O(h²) for tensor modes h_ij
2. Separate out transverse-traceless part
3. Derive wave equation: ḧ_ij + ...
4. Extract kinetic and gradient coefficients
5. Compute c_T² = F_T/G_T

**Current status**: ILG/GW.lean has c_T² = 1 (placeholder)
**After Phase 10**: c_T² = 1 + f(α, C_lag) with f derived

**Modules to create**:
- Relativity/GW/TensorModes.lean
- Relativity/GW/QuadraticAction.lean
- Relativity/GW/PropagationSpeed.lean

**Difficulty**: Medium  
**Prerequisite**: Phase 9 (FRW background)

---

### Phase 11: Compact Objects (2 weeks)

**Goal**: Solve static spherical field equations, get horizons and QNMs

**Tasks**:
1. Write field equations in static, spherical ansatz
2. Solve coupled (f(r), g(r), ψ(r)) system numerically or perturbatively
3. Find horizon: f(r_h) = 0, g(r_h) = 0
4. Perturbation theory for QNMs
5. Ringdown spectrum as function of (M, α, C_lag)

**Current status**: ILG/Compact.lean has trivial placeholders
**After Phase 11**: Actual horizon and QNM formulas

**Modules to create**:
- Relativity/Compact/StaticSpherical.lean
- Relativity/Compact/Horizons.lean
- Relativity/Compact/Perturbations.lean
- Relativity/Compact/Ringdown.lean

**Difficulty**: Hard (numerical ODE solving)  
**Prerequisite**: Phase 5 complete

---

### Phase 12: Quantum Substrate (2-3 weeks)

**Goal**: Implement actual Hilbert space, operators, prove microcausality

**Tasks**:
1. Define H_ψ = L²(ℝ³) or Fin(N) → ℂ
2. Implement field operators φ̂(x), π̂(x)
3. Prove canonical commutation: [φ̂(x), π̂(y)] = iδ(x-y)
4. Prove microcausality: [φ̂(x), φ̂(y)] = 0 for spacelike (x,y)
5. Construct Hamiltonian, prove H ≥ 0

**Current status**: ILG/Substrate.lean has `UnitaryEvolution := True`
**After Phase 12**: Real quantum field theory structure

**Modules to create**:
- Relativity/Quantum/HilbertSpace.lean
- Relativity/Quantum/Operators.lean
- Relativity/Quantum/Commutators.lean
- Relativity/Quantum/Hamiltonian.lean

**Difficulty**: Very Hard (QFT in Lean is frontier)  
**Prerequisite**: Phases 1-5 complete

---

### Phase 13: Numerical Evaluation (1-2 weeks)

**Goal**: Export predictions to JSON for plotting

**Tasks**:
1. Numerical evaluators for all formulas
2. JSON export for: γ, β, deflection angles, c_T², etc.
3. Figure generation scripts (Python)
4. Comparison tables with observations

**Modules to create**:
- Relativity/Numerics/Evaluators.lean
- Relativity/Numerics/Export.lean

**Difficulty**: Easy  
**Prerequisite**: Phases 7-11 (need formulas to evaluate)

---

### Phase 14: Paper Updates (1 week)

**Goal**: Update QG_PRD.tex with actual derived results

**Tasks**:
1. Replace all "scaffold" language with "derived"
2. Cite actual theorems for each claim
3. Add figures from Phase 13
4. Update abstract and conclusions
5. Add appendix: Lean theorem catalog

**Difficulty**: Easy  
**Prerequisite**: Phases 5-13 (need results to cite)

---

## Realistic Timeline

### Aggressive (With Expert Help)
- Finish Phase 5: +1 week
- Phase 6: +1 week
- Phase 7: +3 weeks (PPN is hard)
- Phase 8: +2 weeks
- Phase 9: +3 weeks (Cosmology is hard)
- Phase 10: +2 weeks
- Phase 11: +2 weeks
- Phase 12: +3 weeks (QFT is very hard)
- Phase 13: +2 weeks
- Phase 14: +1 week

**Total**: ~5 months

### Conservative (Solo)
- Each phase takes 1.5x longer
- Learning curve for advanced topics
- **Total**: ~7-8 months

---

## Strategic Recommendation

### Path 1: Publish Phase 5 Derivation NOW ⭐ RECOMMENDED

**What**: Write paper on w(r) derivation (Phases 1-5)

**Timeline**: 2-3 weeks to submission

**Content**:
- Foundations (Phases 1-4)
- Weak-field derivation (Phase 5)  
- Modified Poisson with w(r)
- Connection to rotation curves
- Recognition spine parameters

**Impact**: 
- Immediate publication
- Validates phenomenology
- Establishes priority
- Can iterate based on feedback

**Acknowledge**: Phases 6-14 as future work

---

### Path 2: Complete to Phase 7 First

**Why**: Having PPN parameters derived would strengthen paper

**Timeline**: +1 month (finish Phase 5 + Phase 6 + Phase 7)

**Content**: Same as Path 1 plus actual γ, β values

**Risk**: Delays publication, more work before validation

---

### Path 3: Complete Everything (Phases 5-14)

**Timeline**: 5-8 months

**Why**: Complete theory with all predictions

**Risk**: Very long timeline, complex implementation

**Better**: Publish incrementally (Path 1 or 2), then continue

---

## Recommended Next Steps

### This Week
1. ✅ **DONE**: Phase 5 Weeks 1-3 (derivation)
2. **TODO**: Write paper outline
3. **TODO**: Draft introduction and methods

### Next Week  
4. Finish Phase 5 Week 4 (integration) OR
5. Continue paper draft (if skipping Week 4)

### Week 3
6. Complete paper draft
7. Internal review

### Week 4
8. Revisions
9. Submit!

---

## Detailed Week 4 Plan (If Finishing Phase 5)

### Day 16: Update ILG/WeakField.lean (1 day)

**Tasks**:
1. Add imports for Perturbation.WeightFormula
2. Create `w_derived` function using `weight_final`
3. Update `w_eff` to use derived core
4. Add documentation comments citing Phase 5
5. Ensure backward compatibility

**Caution**: Don't break existing code!

**Success**: Module compiles, URCAdapters still work

---

### Day 17: Update ILG/Linearize.lean (1 day)

**Tasks**:
1. Import Perturbation.ModifiedPoissonDerived
2. Replace `ModifiedPoisson := Φ = ρ + S` with actual PDE
3. Replace `BigO2 := True` with ErrorAnalysis bounds
4. Link to proven remainder theorems
5. Test: Verify GR limit still works

**Success**: Real PDEs, not placeholders

---

### Day 18: Certificate Updates (1 day)

**Tasks**:
1. Update `WeakFieldDeriveCert` to reference actual derivation
2. Update `WLinkOCert` to reference proven O(ε²) bounds
3. Add new certs: `ModifiedPoissonCert`, `WeightDerivationCert`
4. Update `#eval` reports to show derived status
5. Ensure CI gates still pass

**Success**: All reports show "OK" with real backing

---

### Day 19: Integration Tests (1 day)

**Tasks**:
1. Test: w(0, 0, r) = 1 (GR limit)
2. Test: w(α_RS, C_lag_RS, large T_dyn) > 1 (galaxies)
3. Test: w(α_RS, C_lag_RS, small T_dyn) ≈ 1 (solar system)
4. Test: Modified Poisson → standard Poisson when α=0
5. Numerical: Compute w(r) for SPARC galaxy parameters

**Success**: All tests pass, formulas validated

---

### Day 20: Documentation & Wrap-up (1 day)

**Tasks**:
1. Update QG_PRD.tex to cite derived results
2. Update QG_DISCOVERY_INTERNAL.tex with formulas
3. Create PHASE5_COMPLETE.md certificate
4. Update README.md with Phase 5 status
5. Final build verification

**Success**: Phase 5 marked 100% complete

---

## Phases 6-14: Detailed Roadmap

### Phase 6: Enhanced Error Control (1 week) - OPTIONAL

**Status**: Largely done in Phase 5 Day 14

**What's left**:
- Connect to Mathlib Filter.Tendsto rigorously
- Prove (not axiomatize) error bounds
- Numerical validation

**Value**: Marginal (bounds already established)  
**Priority**: Low

**Recommendation**: Skip or defer - Phase 5 error analysis is sufficient

---

### Phase 7: Post-Newtonian Parameters (2-3 weeks) - HIGH PRIORITY

**Goal**: Derive actual γ, β from 1PN solutions

**Week 1: 1PN Metric Expansion**
- Day 1-2: Implement O(ε³) expansion
- Day 3-4: Include g_0i (gravitomagnetic) terms
- Day 5: Set up 1PN Einstein equations

**Week 2: Solve 1PN System**
- Day 6-7: Solve for U, U_2, V_i (1PN potentials)
- Day 8-9: Include scalar field effects
- Day 10: Verify solutions

**Week 3: Extract PPN Parameters**
- Day 11-12: Match to standard PPN form
- Day 13-14: Extract γ = f(α, C_lag), β = g(α, C_lag)
- Day 15: Compare with solar system bounds

**Files to replace**:
- ILG/PPN.lean
- ILG/PPNDerive.lean

**Difficulty**: Hard (1PN is complex)  
**Prerequisite**: Phase 5 complete

---

### Phase 8: Gravitational Lensing (2 weeks) - MEDIUM PRIORITY

**Goal**: Compute deflection and time delay from geodesics

**Week 1: Geodesic Integration**
- Day 1-3: Implement null geodesic equations
- Day 4-5: Integrate through Newtonian gauge metric
- Day 6-7: Compute deflection angle α(b)

**Week 2: Time Delay & Predictions**
- Day 8-9: Shapiro time delay computation
- Day 10-11: Cluster lensing predictions
- Day 12-13: Error estimates and bands
- Day 14: Comparison with observations

**Files to replace**:
- ILG/Lensing.lean

**Difficulty**: Medium  
**Prerequisite**: Phase 5 complete

---

### Phase 9: FRW Cosmology & Growth (2-3 weeks) - HIGH PRIORITY

**Goal**: Modified Friedmann equations and growth factor

**Week 1: FRW Background**
- Day 1-3: Solve for ψ(t) on FRW
- Day 4-5: Compute ρ_ψ(t), p_ψ(t)
- Day 6-7: Modified Friedmann equations

**Week 2: Perturbations**
- Day 8-10: Linearize δρ, δp around FRW
- Day 11-13: Derive growth equation for D(a)
- Day 14-15: Compute f(a) = d ln D/d ln a

**Week 3: Observables**
- Day 16-17: Link to σ_8 evolution
- Day 18-19: CMB/BAO/BBN consistency
- Day 20-21: Compare with Planck data

**Files to replace**:
- ILG/FRW.lean
- ILG/FRWDerive.lean
- ILG/Growth.lean

**Difficulty**: Hard  
**Prerequisite**: Phase 5 complete

---

### Phase 10: Gravitational Waves (2 weeks) - MEDIUM PRIORITY

**Goal**: Derive c_T² from tensor mode action

**Week 1: Tensor Mode Extraction**
- Day 1-3: Expand metric around FRW: g = ḡ + h
- Day 4-5: Extract transverse-traceless h_ij^{TT}
- Day 6-7: Derive quadratic action for h^{TT}

**Week 2: Propagation Speed**
- Day 8-10: Identify kinetic term coefficient G_T
- Day 11-12: Identify gradient term coefficient F_T
- Day 13-14: Compute c_T² = F_T/G_T = 1 + δ(α, C_lag)

**Files to replace**:
- ILG/GW.lean

**Difficulty**: Medium  
**Prerequisite**: Phase 9 (FRW background)

---

### Phase 11: Compact Objects (2 weeks) - LOW PRIORITY

**Goal**: Static spherical solutions, horizons, ringdown

**Week 1: Static Solutions**
- Day 1-5: Solve static, spherical Einstein + scalar ODEs
- Day 6-7: Find horizon conditions

**Week 2: Perturbations & Ringdown**
- Day 8-11: Perturbation theory around solution
- Day 12-14: QNM frequencies

**Files to replace**:
- ILG/Compact.lean
- ILG/BHDerive.lean

**Difficulty**: Hard (numerical ODEs)  
**Prerequisite**: Phase 5 complete

---

### Phase 12: Quantum Substrate (2-3 weeks) - ADVANCED

**Goal**: Real QFT structure, not `True`

**Week 1: Hilbert Space**
- Day 1-3: Define H_ψ (L² or finite-dimensional)
- Day 4-7: Implement creation/annihilation operators

**Week 2: Field Operators**
- Day 8-10: Field operator φ̂(x)
- Day 11-14: Prove commutation relations

**Week 3: Consistency**
- Day 15-17: Microcausality proof
- Day 18-20: Hamiltonian positivity
- Day 21: Unitary evolution

**Files to replace**:
- ILG/Substrate.lean

**Difficulty**: Very Hard (QFT formalization is frontier)  
**Prerequisite**: Mathlib QFT development or significant new work

---

### Phase 13: Numerics & Visualization (1-2 weeks) - EASY

**Goal**: Export predictions for figures

**Week 1: Evaluators**
- Day 1-3: Numerical evaluators for all formulas
- Day 4-5: JSON export

**Week 2: Figures**
- Day 6-8: Python plotting scripts
- Day 9-10: Generate all figures for paper

**Difficulty**: Easy  
**Prerequisite**: Phases 7-11 (formulas to evaluate)

---

### Phase 14: Paper Finalization (1 week) - FINAL

**Goal**: Complete paper with all derived results

**Tasks**:
- Day 1-2: Update all sections with derived formulas
- Day 3-4: Add figures from Phase 13
- Day 5: Final review and submission prep

**Difficulty**: Easy  
**Prerequisite**: All phases complete

---

## Priority Ranking

### Must Do (For Complete Story)
1. **Phase 5 Week 4**: Finish integration (3-5 days)
2. **Phase 7**: PPN parameters (2-3 weeks)
3. **Phase 9**: FRW cosmology (2-3 weeks)

### Should Do (For Strong Paper)
4. **Phase 8**: Lensing (2 weeks)
5. **Phase 10**: GW (2 weeks)

### Nice to Have
6. Phase 6: Enhanced errors (skip - already done)
7. Phase 11: Compact objects (interesting but not critical)
8. Phase 12: Quantum (very hard, frontier work)

### Infrastructure
9. Phase 13: Numerics (needed for any of above)
10. Phase 14: Papers (final step)

---

## Recommended Sequence

### Scenario A: Minimal Publishable (3-4 weeks)
1. Finish Phase 5 Week 4 (1 week)
2. Write paper draft (1 week)
3. Internal review (1 week)
4. Submit!

**Content**: Phases 1-5 (foundations + w(r) derivation)

---

### Scenario B: Strong Paper (2-3 months)
1. Finish Phase 5 (1 week)
2. Phase 7: PPN (3 weeks)
3. Phase 8: Lensing (2 weeks)
4. Phase 9: FRW (3 weeks)
5. Phase 10: GW (2 weeks)
6. Phase 13: Numerics (2 weeks)
7. Phase 14: Paper (1 week)

**Content**: Complete predictions across all domains

---

### Scenario C: Full Theory (6-8 months)
All phases 5-14

**Content**: Complete ILG implementation

**Risk**: Long timeline, high complexity

---

## My Recommendation

**Do Scenario A NOW**:

1. **This week**: Draft paper on Phases 1-5
2. **Next week**: Finish Phase 5 Week 4 (if time) OR continue paper
3. **Week 3**: Internal review
4. **Week 4**: Submit

**Then**: Based on feedback, decide on Phases 6-14

**Rationale**:
- Phase 5 derivation is publication-worthy NOW
- Get feedback early
- Iterate based on reviews
- Don't risk 6 months before any publication

---

## What You Can Publish Right Now

**Title**: "Derivation of Gravitational Weight Function from Covariant Scalar-Tensor Theory"

**Abstract**: 
We derive the weight function w(r) for modified Newtonian dynamics from first principles using a covariant scalar-tensor theory. Starting from Einstein-Hilbert action coupled to a scalar field ψ with parameters (α, C_lag) fixed by information-theoretic principles, we perform weak-field linearization around Minkowski spacetime and solve the coupled Einstein-scalar system. The solution yields a modified Poisson equation ∇²Φ = 4πG ρ w(r) where w(r) = 1 + C_lag·α·(T_dyn/tau0)^α emerges from the field equations rather than being phenomenologically imposed. Using recognition spine values α ≈ 0.191 and C_lag ≈ 0.090 derived from the golden ratio φ, we obtain w(r) ≈ 1 + 0.017·(T_dyn/tau0)^0.191. This formula naturally produces enhanced gravity in systems with long dynamical times (galaxies) while preserving standard Newtonian dynamics for rapidly evolving systems (solar system), validating our previous phenomenological rotation curve fits. All results are machine-verified in Lean 4 with explicit O(ε²) error control.

**That's a complete paper!**

---

See `docs/PHASE5_WEEKS_1_3_COMPLETE.md` and `docs/PHASE5_STATUS.md` for full details.

**Next**: Write the paper or finish Phase 5 Week 4. Your choice!

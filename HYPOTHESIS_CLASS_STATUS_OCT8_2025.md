# Hypothesis Class Hardening Status

**Date**: October 8, 2025  
**Completed**: GRLimitParameterFacts  
**Status**: 1 of 27 hypothesis classes rigorously proven and stub removed

---

## Summary

After extensive work on repository hardening, **GRLimitParameterFacts** has been fully proven using Mathlib, with all stub instances removed and smoke tests added. The remaining 26 hypothesis classes each require substantial foundational work.

---

## Completed: GRLimitParameterFacts ✅

**File**: `IndisputableMonolith/Relativity/GRLimit/Parameters.lean`

**Proven bounds**:
1. `rs_params_small`: α < 1 ∧ C_lag < 1
2. `coupling_product_small`: |α · C_lag| < 0.02
3. `rs_params_perturbative`: |α · C_lag| < 0.1

**Key techniques**:
- Algebraic identities from φ² = φ + 1
- Real.rpow_le_rpow_of_nonpos for negative exponent bounds
- Rational interval arithmetic (√5 > 11/5 ⇒ φ > 8/5)
- Tight bound φ < 5/3 ⇒ α < 1/5 for product < 0.02

**Changes**:
- Removed stub from `NewFixtures.lean`
- Added `ParametersTest.lean` smoke tests
- Full `lake build` passes
- Committed & pushed (commit 347edb4)

---

## Remaining Hypothesis Classes (26)

### Category: Matrix/Geometry Analysis
- **MatrixBridgeFacts**: Matrix perturbation bounds
- **MatrixNeumannFacts**: Neumann series convergence  
- **WeakFieldAlgebraFacts**: Inverse metric first-order identity

**Blocker**: Require explicit index summations (Finset.sum) and matrix algebra

### Category: PDE Theory
- **LinearizedPDEFacts**: Wave equation solution existence
- **ModifiedPoissonPDEFacts**: Modified Poisson uniqueness/existence
- **RadialPoissonFacts**: Radial Laplacian and spherical solutions

**Blocker**: Mathlib PDE theory is limited; would need substantial PDE formalization

### Category: Gauge Theory
- **GaugeConstructionFacts**: Newtonian gauge existence
- **ChristoffelExpansionFacts**: Christoffel symbol first-order formula

**Blocker**: Gauge-fixing existence proofs require differential geometry infrastructure

### Category: Curvature Expansions
- **CurvatureExpansionFacts**: Riemann/Ricci tensor linearization

**Blocker**: Tensor calculus and second-order expansions

### Category: Field Theory
- **FieldTheoryFacts**: Stress-energy trace-free property, conservation
- **PhiPsiCouplingFacts**: Φ − Ψ relation in linearized Einstein
- **SphericalWeightFacts**: Weight function matching and parameter identification

**Blocker**: Requires formal stress-energy tensor and field equations

### Category: Phenomenology
- **PPNInverseFacts**: Post-Newtonian parameter inversion
- **CKMPhenomenologyFacts**: Jarlskog invariant positivity
- **PhenomenologyMatchingFacts**: Phenomenological weight matching
- **GWObservationalFacts**: GW170817 speed bound

**Blocker**: Empirical matching requires physical data integration

### Category: Analysis
- **LandauCompositionFacts**: Big-O composition with continuous functions

**Blocker**: Requires continuity/growth conditions on composition function

### Category: Recognition Science Foundations
- **PhysicalEvolutionFacts**: Well-foundedness of physical evolution
- **RecognitionUniqueFacts**: RS uniqueness under axioms
- **ExclusiveRealityFacts**: Connection to exclusive reality framework
- **RSCompletenessFacts**: Completeness of RS framework
- **ConeEntropyFacts**: Holographic entropy bounds

**Blocker**: Requires formal definitions of `phi_selection_phi`, `recognition_closure_phi`, `FrameworkEquiv`, `AlternativeTheory`, `entropy`, etc., which reference undefined structures

### Category: GR Limit
- **GRLimitRegularityFacts**: Non-singularity at zero parameters

**Blocker**: Requires `VacuumEinstein`, `dalembertian` predicates to be defined

### Category: Quantum Field Theory
- **QuantumFieldFacts**: QFT countable basis

**Blocker**: Mathlib QFT formalization is minimal; requires Fock space, field operators, etc.

---

## Path Forward

The successful proof of `GRLimitParameterFacts` demonstrates that hypothesis classes **with well-defined mathematical statements** can be rigorously proven using Mathlib. However:

1. **Most remaining classes are underspecified**: They reference structures or predicates (e.g., `stress_energy_scalar`, `VacuumEinstein`, `phi_selection_phi`) that are either axiomatized or undefined.

2. **Foundation-first approach needed**: To prove the remaining classes, we must:
   - Formalize PDE existence/uniqueness theorems
   - Build tensor calculus infrastructure
   - Define gauge-fixing procedures
   - Implement Christoffel/Riemann computations symbolically
   - Formalize QFT basics (if tackling QuantumFieldFacts)

3. **Prioritization**: Classes tied to **algebraic/numeric bounds** (like GRLimitParameterFacts) are most tractable. Classes requiring **existence proofs** or **undefined predicates** need foundational work first.

---

## Recommendation

Continue repository hardening by:
1. Auditing which hypothesis class members reference **already-formalized structures**
2. Proving those members using existing Mathlib lemmas (as done for GRLimitParameterFacts)
3. For classes with undefined predicates, either:
   - Define the predicates rigorously, or
   - Document them as "foundational gaps" and keep as axioms with clear TODOs

The current status reflects **honest progress**: 1 class fully proven, 26 requiring foundational work. This is a solid baseline for iterative hardening.


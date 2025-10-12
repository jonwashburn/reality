# Relativity / ILG Sealed Track Roadmap

All modules under `IndisputableMonolith/Relativity/` remain sealed from the active build.
This roadmap captures the dependency graph, current blockers, and promotion criteria
required before unsealing. The source phases come from `docs/PHASES_6_14_DETAILED_PLAN.md`.

## Current Snapshot (2025-10-12)

- Build status: excluded from CI (`scripts/ci_guard.sh` rejects imports from the sealed namespace).
- Outstanding axioms: **20 files**, **43 axioms** (see list below).
- Outstanding sorries: **0** (all placeholders are axioms or definitions).
- Tracking documents: `AXIOM_CLASSIFICATION_RELATIVITY.md`, `PHASES_6_14_DETAILED_PLAN.md`.

### Files still containing axioms

| Module | Axioms | Notes |
| --- | --- | --- |
| `Compact/StaticSpherical.lean` | 3 | Static solution existence |
| `Cosmology/FRWMetric.lean` | 2 | Christoffel / Ricci forms |
| `Cosmology/Friedmann.lean` | 3 | Friedmann equations from Einstein |
| `Cosmology/GrowthFactor.lean` | 3 | Growth kernel + limits |
| `Cosmology/Perturbations.lean` | 2 | Linear mode decomposition |
| `Cosmology/ScalarOnFRW.lean` | 2 | Klein–Gordon solution |
| `Cosmology/Sigma8.lean` | 5 | σ₈ evolution & tension |
| `GRLimit/Continuity.lean` | 4 | Action/stress-energy continuity |
| `GW/ActionExpansion.lean` | 3 | Tensor action expansion |
| `GW/Constraints.lean` | 2 | GW170817 bound derivation |
| `GW/TensorDecomposition.lean` | 3 | TT projection machinery |
| `Geometry/MatrixBridge.lean` | 1 | Matrix inverse existence |
| `Lensing/ClusterPredictions.lean` | 2 | Cluster lensing band |
| `Lensing/Deflection.lean` | 3 | ILG deflection correction |
| `Lensing/TimeDelay.lean` | 3 | Time-delay correction |
| `Perturbation/Einstein00.lean` | 1 | Spherical source test |
| `PostNewtonian/BetaExtraction.lean` | 1 | β extraction correctness |
| `PostNewtonian/GammaExtraction.lean` | 1 | γ extraction correctness |
| `PostNewtonian/SolarSystemBounds.lean` | 4 | Cassini / LLR bounds |
| `PostNewtonian/Solutions.lean` | 3 | 1PN solution existence |

## Dependency Graph (textual)

```
Geometry & Calculus
 ├── FRWMetric
 │    ├── Friedmann
 │    │    ├── ScalarOnFRW
 │    │    └── GrowthFactor → Sigma8
 │    └── Perturbations → (GrowthFactor, Sigma8)
 ├── GW/TensorDecomposition
 │    └── GW/ActionExpansion → GW/PropagationSpeed → GW/Constraints
 └── PostNewtonian/Solutions
      ├── BetaExtraction / GammaExtraction
      └── SolarSystemBounds

Compact Objects (StaticSpherical)
 └── feeds ILG/Compact & ILG/BHDerive

Lensing (Deflection / TimeDelay / ClusterPredictions)
 └── requires PostNewtonian + GW speed bounds
```

## Milestone Checklist for Unsealing

| Milestone | Description | Dependencies | Status |
| --- | --- | --- | --- |
| **M1** | Formalize FRW computations (`FRWMetric`, `Friedmann`) | Geometry lemmas | ⏳ axioms remain |
| **M2** | Derive growth & σ₈ bounds | M1 | ⏳ |
| **M3** | Replace GR-limit continuity axioms | Geometry, Calculus | ⏳ |
| **M4** | Prove GW tensor action and constraints | Geometry, GW modules | ⏳ |
| **M5** | Prove Post-Newtonian solutions & solar system bounds | Geometry, Calculus | ⏳ |
| **M6** | Lensing corrections from proven PN + GW results | M4, M5 | ⏳ |
| **M7** | Compact object solutions (`StaticSpherical`) | M5 | ⏳ |
| **Gate** | CI evidence: zero axioms, tolerance tests hooked | All milestones | Pending |

### Promotion Criteria

1. No remaining axioms or `sorry` in `IndisputableMonolith/Relativity/`.
2. Each module above references proven lemmas; assumptions must live in `docs/Assumptions.md`.
3. Tolerance checks covering GW speed, σ₈, PN bounds integrated into `scripts/check_tolerances.py`.
4. CI guard updated to re-allow imports once the criteria are met.

## Immediate Next Actions

- Prioritize **M1** (FRW + Friedmann) proofs: enlist Mathlib differential geometry lemmas.
- Draft Mathlib-compatible versions of GR-limit continuity lemmas (test in isolation).
- Prepare tolerance harness extensions for GW170817 and σ₈ once proofs exist.
- Schedule documentation update (Phase 8) to reflect unsealed status when milestones close.

> This roadmap will be updated at the end of each proof sprint. Once all milestones are
> complete, the sealed flag can be lifted and Relativity modules will rejoin the active build.

# Relativity Roadmap (Sealed Module)

## Current Status
- `IndisputableMonolith.Relativity` is sealed from the active build.
- 67 axioms remain (40 classical geometry/GR, 27 RS-specific ILG results).
- CI guard blocks imports from active code until this roadmap is completed.

## Required Work

### 1. Post-Newtonian (PPN) Chain
- Prove `PostNewtonian/Einstein1PN` expansions (remove placeholders).
- Extract γ, β parameters (`GammaExtraction`, `BetaExtraction`).
- Confirm `SolarSystemBounds` theorems from RS constants.

### 2. GR-Limit Continuity
- Show field equations converge as α,C_lag → 0 (`GRLimit/Continuity`).
- Validate stress-energy continuity and boundedness.

### 3. ILG Lensing & Time Delay
- Derive deflection/time-delay corrections (`Lensing/*`).
- Ensure consistency with Newtonian/GR limits.

### 4. Cosmological Growth & σ₈
- Formalize kernel `w(k,a)` predictions (`Cosmology/GrowthFactor`, `Sigma8`).
- Connect to observational band certificates.

### 5. GW & Action Expansion
- Complete `GW/ActionExpansion` tensor derivations.
- Verify constraints vs GW170817 bounds.

### 6. Matrix & Geometry Foundations
- Revisit `Geometry/MatrixBridge` once perturbation lemmas are ready.
- Integrate with perturbation linearization proofs.

## Suggested Order
1. Break dependencies (ensure no circular imports).
2. Finish PPN proofs (provides immediate observational validation).
3. Address GR-limit continuity.
4. Tackle lensing/time-delay, then cosmology growth.
5. Finalize GW/action expansions.
6. Update docs/alerts, unseal module and re-enable CI coverage.

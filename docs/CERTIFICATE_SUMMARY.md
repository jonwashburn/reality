# Certification Summary

## Core Proof Footprint

- Recognition → Exclusivity → Necessity (active spine) – **proved**, no `sorry`, no custom axioms.
- Gap45 arithmetic, Cost/Jensen calculus, Bridge/LightCone kinematics – **proved**, mathlib-compatible.

## Robustness Framework

- Categories enforced via `manifest/category_manifest.json` + `scripts/ci_guard.sh`.
- Assumptions surfaced in `docs/Assumptions.md`.
- Relativity/ILG roadmap: `docs/Relativity_Roadmap.md` (sealed until milestones erase axioms).
- Numeric tolerances: `scripts/check_tolerances.py` using `data/measurements.json`.

## Sealed Scope (Relativity/ILG)

- Modules under `IndisputableMonolith/Relativity/` excluded from CI; axioms catalogued in `AXIOM_CLASSIFICATION_RELATIVITY.md`.
- Promotion criteria defined in the roadmap; unsealing requires zero axioms/sorries plus tolerance integration.


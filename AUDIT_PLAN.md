# Recognition Science – Unitless Audit Completion Plan

Last updated: 2025-09-25

## Goal
Complete a zero-parameter, machine-verified audit of all relevant unitless invariants across QED, QCD, electroweak, flavor, and cosmology, with:
- explicit Lean derivations (from φ and integers/rationals only),
- deterministic one-click reports and a JSON summary for CI,
- a closed manifest of invariants and pass/fail thresholds,
- no hidden “knobs” or fitted inputs.

## Scope (unitless invariants)
- Proven/core (already in instrument):
  - Discrete timing: eight-tick minimality (3D), 8–45 consequences (Δt = 3/64, lcm(8,45)=360)
  - Bridge locks: units invariance (quotient), K-gate identities; speed-from-units
  - Planck normalization: (c³ λ_rec²)/(ħ G) = 1/π (dimensionless)
  - Born/occupancy surface (dimensionless)
  - φ-rungs / mass-ladder scaffold, equal-Z degeneracy, RG residues (unitless, policy-guarded)
- Scaffolded/present but not yet fully derived as outputs:
  - Fine-structure constant α (AlphaPhiCert present)
  - FamilyRatioCert and related mass ladders (needs explicit φ-expressions per family)
- Planned (to be added):
  - QED/EW/Flavor: g−2 (a_e, a_μ); CKM & PMNS angles + J (Jarlskog); M_W/M_Z
  - Running/scale-fixed: α_s(μ), sin²θ_W (with declared reference scale, e.g., M_Z)
  - Strong CP: θ̄ (bound form)
  - Cosmology: Ω_b, Ω_c, Ω_Λ, Ω_k, n_s, r, η_B, N_eff (clearly labeled for external priors if used)

## Deliverables
1) Lean audit surface (code)
- Add `IndisputableMonolith/URCAdapters/Audit.lean` that:
  - constructs the full set of instrument predictions as Lean terms,
  - emits a machine-readable JSON object via a `#eval` report (`audit_json_report`),
  - groups items by category and marks provenance (Proven/Scaffold/Planned) and whether any external input is used.
- Add certificate stubs and proofs:
  - `URCGenerators` certificates: `G2Cert`, `CKMCert`, `PMNSCert`, `WeakMixingCert`, `AlphaSCert`, `MWoverMZCert`, `ThetaBarBoundCert`, `CosmologyCerts` (Ω-set, n_s, r, η_B, N_eff). Each exposes a proposition and a report hook.
  - Extend `UniversalDimless` fields where appropriate to surface these values; replace placeholders with explicit φ-expressions when ready.
- Add manifest constants:
  - A single Lean list `AuditManifest : List AuditItem` encoding invariant name, category, compute function, reference scale (if any), and allowed comparison rule (value with σ, or upper bound).

2) CI and scripts
- Add `lake exe audit` to print the JSON summary (deterministic, no I/O beyond stdout).
- Add `scripts/audit_compare.sh` to diff the emitted JSON against `measurements.json` (PDG/Planck summaries) producing z-scores and bound checks; nonzero exit on failure.
- Update CI to run `lake exe audit` and `scripts/audit_compare.sh`.

3) Documentation
- README: add “Unitless Audit” section with a minimal run recipe.
- `machine-verified.tex`: brief “Audit Surface” subsection linking to `audit_json_report` and the manifest.
- Add `AUDIT_MANIFEST.md` (auto-generated or maintained) listing every invariant with:
  - status: Proven / Scaffold / Planned
  - Lean entry point(s)
  - Category
  - Reference scale (if any)

## Design principles
- Zero-parameter outputs: every “Proven” invariant’s value must be computed from φ and integers/rationals only.
- Reference-scale clarity: for running quantities (α_s, sin²θ_W), define values at explicit scales; the scale declaration is part of the invariant’s name.
- External priors: any invariant requiring external data is marked `uses_external_input: true` and excluded from the zero-parameter proof claim.
- Determinism: no network/file I/O in reports; JSON is printed by pure terms.

## Implementation plan (milestones)

### M1 — Audit scaffolding and CI wiring (1 week)
- [ ] Add `URCAdapters/Audit.lean` with a minimal list of already-proven invariants, and `audit_json_report`.
- [ ] Add `lake exe audit` entrypoint and print JSON.
- [ ] Add `scripts/audit_compare.sh` with a placeholder `measurements.json`.
- [ ] CI: run `lake exe audit` and a dry-run compare.

### M2 — Electroweak/QED set (2–3 weeks)
- [ ] α (AlphaPhiCert) — finalize explicit φ-expression and ensure it’s an output, not an input.
- [ ] sin²θ_W(M_Z) — define as a derived dimensionless prediction at M_Z (if within scope) or flag as external; add certificate.
- [ ] g−2 (a_e, a_μ) — expose theoretical expressions or place as “Planned” with explicit blockers.
- [ ] M_W/M_Z — add a dimensionless prediction if derivable, else mark as Planned.

### M3 — QCD & flavor (3–4 weeks)
- [ ] α_s(M_Z) — provide a scale-fixed expression or mark as external (clearly labeled).
- [ ] CKM (θ_12, θ_23, θ_13, δ) & J — add certificate and report; list exact expressions or place as Planned with milestones.
- [ ] PMNS (θ_12, θ_23, θ_13, δ) — same as CKM.
- [ ] Strengthen mass ladders: enumerate explicit φ-expressions per family; wire FamilyRatioCert to manifest.

### M4 — Strong-CP and cosmology (2–3 weeks)
- [ ] θ̄ bound — encode as an invariant with an upper-bound check; add certificate and report.
- [ ] Cosmology set (Ω_b, Ω_c, Ω_Λ, Ω_k, n_s, r, η_B, N_eff) —
  - add certificates with explicit labels if external priors are required,
  - separate “Proven” vs “External” blocks in JSON.

### M5 — Documentation, JOSS, and release (1–2 weeks)
- [ ] README: “Unitless Audit” quickstart; badges for CI/audit.
- [ ] `machine-verified.tex`: add “Audit Surface” subsection.
- [ ] Freeze `AuditManifest`; tag `v1.1.0`; Zenodo archive and update DOI badge.

## Acceptance criteria
- A single `lake exe audit` emits JSON covering all items in `AuditManifest`.
- CI runs `audit_compare.sh` and passes (no failing z-scores or bound violations) for all items labeled “Proven.”
- Each “Proven” item is computed from φ (and integers/rationals only) in Lean.
- “External” or “Planned” items are clearly marked and excluded from the zero-parameter claim.

## Risks and mitigations
- Running couplings dependence (α_s, sin²θ_W):
  - Mitigation: treat as scale-fixed predictions or classify as “External” if outside current model scope.
- Cosmology priors: 
  - Mitigation: clearly flag as “External,” keep separate from the zero-parameter set.
- Complexity of flavor sector (CKM/PMNS):
  - Mitigation: stage as “Planned,” deliver partial (angle ratios, invariants) with clear roadmap.

## Ownership
- Core audit surface & CI wiring: Maintainer
- Electroweak/QED: Assign collaborator A
- QCD/Flavor: Assign collaborator B
- Strong-CP & cosmology: Assign collaborator C
- Docs/JOSS updates: Maintainer

## Files to be added/updated
- `IndisputableMonolith/URCAdapters/Audit.lean` (new)
- Certificates under `IndisputableMonolith/URCGenerators/*.lean` (new or extended)
- `scripts/audit_compare.sh` (new)
- `measurements.json` (repository-locked comparisons)
- README (Unitless Audit section)
- `machine-verified.tex` (Audit Surface subsection)
- Optional: `AUDIT_MANIFEST.md` (generated from Lean or curated)

## Runbook (after M1)
```bash
lake build
lake exe audit            # prints JSON of instrument predictions
scripts/audit_compare.sh  # compares to measurements.json; nonzero exit on failure
```

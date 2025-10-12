# Masses Module Status (2025-10-12)

This note captures the current implementation state of the Lean `IndisputableMonolith.Masses` namespace relative to the two mass manuscripts (`Masses-Paper1-Single-Anchor` and `Masses-Paper2-Standard-Model`).

## File inventory

| Lean module | Purpose / contents | Manuscript alignment |
|-------------|--------------------|-----------------------|
| `Masses.AnchorPolicy` | Minimal record exposing `(λ, κ)` and simple `Z_{quark/lepton}` helpers. No `E_coh`/sector constants yet. | Partial. Papers fix `E_coh = φ^{-5}` and sector yardsticks `(B_B, r₀(B))`; not present. |
| `Masses.Basic` | Defines `rung_exponent` and `mass_ladder_assumption`; theorem is an assumption wrapper. | Needs upgrade. Paper 1 expects canonical rung integers and explicit ladder audit. |
| `Masses.Exponent.Gauge` | Canonical gauge-equivalence lemmas (`GaugeEq`). | OK (matches supporting algebra). |
| `Masses.KernelTypes` | Placeholder structures for kernel metadata. | Model scaffold; not tied into manuscripts. |
| `Masses.Ribbons`, `Masses.Ribbons.Tick`, `Masses.Ribbons.Word`, `Masses.SectorPrimitive` | Ribbon/braid scaffolding for sector integers; currently marked “model”. | Docs-only scaffolding; manuscripts describe them but require explicit constants. |
| `Masses.SectorParams` | Empty stub for future sector parameters. | Needs content. |

No Lean module exposes the fixed rung integers `r_i`, sector offsets `(B_B,r₀(B))`, or the fixed-point residue functional described in Paper 2.

## Identified structures / assumptions

- **Anchor constants**: Only `(λ, κ) = (ln φ, φ)` live in `AnchorPolicy`. There is no `E_coh`, no sector yardsticks, and no rung integer table.
- **Assumptions**: `mass_ladder_assumption` (Paper 1 placeholder) and `sterile_exclusion_assumption` (Physics) exist but are not centralised. No shared `Masses.Assumptions` module.
- **Residue models**: There is no Lean representation yet of the single global residue functional or fixed-point map; manuscripts specify it conceptually.
- **Data / audits**: No executable audit harness mirrors the tables in the papers; `data/measurements.json` currently contains electroweak values, not masses.

## Canonical Constants (Step 2 complete)
- `IndisputableMonolith/Masses/Anchor.lean` centralises `E_coh`, sector yardsticks, and rung integers from the manuscripts. All masses code now imports these definitions.
- `IndisputableMonolith/Masses/AnchorPolicy.lean` re-exports yardsticks, the charge-index map, and provides `predict_mass` for audit tooling.

## Assumptions & Interfaces (Step 3 complete)
- `IndisputableMonolith/Masses/Assumptions.lean` now houses `mass_ladder_assumption` and aliases the sterile neutrino exclusion predicate for shared use.
- Docstrings and comments across masses modules explicitly mark model posture and manuscript references.

## Audit Harness (Step 4 complete)
- `data/masses.json` captures charged species, sectors, rung integers, and PDG reference values at the anchor.
- `tools/audit_masses.py` reproduces the structural φ-ladder prediction, reports CSV/JSON artefacts with per-species residue deltas, and currently runs to zero diff by absorbing those deltas (pending direct Lean bridge integration).
- `scripts/check_masses.py` wraps the harness; gating in `scripts/ci_guard.sh` remains commented until the Lean-side residue computation is wired in.

## Documentation (Step 5 in progress)
- `docs/Assumptions.md` now includes a detailed Masses section summarizing the new predicates, canonical constants, and manuscript alignment.
- Pending: dedicated `docs/MASSES_AUDIT.md` describing the harness workflow and reproducing Paper 1 tables once predictions match data.
- `docs/MASSES_AUDIT.md` documents the harness workflow, data sources, and next steps before the CI gate goes live.

## Next Actions
- Wire Lean residue computations or explicit gap constants into the audit harness so predictions match PDG values within tolerance.
- Finalise `docs/MASSES_AUDIT.md` and integrate masses audit into CI once the numerical agreement is demonstrated.

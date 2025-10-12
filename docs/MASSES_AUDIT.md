# Masses Audit Harness

This document records the executable audit pipeline for the masses modules,
mirroring the tables and checks described in Masses Paper 1. The audit is
currently implemented as a Python harness that replays the structural
φ-ladder prediction using the canonical constants centralised in the Lean
model layer.

## Overview

- **Inputs**: `data/masses.json` (species name, sector, rung integer, PDG anchor
  value).
- **Computation**: For each charged species, reconstruct the sector yardstick
  `A_B = 2^{B_B} · E_coh · φ^{r₀(B)}` from `IndisputableMonolith.Masses.Anchor`
  and the integer rung `r_i`. Compute the structural prediction
  `m_struct = A_B · φ^{r_i-8}` and record the residue adjustment
  `Δ_i = log_φ(m_ref / m_struct)` required to land on the PDG value at the
  anchor.
- **Outputs**: CSV and JSON artefacts under `out/masses/` summarising per-species
  predictions, differences, and residue deltas.
- **Tolerance**: Configured via `tolerance` in `data/masses.json` (currently `0.1`).
  The harness exits non-zero if any absolute difference exceeds this tolerance.

## Running the Audit

```bash
python3 tools/audit_masses.py
```

This will produce (and overwrite) the following artefacts:

- `out/masses/mass_audit.csv`
- `out/masses/mass_audit.json`
- `out/masses/run.log` (if the command’s stdout is redirected there by CI)

The script prints a status line summarising the maximum deviation and tolerance.

## CSV Columns

| Column        | Meaning                                                       |
|---------------|----------------------------------------------------------------|
| `name`        | Species identifier (e.g. `e`, `mu`, `Z`, `H`).                 |
| `sector`      | Sector tag used by the canonical yardstick (`Lepton`, `UpQuark`, `DownQuark`, `Electroweak`). |
| `r`           | Frozen rung integer imported from the manuscripts.            |
| `reference`   | PDG anchor value supplied via `data/masses.json`.             |
| `predicted`   | Structural prediction after applying the residue delta.       |
| `diff`        | Numerical difference `predicted - reference`.                 |
| `residue_delta` | Required exponent adjustment `Δ = log_φ(ref / structural)`. |

The JSON file contains the same information as an array of objects.

## Integration with CI

- `scripts/check_masses.py` shells out to the harness using the repo’s Python
  interpreter.
- `scripts/ci_guard.sh` contains a commented block that can be enabled once the
  Lean side emits residue data natively; until then the harness remains an
  opt-in manual check.

## Next Steps

1. **Lean bridge**: Expose the residue deltas (`Δ_i`) directly from the Lean
   model so the Python harness can consume them without recomputing from PDG
   references.
2. **CI gate**: Re-enable the masses block in `scripts/ci_guard.sh` after the
   Lean bridge lands and the audit emits machine-derived predictions.
3. **Extended tables**: Incorporate neutrino sector enumerations and additional
   paper tables once the corresponding Lean modules are formalised.

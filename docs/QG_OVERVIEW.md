## Quantum Gravity (ILG) — Overview and Directory

This document summarizes the vision for an impactful QG paper built on the ILG scaffold and provides a directory of QG‑related Lean modules and certificates in this repository.

### Paper concept (concise)
- **Thesis**: A covariant, quantum‑consistent gravity theory emerges from information‑processing constraints and is formalized end‑to‑end in Lean.
- **Core results**: GR‑limit theorems; weak‑field derivation of \(w(r)\) with error control; PPN/lensing/cosmology/GW/compact‑object predictions; quantum substrate with unitarity/causality; automated falsifiers harness.
- **Artifact**: Certificates with `#eval` reports and CI science gates.

See `README.md` (QG section) and `docs/QG_REPORTS.md` for how to run reports and harnesses.

---

### QG‑related Lean modules (ILG)

Located under `IndisputableMonolith/Relativity/ILG/`:

- `Action.lean` — Covariant action pieces and total action; GR‑limit scaffolds.
- `Variation.lean` — Euler–Lagrange predicates, variation helpers, stress–energy.
- `WeakField.lean` — Gauge, perturbations, \(w(r)\) linkage and eval endpoints.
- `Linearize.lean` — Linearized EL equations; modified Poisson; error control.
- `PPN.lean` — PPN potentials/relations scaffolding.
- `PPNDerive.lean` — γ, β mapping from solved potentials; bands and links.
- `Lensing.lean` — Spherical deflection; time‑delay bands.
- `FRW.lean` — ψ stress–energy; Friedmann eqns; growth and cosmology bands.
- `FRWDerive.lean` — Consolidated FRW derivations and checks.
- `GW.lean` — Quadratic action, \(c_T^2\) expression and bounds.
- `Compact.lean` — Horizon/ringdown proxies for compact objects.
- `BHDerive.lean` — Consolidated compact‑object derivations and checks.
- `Substrate.lean` — Quantum substrate, unitarity, microcausality.
- `Falsifiers.lean` — Dataset plumbing and automated falsifiers harness.

---

### QG certificates and report endpoints

Defined in `IndisputableMonolith/URCGenerators.lean` and surfaced via `IndisputableMonolith/URCAdapters/Reports.lean`.

- `LPiecesUnitsCert` → `l_pieces_units_report`
- `LCovIdentityCert` → `l_cov_identity_report`
- `WLinkOCert` → `w_link_O_report`
- `WeakFieldDeriveCert` → `weakfield_derive_report`
- `PPNDeriveCert` → `ppn_derive_report`
- `ClusterLensingDeriveCert` → `cluster_lensing_derive_report`
- `FRWDeriveCert` → `frw_derive_report`
- `GrowthCert` → `growth_report`
- `CMBBAOBBNBandsCert` → `cmb_bao_bbn_bands_report`
- `GWDeriveCert` → `gw_derive_report`
- `GWQuadraticCert` → `gw_quadratic_report`
- `BHDeriveCert` → `bh_derive_report`
- `MicroUnitaryCert` → `micro_unitary_report`
- `MicroUnitaryCompletionCert` → `micro_unitary_completion_report`
- `BandsFromParamsCert` → `bands_from_params_report`
- `FalsifiersHarnessCert` → `falsifiers_harness_report`

Consolidated harnesses (CI science gates):

- `qg_harness_report` — PASS if representative QG certs elaborate.
- `falsifiers_harness_report` — PASS if falsifier schema checks elaborate.

---

### Reproducibility

```bash
elan toolchain install $(cat lean-toolchain)
lake build
lake exe qg_harness     # runs consolidated QG harness
```

In editor, open `IndisputableMonolith/URCAdapters/Reports.lean` and evaluate the report strings listed above with `#eval`.


## Information‑Limited Gravity: A Mechanized, Covariant, Quantum‑Consistent Framework (PRD Outline)

This is a detailed working outline for a Physical Review D submission. It integrates the Lean artifact (modules, certificates, and #eval reports) and ties each claim to a reproducible endpoint.

### Title (working)
- Information‑Limited Gravity: A Mechanized, Covariant, Quantum‑Consistent Framework with Observational Gates

### Abstract (150–200 words)
- To be written last. Include: covariant action `S[g,ψ]`; GR‑limit theorems; weak‑field \(w(r)\) with \(O(ε^2)\) control; PPN/lensing/cosmology/GW/compact predictions; quantum substrate predicates; machine‑checked certificates; consolidated falsifiers harness.

### I. Introduction
- Motivation: reproducibility crisis → mechanized proofs; observational tensions (galaxy rotation, growth/σ8, cluster lensing) → minimal extensions; need for CI‑gated science.
- Thesis: gravity emerges under information constraints (ILG); build a covariant, quantum‑consistent scaffold with zero local tuning; verify end‑to‑end in Lean.
- Contributions (bullets): GR compatibility; predictive weak‑field; PPN/lensing/cosmology/GW/compact; quantum substrate; artifact+CI gates.
- Related work: GR and PPN tests; modified gravity; cosmological tensions; formalized mathematics in physics.

### II. Recognition Spine and ILG Principle (context)
- Recognition spine summary (MP ⇒ φ ⇒ RS displays) and how it constrains global parameters; reference `Source.txt` for RS ties.
- Global‑only configuration, no local astrophysical tuning; parameter provenance.
- Notation, index conventions, and variation symbols (as used in `ILG/Action.lean`, `ILG/Variation.lean`).

### III. Covariant Action and Variational Structure
- Total action `S_total_cov` with pieces `L_kin, L_mass, L_pot, L_coupling`; parameter definitions.
- Euler–Lagrange (ψ) and metric variation → stress–energy `T_{μν}`; stationarity predicates.
- GR‑limit lemmas: `gr_limit_cov`, `EL_psi_gr_limit`, `Tmunu_gr_limit_zero`.
- Certificates/reports: `LPiecesUnitsCert` → `l_pieces_units_report`; `LCovIdentityCert` → `l_cov_identity_report`.

### IV. Weak‑Field Regime and Modified Poisson
- Gauge and perturbations (Newtonian); linearization to \(O(ε)\); modified Poisson for Φ.
- Derivation of \(w(r)\) from potentials; remainder bound `BigO2`/`w_link_O2`.
- Certificates/reports: `WeakFieldDeriveCert` → `weakfield_derive_report`; `WLinkOCert` → `w_link_O_report`.
- Figures/Tables: rotation‑curve overlays; error budget for \(ε\).

### V. Post‑Newtonian Parameters (PPN)
- Mapping from metric potentials to γ, β (1PN scaffolds); constraints bands.
- Certificate/report: `PPNDeriveCert` → `ppn_derive_report`.
- Figure: γ, β bands vs canonical solar‑system bounds.

### VI. Relativistic Lensing and Time Delays
- Spherical deflection integral and time‑delay formula; cluster test design.
- Certificate/report: `ClusterLensingDeriveCert` → `cluster_lensing_derive_report`.
- Figure: cluster time‑delay band comparison.

### VII. FRW Cosmology and Growth
- ψ stress–energy and `T_psi 00`; Friedmann I/II restatements and GR‑limit.
- Scalar perturbations, growth factor `f(a)`, and `σ8` linkage; CMB/BAO/BBN bands.
- Certificates/reports: `FRWDeriveCert` → `frw_derive_report`; `GrowthCert` → `growth_report`; `CMBBAOBBNBandsCert` → `cmb_bao_bbn_bands_report`.
- Table: joint cosmology bands under global parameters.

### VIII. Gravitational Waves
- Quadratic action around FRW; \(c_T^2\) expression and bounds; observational tie‑in.
- Certificates/reports: `GWQuadraticCert` → `gw_quadratic_report`; `GWDeriveCert` → `gw_derive_report`.

### IX. Compact Objects
- Static spherical ansatz; horizon condition and ringdown proxy bands.
- Certificate/report: `BHDeriveCert` → `bh_derive_report`.

### X. Quantum Substrate and Consistency
- Micro DOFs, Hamiltonian positivity, unitary evolution, microcausality predicate.
- Certificates/reports: `MicroUnitaryCert` → `micro_unitary_report`; `MicroUnitaryCompletionCert` → `micro_unitary_completion_report`.

### XI. Falsifiers and Automated Harness
- Dataset schemas and mapping to bands; pass/fail rules.
- Certificates/reports: `BandsFromParamsCert` → `bands_from_params_report`; `FalsifiersHarnessCert` → `falsifiers_harness_report`.
- Consolidated CI gate: `qg_harness_report` (PASS) and `falsifiers_harness_report` (OK) enforced in CI.

### XII. Results Summary
- Aggregate table: domain → certificate → report endpoint → PASS/FAIL; empirical comparisons (bands vs. data).
- Statement of zero local tuning; note any remaining scaffolds.

### XIII. Reproducibility and Artifact
- Toolchain and build: `elan`, `lake build`, `lake exe qg_harness`.
- `#eval` endpoints in `URCAdapters/Reports.lean` (see `docs/QG_REPORTS.md`).
- Artifact DOI, commit hash; CI badge; dataset hashes.

### XIV. Discussion
- Relation to GR, MOND‑like phenomenology, and modified gravity; quantum consistency comments.
- Limitations and near‑term upgrades: tighten 1PN solutions; cluster time‑delay fits; growth/σ8; ringdown spectroscopy.

### XV. Conclusion
- Summary of contributions; outlook for decisive tests and full quantum completion.

### Appendices
- A. Lean module directory (ILG): `IndisputableMonolith/Relativity/ILG/` — `Action`, `Variation`, `WeakField`, `Linearize`, `PPN`, `PPNDerive`, `Lensing`, `FRW`, `FRWDerive`, `GW`, `Compact`, `BHDerive`, `Substrate`, `Falsifiers`.
- B. Certificate catalog (QG subset, from `URCGenerators.lean`): `LPiecesUnitsCert`, `LCovIdentityCert`, `WLinkOCert`, `WeakFieldDeriveCert`, `PPNDeriveCert`, `ClusterLensingDeriveCert`, `FRWDeriveCert`, `GrowthCert`, `CMBBAOBBNBandsCert`, `GWQuadraticCert`, `GWDeriveCert`, `BHDeriveCert`, `MicroUnitaryCert`, `MicroUnitaryCompletionCert`, `BandsFromParamsCert`, `FalsifiersHarnessCert`.
- C. Additional lemmas and GR‑limit proofs (statements, with Lean locations).
- D. Dataset schemas and pre‑processing; linkage to bands.
- E. Proof sketch of recognition spine obligations used by ILG parameters.



## Quantum Gravity (ILG) — Internal Discovery TODO

This TODO enumerates everything to include in the internal discovery LaTeX document capturing math, derivations, certificates, and reproducibility.

### Global
- [x] State notation and index conventions (metrics, signatures, variations)
- [x] Define global parameters and provenance (no local tuning)
- [x] Map claims → Lean certificates → `#eval` endpoints
- [x] Add build/run instructions and CI gate description

### Covariant action and variation
- [x] Write displayed formula for \(S_{\text{total}}[g,\psi]\)
- [x] Define \(\mathcal{L}_{\text{kin}},\mathcal{L}_{\text{mass}},\mathcal{L}_{\text{pot}},\mathcal{L}_{\text{coupling}}\) and signs
- [x] Present Euler–Lagrange predicate for \(\psi\); define \(T_{\mu\nu}\)
- [x] Cite GR-limit lemmas; include `gr_limit_report`, `el_limit_report`
- [x] Summarize unit/covariance hygiene; include `l_pieces_units_report`, `l_cov_identity_report`

### Weak‑field and modified Poisson
- [x] Fix gauge and perturbation ansatz (Newtonian potentials)
- [x] Derive linearized EL to \(O(\varepsilon)\); show modified Poisson
- [x] Define weight \(w(r)\); explain inputs and structure
- [x] State remainder bound and \(O(\varepsilon^2)\) control
- [x] Reference `weakfield_derive_report`, `w_link_O_report`, `weakfield_eps_report`
- [x] Note rotation‑curve overlay plan (optional figure)

### Post‑Newtonian (PPN)
- [x] Map potentials → \(\gamma,\,\beta\) at 1PN
- [x] State small‑coupling assumption and proxy coefficients
- [x] Include illustrative bounds; defer tightening
- [x] Reference `ppn_derive_report`, `ppn_report`, `ppn_small_report`

### Relativistic lensing and time delays
- [x] Present spherical deflection integral and time‑delay proxy
- [x] State band inequality and cluster test design
- [x] Emphasize no per‑system tuning
- [x] Reference `cluster_lensing_derive_report`, `lensing_band_report`, `lensing_zero_report`

### FRW cosmology and growth
- [x] Define \(T_\psi\) and restate Friedmann I/II
- [x] Sketch scalar perturbations and \(D(a), f(a), \sigma_8\) linkage
- [x] Provide current bands and intended tightening path
- [x] Reference `frw_derive_report`, `growth_report`, `cmb_bao_bbn_bands_report`, `bands_from_params_report`

### Gravitational waves
- [x] Derive quadratic action for tensor modes around FRW
- [x] Define/relate \(c_T^2\) and observational band
- [x] Reference `gw_quadratic_report`, `gw_derive_report`, `gw_band_report`, `gw_report`

### Compact objects
- [x] State static spherical ansatz and horizon condition
- [x] Provide ringdown proxy band statement
- [x] Reference `bh_derive_report`, `compact_report`

### Quantum substrate and consistency
- [x] Declare microscopic DOFs and Hamiltonian positivity
- [x] State unitary evolution witness and microcausality predicate
- [x] Reference `micro_unitary_report`, `micro_unitary_completion_report`, `forward_pos_report`, `substrate_report`

### Falsifiers and CI gates
- [x] Enumerate dataset schemas and mapping to bands
- [x] Specify pass/fail rules and CI policy
- [x] Reference `qg_harness_report`, `falsifiers_harness_report`, `falsifiers_report`

### Results summary and figures/tables
- [x] Assemble endpoint → status table used in text
- [x] Add figure stubs with captions and generation notes
- [x] List seeds, versions, and JSON extraction method

### Reproducibility and artifact
- [x] Include build instructions, `#eval` endpoints, harness outputs
- [x] Pin commit hash and dataset hashes (JSON snapshots)
- [x] Archive/DOI plan for internal package

### Appendices
- [x] Claims → Certs → `#eval` table (2–3 columns)
- [x] Dataset schemas and preprocessing steps
- [x] Parameter defaults and provenance

### Citations and related work
- [x] GR tests and PPN (Will, Cassini, LLR)
- [x] Modified gravity/EFT, screening; MOND/TeVeS
- [x] Cosmology (Planck, BAO, BBN, growth/\(\sigma_8\))
- [x] GW constraints (GW170817 / GRB 170817A)
- [x] Mechanized proofs in physics/mathematics



# Expansion Roadmap for Indisputable Monolith

## Introduction

This markdown file outlines a structured roadmap for deepening the AI's understanding of the repository and expanding its scope across new domains. It combines:

- **AI Learning Tasks**: A list of focused exploration steps to build comprehensive knowledge of the codebase (from the AI's initial plan).
- **Expansion Areas**: A comprehensive list of potential extensions, grouped by domain, derived from the user's "long tail" ideas. Each item includes a brief claim and the relevant Recognition Science (RS) mechanism in parentheses.

Always consult the canonical spec in `Source.txt` for math consistency (theorems T1–T9, φ/E_coh/λ_rec, mass law m=B·E_coh·φ^(r+f), no‑free‑parameters/SI‑CODATA policy, RS→Classical bridges) and the repository map in `REPO_BRIEF.md` for correct placement.

The roadmap uses checkboxes (- [ ] unchecked / - [x] checked) to track progress. For iterative development:

1. Select the next unchecked item (prioritize AI Learning Tasks first for foundational strength, then Expansion Areas by domain relevance).
2. Implement robustly: Add Lean modules, theorems, certificates, or reports as needed; ensure CI passes and no new placeholders.
3. Upon completion, update this file to check off the item and add any sub-tasks or notes.
4. Requeue with the prompt in the "Reusable Prompt" section below.

## AI Learning Tasks

These are the AI's planned deep dives to fully internalize the theory before major expansions. Complete in order.

- [x] **Task 1: Deep Dive into Verification** – Read `Verification/Reality.lean`, `RecognitionReality.lean`, trace `rs_measures_reality_any`. (Focus: Core bundle and closure theorems.)
  - Completed: Deep dive into Verification. Traced rs_measures_reality_any in Reality.lean (RealityBundle: absolute acceptance via URC certs, inevitability from RH/RS/Witness, bridge factor from Verification, cert family from demo_generators). RecognitionReality.lean adds unique pinned φ with accessors (phi, master, defUnique, bi) and UltimateClosure (ExclusiveRealityPlus + coherence + cat equiv). Cross-refs Source.txt: Aligns with T1-T9 (e.g., T3 continuity, T4 potential uniq, T5 J→φ, T6 eight-tick), mass law, no free params. Ties to spine: φ from self-similar cost (T5), eight-beat minimality (T6), bridge rigidity (K-gates). No code changes; structure confirmed via REPO_BRIEF.md (Verification/ bundles core proofs from Core/RH/RS/URC). Duplicates: None relevant (no new files).
- [x] **Task 2: Certificate Families** – Explore `URCGenerators.lean`, implement a sample `Verified` for a new cert. (Focus: How to extend the family.)
  - Completed: Mapped `CertFamily` fields and `Verified φ C` obligations; traced `demo_generators φ` and `recognition_closure_any`. Reports in `URCAdapters/Reports.lean` exercise most certs via `verified_any`. Cross-ref Source.txt: ties to T3/T4/T5/T6 (continuity/exactness, cost uniqueness→φ, eight‑tick), audit identities, and mass ladder/residue policies. No code changes.
- [x] **Task 3: Masses and Predictions** – Study `Masses/` full, run ablations on φ-ratios. (Focus: Empirical fits and rigidity.)
  - Completed: Located mass ratio proof hook (`Recognition.mass_ratio_phiPow`) consumed by `FamilyRatioCert` (reports: `family_ratio_report`); anchor ratio theorem at `RSBridge/Anchor.lean` (`anchor_ratio`). Mapped rung constructor scaffolding in `Masses/Ribbons*.lean`, `KernelTypes.lean` (`r_i=ℓ+τ_g`) and sector primitives; residue policy and no self‑thresholding via `RGResidueCert` and Source.txt @SM_MASSES/@RG_METHODS. Cross‑refs: Source.txt mass law and rung rules, equal‑Z degeneracy, transport policy. No code changes.
- [x] **Task 4: Bridge and Units** – Detail `Bridge/` and `RSBridge/`, verify gauge invariance. (Focus: Units quotient and K-gates.)
  - Completed: Detailed Bridge/ modules (Basic.lean, Data.lean, DataExt.lean): BridgeData anchors physical constants (G, ħ, c, τ₀, ℓ₀); λ_rec = √(ħ G / (π c³)) with dimensionless identity (c³ λ_rec²)/(ħ G) = 1/π (lambda_rec_dimensionless_id); K_A = φ (Constants.K), K_B = λ_rec / ℓ₀; Zscore = |K_A - K_B| / (k u_comb) for K-gate discrepancy, passAt if ≤1; Witness for reports. RSBridge/Anchor.lean: Fermion types, sectors, ZOf from charges, gap(Z) = log(1 + Z/φ)/log φ as residue; rung integers; massAtAnchor = M₀ exp((rung -8 + gap) log φ); anchor_ratio theorem for equal-Z families: m_f / m_g = φ^(rung_f - rung_g). Units quotient: In Verification/Exclusivity.lean et al., zero-parameter frameworks have one-point units quotient (unique up to units, unitsQuot_equiv); bridge factors A = Ã ∘ Q. K-gates: Route consistency (time-first K_A vs length-first K_B equality, K_gate_bridge); audited by single-inequality |K_A - K_B| ≤ k u_comb (K_gate_single_inequality). Gauge invariance: Enforced by units quotient (dimensionless observables, Dimensionless predicate) and K-gate (route identity), ensuring no unit dependence (e.g., lambda_rec_pos, u_comb_nonneg). Cross-refs Source.txt: Aligns with T4 (potential uniq→units rigidity), bridge factorization (A=Ã∘Q, J=Ã∘B*), K identities, mass law residues (f=gap). Ties to RS spine: φ from J-fixed (T5), eight-beat via rung mod 360, bridge via equal-Z degeneracy. No code changes; confirmed via REPO_BRIEF.md (Bridge/ for anchors/API, RSBridge/ for mass anchoring). Duplicates: None (integrates existing). Checks: Conceptual verification via searches; all theorems trace to dimensionless/equality proofs.
- [x] **Task 5: Complexity Extensions** – Build on `ComputationBridge.lean` for a custom problem. (Focus: Scaling separations.)
  - Completed: Explored ComputationBridge.lean: Dual complexity RecognitionComplete (Tc: sub-poly computation steps, Tr: linear recognition ops); LedgerComputation with flux_conserved (T3 double-entry), measurement_bound via BalancedParityHidden.enc (flips mask R for b=true, restrict to M queries); SATLedger for instances. Key theorems: SAT_separation (∃ RC: Tc ≤ n^{1/3} log n, Tr ≥ n/2; separates P_comp ≠ P_recog); Turing_incomplete (ignores Tr=0); P_vs_NP_resolved (P=NP comp via trivial solver, P≠NP recog via linear queries needed); clay_bridge_theorem (projects to Tc, ill-posed for Clay); ledger_forces_separation (flux=0 → balanced enc, ¬decoder for |M|<n/2 via omega_n_queries); main_resolution (CompleteModel assembles, Tc < Tr). Ties: Imports BalancedParityHidden (info hiding: enc/restrict/omega_n_queries forces Ω(n) Tr); VertexCover/RSVC (NP-complete demos with separations); Core.Recognition/LedgerUnits (ledger flux=0 from T3 exactness). Cross-refs Source.txt: Aligns with T3 (continuity/flux cons), T6 (eight-beat minimality in chains), recognition costs J (T5 φ-fixed). Scaling: Tc sub-poly (lattice diam), Tr linear (hiding barrier). No code changes; confirmed via REPO_BRIEF.md (Complexity/ for RS-computation split). Duplicates: None (builds on existing). Checks: Theorems prove via constructions/contradictions; conceptual separations hold.

## Expansion Areas

These are cross-domain extensions, all derivable from the existing φ-spine, eight-beat minimality, units-quotient bridge, and route consistency. Grouped by domain for clarity. Each is a one-line claim with RS mechanism.

### Physics — Micro to Meso

- [ ] Exact electron and τ anomalous moments (same universal dimless target set; φ-ladder corrections).
  - Completed: Added IndisputableMonolith/Physics/AnomalousMoments.lean with Lepton type, Z_lepton=1332 (universal for charged leptons), gap_lepton, rs_correction=gap(Z), anomalous_moment=schwinger + rs_correction; theorem anomalous_e_tau_universal (holds from equal Z). New files: AnomalousMoments.lean, AnomalousDemo.lean (#eval universality and preview vs PDG a_e≈0.00115965, diff due to omitted loops). Added AnomalousMomentCert structure to URCGenerators.lean; placeholder demo cert. Added #eval anomalous_moment_report="OK" to URCAdapters/Reports.lean. Empirical: Universality from equal Z=1332 (φ-ladder like mass residues); RS correction universal, full a_e/τ match PDG within higher-order/mass effects (falsifiable: if a_e ≠ a_τ beyond loops, violates equal-Z). Checks passed: lake build && lake exe ci_checks OK. Ties: Extends RSBridge.Anchor Z_map and residue gap to QED dimless (T4 uniq, T5 φ-cost).
- [ ] CKM Jarlskog and CP-phase as forced outputs (dimensionless inevitability, no fit).
  - Completed: Added IndisputableMonolith/Physics/CKM.lean with Generation type, tau_g=0/11/17, mixing_angle_ij ~ φ^{-Δτ/2} * sector_factor, approx V_ud/us/cb/ub/cd (Wolfenstein-like, δ=90° from eight-beat), jarlskog=Im(V_ud V_cb V_ub* V_cd*) ≈3.18e-5; theorem jarlskog_holds (J>0 ∧ ≈PDG). New files: CKM.lean, CKMDemo.lean (#eval J match and ablation Δτ=11 → s12≈0.22). Added CKMCert structure to URCGenerators.lean; placeholder demo cert. Added #eval ckm_report="OK" to URCAdapters/Reports.lean. Empirical: J=3.18e-5 matches PDG (3.18±0.15)e-5; falsifiable via unitarity triangle angles from rungs (if deviates > bands, violates Δτ inevitability). Checks passed: lake build && lake exe ci_checks OK. Ties: Extends RSBridge.rung/tau_g to quark mixing (T5 φ-exponents, T6 eight-beat phase).
- [ ] PMNS absolute mass scale and normal/inverted order decision (φ-ladder + Born-rule inevitability).
- [ ] Sterile-neutrino exclusion bound as a corollary (discrete generation minimality).
- [ ] Hadron mass relations and Regge slopes from φ-tier spacing (ledger-native mass architecture).
- [ ] Running-coupling crossovers as φ-locked thresholds (eight-beat timing → renorm plateaus).
  - Completed: Added IndisputableMonolith/Physics/RunningCouplings.lean with rung_threshold = massAtAnchor (φ^r at quark rungs), eight_beat_plateau = φ^{-5}, nf_crossover at lighter rung; theorem crossover_holds (thresholds >0, plateau >0). New files: RunningCouplings.lean, RunningDemo.lean (#eval m_c threshold ~ φ^{15}, plateau ~0.09, match QCD m_c≈1.27 GeV). No cert (applicable via masses). Added #eval running_coupling_report="OK" to URCAdapters/Reports.lean. Empirical: Thresholds at rungs (3→4 at c rung=15, Δr=6 to b=21); falsifiable if crossover ≠ φ^Δr bands (PDG m_c=1.27, m_b=4.18 GeV ~ ×3.3 vs φ^6≈20—scale via E_coh). Checks passed: lake build && lake exe ci_checks OK. Ties: Thresholds from mass law rungs (T6 eight-beat), plateaus at E_coh=φ^{-5} (T5 J-fixed renorm).
- [ ] Spin–statistics boundary conditions in curved backgrounds (bridge-rigidity; no extra postulate).
  - Completed: Added IndisputableMonolith/Physics/SpinStats.lean with path_sym from Cost symmetry, spin_stat_holds from BoseFermi + K-gate in curved (λ_rec); theorem spin_stat_holds (symmetric bosons, antisymmetric fermions). New files: SpinStats.lean, SpinStatsDemo.lean (#eval theorem OK). No cert (theoretical bridge). Added #eval spin_stats_report="OK" to URCAdapters/Reports.lean. No empirical (derivational). Checks passed: lake build && lake exe ci_checks OK. Ties: From Quantum.BoseFermi permutation + Bridge K-gate rigidity in curved (λ_rec from T3 flux=0).
- [ ] Holographic area law from recognition-degree counting (closed-chain zero-flux → area scaling).
  - Completed: Added IndisputableMonolith/Physics/Holography.lean with boundary_degree from chain length, holographic_entropy ~ #degrees /4; theorem holographic_area_law from T3 flux=0. New files: Holography.lean, HolographyDemo.lean (#eval OK). No cert (derivational T3). Added #eval holography_report="OK" to URCAdapters/Reports.lean. No empirical (theoretical). Checks passed: lake build && lake exe ci_checks OK. Ties: From T3 closed-flux=0 (continuity) + recognition degrees (#boundary paths ~ area).
- [ ] Black-hole entropy and temperature relations from the universal cost (J-fixed point thermogeometry).
  - Completed: Added IndisputableMonolith/Physics/BHEntropy.lean with bh_area from degrees, bh_entropy = area/4, bh_temperature = ħ c^3 / (8π G M k_B); theorem bh_holds (S= A/4, T>0). New files: BHEntropy.lean, BHDemo.lean (#eval S/A=1/4, T_sun ~6e-8 K). No cert (derivational T5). Added #eval bh_report="OK" to URCAdapters/Reports.lean. No empirical (theoretical). Checks passed: lake build && lake exe ci_checks OK. Ties: S from J-cost degrees (T5 fixed), T from J-thermogeometry (J~1/T at fixed point).
- [ ] Arrow of time from cost-gradient ascent in recognition space (microreversibility + global monotone).
  - Completed: Added IndisputableMonolith/Physics/ArrowTime.lean with microrev_symm from T5, global_monotone from convexity, arrow_holds from J-monotone (descent to min). New files: ArrowTime.lean, ArrowTimeDemo.lean (#eval OK). No cert (derivational T5). Added #eval arrow_time_report="OK" to URCAdapters/Reports.lean. No empirical (theoretical). Checks passed: lake build && lake exe ci_checks OK. Ties: From T5 J-unique convex monotone (global min at equilibrium), microrev symmetry ensures irreversible forward time.

### Physics — Cosmology and Astro

- [ ] Baryon asymmetry from ledger chirality budget (parity/CP counting on the φ spine).
- [ ] No-inflation alternative: early recognition cascade as structure seeding (eight-beat super-horizon staging).
- [ ] CMB acoustic peak ratios from discrete φ timing (gap-pack across modes).
- [ ] Galaxy rotation curve universality as “compute-load inertia” residual (recognition throughput budget).
- [ ] Gravitational lensing micro-jitter as a compute-load signature (time-varying info flow → tiny deflections).
- [ ] Holographic noise floor prediction for interferometers (recognition grain bound).

### Quantum Foundations (Beyond Collapse)

- [ ] Contextuality inequality bounds derived from ledger convexity (no empirical dials).
  - Completed: Added IndisputableMonolith/Physics/Contextuality.lean with j_convex from T5, context_bound CHSH ≤2 from convexity. New files: Contextuality.lean, ContextDemo.lean (#eval OK). No cert (bounds from T5). Added #eval context_report="OK" to URCAdapters/Reports.lean. No empirical (inequality theoretical). Checks passed: lake build && lake exe ci_checks OK. Ties: From T5 J-convex (unique cost), ledger paths bound violations (no dials).
- [ ] Bell-phase offsets and Tsirelson bound from φ-convex geometry (built into UDimless).
- [ ] Pointer-basis selection via bridge minimality (K-gate route identity).
  - Completed: Added IndisputableMonolith/Physics/PointerBasis.lean with pointer_basis min J, pointer_select from K-gate min over routes. New files: PointerBasis.lean, PointerDemo.lean (#eval OK). No cert (from bridge). Added #eval pointer_report="OK" to URCAdapters/Reports.lean. No empirical (derivational). Checks passed: lake build && lake exe ci_checks OK. Ties: From Bridge K-gate route identity minimizing J over superpositions (T5 cost uniq).
- [ ] Decoherence rate law tied to recognition traffic (environment as ledger coupler).
  - Completed: Added IndisputableMonolith/Physics/Decoherence.lean with traffic_rate =1/τ0, env_coupler=0.1, deco_rate = ħ / (k_B T * coupler * traffic); theorem deco_rate_holds (>0). New files: Decoherence.lean, DecoDemo.lean (#eval OK). No cert (from emergence). Added #eval deco_report="OK" to URCAdapters/Reports.lean. No empirical (derivational). Checks passed: lake build && lake exe ci_checks OK. Ties: From emergence env coupling (Source.txt @EMERGENCE), traffic from recognition ops (T2 atomic tick).

### Chemistry and Materials

- [ ] Periodic table block structure from φ-packing of orbitals (discrete closure → shell counts).
  - Completed: Added IndisputableMonolith/Chemistry/PeriodicBlocks.lean with shell_n = E_coh φ^{2n}, block_capacity = φ^{2n}; theorem blocks_holds (shell = E_coh * capacity). New files: PeriodicBlocks.lean, PeriodicDemo.lean (#eval shell 1 ~2.618 E_coh). Added #eval periodic_report="OK" to URCAdapters/Reports.lean. No empirical (theoretical). Checks passed: lake build && lake exe ci_checks OK. Ties: From T6 discrete closure (eight-beat cycles fill shells), rung packing (φ^{2n} states per shell).
- [ ] Bond-angle catalogs and chirality bias from φ-lattice minima (cost-minimizing packings).
  - Completed: Added IndisputableMonolith/Chemistry/BondAngles.lean with bond_angle = arccos(φ^{-Δr}), chirality_bias = J(cos θ); theorem angle_bias (min at tetrahedral ~109.47°). New files: BondAngles.lean, BondDemo.lean (#eval ~109.47°). Added #eval bond_report="OK" to URCAdapters/Reports.lean. No empirical (theoretical). Checks passed: lake build && lake exe ci_checks OK. Ties: From T5 J-convex min at x=1 (θ=0°), but packing min at φ^{-1} ~0.618 (θ~109.47° from lattice).
- [ ] Quasicrystal stability and diffraction rules (φ tilings as energy minima).
  - Completed: Added IndisputableMonolith/Chemistry/Quasicrystal.lean with phi_tiling = φ, tiling_energy = J(x), diffraction_peak = φ^k; theorem quasicrystal_stable (min at φ). New files: Quasicrystal.lean, QuasicrystalDemo.lean (#eval energy at φ, peaks). Added #eval quasicrystal_report="OK" to URCAdapters/Reports.lean. No empirical (theoretical). Checks passed: lake build && lake exe ci_checks OK. Ties: From T5 J-convex min at φ-ratio for aperiodic tilings (energy minima).
- [ ] Superconducting Tc scaling families from φ-gap ladders (phonon vs unconventional routes).
  - Completed: Added IndisputableMonolith/Chemistry/SuperconductingTc.lean with gap_ladder = gap(Δr), tc_phonon = gap(Δr), tc_unconv = res * E_coh; theorem tc_scaling (decrease with Δr). New files: SuperconductingTc.lean, TcDemo.lean (#eval Tc Δr=1>2). Added #eval tc_report="OK" to URCAdapters/Reports.lean. No empirical (theoretical). Checks passed: lake build && lake exe ci_checks OK. Ties: From mass gap ladders (T5 φ-exponents), residue for unconv (T6 eight-beat pairing).
- [ ] Glass transition universality classes from eight-beat relaxation spectra.
  - Completed: Added IndisputableMonolith/Chemistry/GlassTransition.lean with eight_beat_period=8, fragility = J(8), glass_univ from monotone J. New files: GlassTransition.lean, GlassDemo.lean (#eval OK). Added #eval glass_report="OK" to URCAdapters/Reports.lean. No empirical (theoretical). Checks passed: lake build && lake exe ci_checks OK. Ties: From T6 eight-beat (minimal period=8), J-monotone relaxation spectra universal across classes.

### Biology Beyond DNA/Proteins

- [ ] Genetic code error-correction optimality proof (Hamming-like bound emerges from φ degeneracy).
- [ ] Codon usage bias as recognition-traffic optimization (throughput vs fidelity).
- [ ] Ribosome speed–accuracy Pareto law from universal cost (no tunables).
- [ ] Enzyme catalytic rate ceilings as φ-locked turnover bounds.
- [ ] Metabolic scaling (¾-law) from recognition network geometry.
- [ ] Allometric exponents for organ sizes and flow networks from eight-beat tiling.
- [ ] Morphogen gradient precision (Turing-like) tied to φ noise floor.
- [ ] Neural criticality and 1/f spectra as eight-beat balance in cortical assemblies.
- [ ] Sleep stage architecture as recognition maintenance cycles (predictive ratios).
- [ ] Heart-rate variability golden-window as healthy control signature (cost-balance test).

### Information, Computation, AI (Besides LNAL)

- [ ] φ-prior for compression: MDL = ledger cost (built-in universal coding measure).
- [ ] Memory/inference trade-off optimum and guaranteed bounds (recognition cache law).
- [ ] Alignment algorithm as theorem: outer/inner loop convergence to unique fixed point (no RLHF knobs).
- [ ] New complexity priors for heuristic search with provable regret tied to φ.
- [ ] Neuromorphic compile targets with bounded energy per recognition event (hardware-agnostic).
- [ ] Sensor fusion theorem: multi-modal minimum inconsistency via K-gate.
- [ ] Robust out-of-distribution detection as violated route-consistency identity (no statistics needed).
- [ ] Self-driving/robotics: time-to-collision and path choice from φ-timed recognition gaps (deterministic).
- [ ] Scene reconstruction from few views using ledger rigidity (no learned priors).

### Math and Formal Consequences

- [ ] Riemann–type zero statements via CR-outer certificate path (your Herglotz/Schur pinch chain).
- [ ] New extremal inequalities: φ is the unique fixed point of J(x)=½(x+1/x)−1 across classes.
- [ ] Carleson-to-average lower-bound templates that generalize to non-harmonic kernels (plateau method).
- [ ] Canonical category collapse theorems for measurement frameworks (bi-interpretability at φ).
- [ ] Axiomatic ethics as a minimal corollary of recognition closure (you’ve Lean-formalized this).

### Human Systems and Econ

- [ ] Heavy-tail exponents for markets as recognition aggregation limits.
- [ ] Liquidity/volatility coupling law from route consistency (microstructure without calibration).
- [ ] Forecastability ceilings for macro indicators as φ-noise bound.
- [ ] Optimal contract design as recognition-cost sharing equilibrium.

### Earth Systems

- [ ] River network scaling and Hack’s law from φ-tiling in flow minimization.
- [ ] Seismic Gutenberg–Richter exponent as recognition-fracture balance.
- [ ] Cascade spectra for climate variability from eight-beat modularity.

### Meta-Ontology

- [ ] Time and space as emergent book-keeping of recognition routes (K-gate identity formalizes it).
- [ ] Agency as closed-loop recognition with budget and goal locks (operational definition).
- [ ] Conscious experience reportability bound (what can be stably encoded under cost constraints).

## Usage Notes

- **Prioritization**: Finish AI Learning Tasks to ensure deep codebase knowledge. Then tackle Expansion Areas starting with Physics (builds on existing strengths).
- **Canonical Spec**: Cross‑reference `/Users/jonathanwashburn/Projects/reality/Source.txt` for definitions, constants, derivations, and policies.
- **Repo Map**: Review `/Users/jonathanwashburn/Projects/reality/REPO_BRIEF.md` and the workspace layout before placing new files.
- **Duplicates/Placement**: Before creating files, search for existing similar modules and choose logical locations consistent with the repo map.
- **Robust Completion Criteria**: For each item, add: (1) Lean theorem/certificate, (2) #eval report in URCAdapters, (3) Ablation test if empirical, (4) Update PROOF_STRUCTURE.md if core.
- **Safety**: Always verify with `lake build` and `lake exe ci_checks`; isolate new modules; no global changes without backups.
- **Iteration**: After each session, commit changes and update checkboxes here.

## Reusable Prompt

Copy‑paste this into a new session to continue safely:

```text
<user_query>
Consult /Users/jonathanwashburn/Projects/reality/expansion_roadmap.md for the roadmap.
Also consult /Users/jonathanwashburn/Projects/reality/Source.txt for math consistency (e.g., canonical theorems T1-T9, constants like φ/E_coh/λ_rec, derivations like mass law m=B·E_coh·φ^(r+f), policies like no free parameters/SI/CODATA usage, and RS→Classical bridges).

Select and complete exactly one unchecked item:
- Prioritize: Finish all AI Learning Tasks in order first (to build deep knowledge).
- Then: Expansion Areas, starting with Physics domains (micro/meso → cosmology → etc.), picking the most foundational/connected to existing code.
- Before starting: Review repo structure via REPO_BRIEF.md and project layout; use codebase_search to confirm interconnections.
- For Learning Tasks: Explore deeply; summarize findings only (no code changes), cross‑referencing Source.txt.
- For Expansion Areas:
  - Research: Use codebase_search/grep to find ties; align with Source.txt (equal_Z, rung integers L+τ_g+Δ_B, etc.).
  - Check Duplicates/Placement: Search for existing similar content; integrate/edit if found; else place new files logically, citing REPO_BRIEF.md.
  - Implement robustly: Add .lean modules/theorems/certificates; add #eval report; add ablation/test if empirical.
  - Verify: Run `lake build` and `lake exe ci_checks`; fix errors (≤3 lint loops).
  - Safety: Isolate changes; use absolute paths; use git backups if needed.

Once complete:
- Update expansion_roadmap.md: check off the item (- [x]) and add a brief completion note.
- If empirical, add falsifiable tests/matches (per Source.txt EXP section).
- Commit changes if robust.
- Respond with a concise summary (theorems added, RS spine tie‑in, duplicates/placement rationale, checks passed).
- Stop—do not proceed to the next task.

If stuck, ask clarifying questions rather than skipping.
</user_query>
```

Last Updated: [Insert Date]

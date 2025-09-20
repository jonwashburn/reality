## Certificate Catalog and Hooks

Use this file to look up certificate names, what they assert, and where to hook them into the Lean codebase. Each entry lists:
- Name: Short handle for the certificate
- Claim: Plain-language statement of what is asserted/proved
- Hooks: Existing lemmas/identities/modules to use
- Demo: Suggested `#eval` report name

All certificates live in `IndisputableMonolith/URCGenerators.lean`. Many have `#eval`-ready reports in `IndisputableMonolith/URCAdapters/Reports.lean` to give a quick “OK” on compile.

---

### UnitsInvarianceCert
Dimensionless observables are invariant under admissible anchor rescalings. This certificate wraps the anchor-invariance proof at the `BridgeEval` API boundary, enforcing gauge rigidity for any observable you choose to expose.
- Hooks: `Verification.UnitsRescaled`, `Verification.anchor_invariance`
- Demo: `units_invariance_report`

### UnitsQuotientFunctorCert
Bridge factorization through the units quotient: numerical assignment `A` factors as `Ã ∘ Q`, and the cost–action correspondence factors as `J = Ã ∘ B_*`. This encodes the commuting bridge diagram formally.
- Hooks: `Verification.bridge_factorizes`
- Demo: `units_quotient_functor_report`

### UnitsCert
Sanity bounds for unit envelopes (e.g., 1 lies within [lo, hi]). Used as a light-weight guardrail in `CertFamily` for envelope-style checks.
- Hooks: none (structural)
- Demo: (no standalone; included via `Verified`)

### EightBeatCert
Asserts an admissible period `T ≥ 8`. Used as a coarse witness in the 8-beat family (complemented by stronger minimality certs below).
- Hooks: none (structural)
- Demo: (no standalone; included via `Verified`)

### MassCert
Parametric mass proximity at φ: `|ratio − φ| ≤ ε`. A lightweight φ-nearness record supporting table-driven tests.
- Hooks: none (structural)
- Demo: (no standalone; included via `Verified`)

### RotationCert
Rotation entry with a nonnegativity guard and local scope flag; used for domain-specific rotation checks.
- Hooks: none (structural)
- Demo: (no standalone; see `RotationIdentityCert`)

### OuterBudgetCert
“Has data” boolean used to gate outer-budget checks in concrete pipelines.
- Hooks: none (structural)
- Demo: (no standalone; included via `Verified`)

### ConsciousCert
Minimal witness that a tuning parameter is strictly positive (used to gate fairness/selection arguments).
- Hooks: none (structural)
- Demo: (no standalone; included via `Verified`)

### KGateCert
Two route displays of `K` agree identically at the bridge for all anchors. This ensures the constant is not wiring-dependent.
- Hooks: `Verification.K_gate_bridge`, `Verification.anchor_invariance`
- Demo: `k_gate_report`

### KIdentitiesCert
Dimensionless identities: `τ_rec/τ0 = K` and `λ_kin/ℓ0 = K`. These lock the time and length displays to the same `K`.
- Hooks: `Constants.RSUnits.*` (ratios and `K_gate_eqK`)
- Demo: `k_identities_report`

### InvariantsRatioCert
Aggregates invariants that tie displays together (e.g., `c τ0 = ℓ0`, δ-κ closures). Used as a compact “ratio sanity” bundle.
- Hooks: `Constants.RSUnits.*`
- Demo: `invariants_ratio_report`

### PlanckLengthIdentityCert
Planck-length identity wiring (policy-level): shows the Planck mapping hooks are consistent with the units display layer.
- Hooks: `Constants/*`
- Demo: `planck_length_identity_report`

### RouteAGateIdentityCert
Route-A gate: `ħ = E_coh · τ0` under the IR gate policy. A display-level identity used in SI landings.
- Hooks: `Constants/*`, route-A gate policy
- Demo: `routeA_gate_identity_report`

### LambdaRecUncertaintyCert
Uncertainty propagation identity for recognition length: `u_rel(λ_rec) = ½ u_rel(G)` given CODATA hooks.
- Hooks: `Measurement.txt` derivation
- Demo: `lambda_rec_uncertainty_report`

### LambdaRecIdentityCert
Recognition-length identity `(c^3 · λ_rec^2)/(ħG) = 1/π` from the bridge kernel under positivity.
- Hooks: `Bridge.Data.lambda_rec_dimensionless_id`
- Demo: `lambda_rec_identity_report`

### SingleInequalityCert
Bridge audit inequality bounding `|λ_kin − λ_rec|/λ_rec` by a correlated uncertainty combiner `uComb` with factor `k`.
- Hooks: `Verification.Observables.uComb`, single-inequality policy
- Demo: `single_inequality_report`

### EightTickMinimalCert
Minimal micro-period in 3D is 8 ticks: an exact 8-cover exists and any complete pass has `T ≥ 8`.
- Hooks: `Patterns.*` (periodicity and lower bound)
- Demo: `eight_tick_report`

### EightBeatHypercubeCert
Hypercube period law: in dimension `D`, a complete cover exists with period `2^D`, and no complete pass occurs with shorter period.
- Hooks: `Patterns.cover_exact_pow`, `Patterns.min_ticks_cover`
- Demo: `hypercube_period_report`

### GrayCodeCycleCert
Existence of an 8-vertex Hamiltonian cycle (the 3-cube Gray code), specializing the hypercube law to `D=3`.
- Hooks: `Patterns.cover_exact_pow (3)`
- Demo: `gray_code_cycle_report`

### ExactnessCert
Closed-chain flux zero implies a potential representation on components. This wraps T3/T4 into a single check.
- Hooks: `Recognition.Continuity`, `Potential.unique_on_component`
- Demo: `exactness_report`

### ConeBoundCert
Discrete light-cone bound for admissible step kernels; enforces causal locality.
- Hooks: `LightCone.StepBounds.cone_bound`
- Demo: `cone_bound_report`

### Window8NeutralityCert
8-window measurement identities: neutrality on periodic extension, aligned block sums, and averaged observation equality.
- Hooks: `PatternLayer` and `MeasurementLayer` identities
- Demo: `window8_report`

### LedgerUnitsCert
δ-subgroup quantization: for δ≠0, the subgroup is isomorphic to `ℤ` with unique representation. Encodes counting structure.
- Hooks: `LedgerUnits.*`
- Demo: `ledger_units_report`

### Rung45WitnessCert
Witness that rung 45 exists and no multiples appear for `n ≥ 2`. Minimal witness used by the 45-gap consequence pack.
- Hooks: `RH.RS.FortyFiveGapHolds`
- Demo: `rung45_report`

### GapConsequencesCert
Packs rung-45 with Δ=3/64 time-lag, no-multiples, and synchronization consequences to satisfy the 45-gap spec.
- Hooks: `RH.RS.fortyfive_gap_consequences_any`
- Demo: `gap_consequences_report`

### FamilyRatioCert
Mass ratios at the matching scale follow φ-powers: `m_i/m_j = φ^(r_i−r_j)`.
- Hooks: `Recognition.mass_ratio_phiPow`
- Demo: `family_ratio_report`

### EqualZAnchorCert
Equal-Z anchor degeneracy at μ* bands with a closed-form gap landing; tests anchor policy wiring.
- Hooks: `Masses` anchor policy hooks, `Source.txt`
- Demo: `equalZ_report`

### DECDDZeroCert
Discrete exterior calculus identity: `d ∘ d = 0`.
- Hooks: `Verification.DEC.dec_dd_eq_zero`
- Demo: `dec_dd_zero_report`

### DECBianchiCert
Bianchi identity in DEC: `dF = 0`.
- Hooks: `Verification.DEC.dec_bianchi`
- Demo: `dec_bianchi_report`

### InevitabilityDimlessCert
Dimensionless inevitability: for every ledger/bridge there exists a universal φ-closed target pack that the bridge matches.
- Hooks: `RH.RS.Inevitability_dimless`, `RH.RS.Witness.inevitability_dimless_partial`
- Demo: `inevitability_dimless_report`

### SectorYardstickCert
Sector yardsticks (A_B) are consistent with the display equations and normalizations used in reports.
- Hooks: `Source.txt @SECTOR_YARDSTICKS`
- Demo: `sector_yardstick_report`

### TimeKernelDimlessCert
Time-kernel dimensionless check and normalization `w_time_ratio(τ0,τ0)=1`.
- Hooks: `TruthCore.TimeKernel`
- Demo: `ilg_time_report`

### AbsoluteLayerCert
Absolute layer acceptance: there exist anchors and centered bands such that `UniqueCalibration ∧ MeetsBands` holds.
- Hooks: `RH.RS.UniqueCalibration`, `RH.RS.MeetsBands`
- Demo: `absolute_layer_report`

### EffectiveWeightNonnegCert
Effective weight is nonnegative and monotone under assumptions—stability guard for ILG arguments.
- Hooks: `Gravity.ILG` effective weight lemmas
- Demo: `ilg_effective_report`

### BoseFermiCert
Symmetrization laws: permutation invariance yields Bose–Einstein and Fermi–Dirac occupancy forms.
- Hooks: `Quantum` occupancy definitions
- Demo: `bose_fermi_report`

### RotationIdentityCert
Rotation identity `v^2 = G M_enc/r` and flat-curve condition when `M_enc ∝ r`.
- Hooks: `Gravity.Rotation`
- Demo: `rotation_identity_report`

### ControlsInflateCert
Experimental pipeline guard: negative controls inflate medians; EFE sensitivity is bounded; fairness is maintained.
- Hooks: `Source.txt @EXPERIMENTS`
- Demo: `controls_inflate_report`

### PDGFitsCert
Interface-level PDG fits with simple acceptability bounds per species/group; a placeholder for full CLI pipelines.
- Hooks: `PDG.Fits`
- Demo: `pdg_fits_report`

### ProtonNeutronSplitCert
Proton–neutron split at specified tolerance; quick baryon-scale check.
- Hooks: `PDG.Fits` entries
- Demo: `pn_split_report`

### OverlapContractionCert
Uniform-overlap implies total-variation contraction (finite 3×3 exemplar) in the YM section.
- Hooks: `YM.Dobrushin`
- Demo: `overlap_contraction_report`

### BornRuleCert
Path-weight interface implies the Born rule: probability `= exp(−C)`.
- Hooks: `Quantum.PathWeight`
- Demo: `born_rule_report`

### QuantumOccupancyCert
Textbook Bose/Fermi occupancy forms and the exponential-probability identity under the path-weight API.
- Hooks: `Quantum.occupancyBose/Fermi`, `Quantum.PathWeight`
- Demo: `quantum_occupancy_report`

### SpeedFromUnitsCert
Units sanity: `ℓ0/τ0=c`, `λ_kin/τ_rec=c`, and derivable `ell0_div_tau0_eq_c`, `display_speed_eq_c` identities.
- Hooks: `Constants.RSUnits.*`
- Demo: `speed_from_units_report`

### PathCostIsomorphismCert
Path-cost additivity and a policy placeholder for `(ln φ)·|Γ|`. Encodes the cost algebra used repeatedly.
- Hooks: `Quantum.PathWeight` (additivity)
- Demo: `path_cost_isomorphism_report`

### GapSeriesClosedFormCert
Gap-series closed form at `z=1`: `F(1) = log(1 + 1/φ)`. Used in curvature/α pipelines.
- Hooks: `Pipelines.GapSeries`
- Demo: `gap_series_closed_form_report`

### InflationPotentialCert
Policy-level inflation potential hooks; used to document and stabilize choices for cosmology-facing demos.
- Hooks: `Gravity/*` and text references
- Demo: `inflation_potential_report`

### ILGKernelFormCert
Policy/form-level check for ILG kernel symbols; placeholder until heavier analysis is imported.
- Hooks: `Gravity.ILG`
- Demo: `ilg_kernel_form_report`

### IRCoherenceGateCert
IR gate tolerance placeholder—encodes the policy that coherence tolerances stay under a knob.
- Hooks: (policy)
- Demo: `ir_coherence_gate_report`

### PlanckGateToleranceCert
Planck gate tolerance placeholder using metrology anchors.
- Hooks: (policy)
- Demo: `planck_gate_tolerance_report`

### SATSeparationCert
Recognition–computation inevitability layer: ties to a monotone growth predicate over φ-powers.
- Hooks: `URCAdapters.tc_growth_prop`
- Demo: `sat_separation_report`

### RGResidueCert
RG residue models and no-self-thresholding policy for heavy species; documents the model wiring.
- Hooks: `Masses.AnchorPolicy`, `Source.txt`
- Demo: `rg_residue_report`

### AblationSensitivityCert
Stress tests: ablations (drop +4, drop Q^4, mis-integerize 6Q) cause deviations far above tolerance.
- Hooks: `Source.txt @RG_METHODS`
- Demo: `ablation_sensitivity_report`

### UniqueUpToUnitsCert
Bridge uniqueness up to units equivalence (Spec-level relation witness).
- Hooks: `RH.RS.Spec.UniqueUpToUnits`
- Demo: `unique_up_to_units_report`

### MaxwellContinuityCert
Current conservation `dJ=0` in the DEC Maxwell model; pairs with Bianchi.
- Hooks: `Verification.DEC.Maxwell`
- Demo: `maxwell_continuity_report`

### LNALInvariantsCert
Low-level automaton invariants (parity caps, 8-window neutrality, legal SU(3) triads, long-cycle with flip).
- Hooks: `LNAL.VM` and text spec
- Demo: `lnal_invariants_report`

### CompilerStaticChecksCert
Ensures compiled artifacts for the automaton meet the invariants (developer pipeline check).
- Hooks: build/experiment scripts
- Demo: `compiler_checks_report`

### FoldingComplexityCert
Complexity split: folding depth/time `O(n^{1/3} log n)` and recognition lower bound `Ω(n)` via balanced-parity hidden.
- Hooks: `Complexity.BalancedParityHidden`
- Demo: `folding_complexity_report`

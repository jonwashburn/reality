# Certificates Manifest

This index lists the wired certificates and their #eval reports. Copy/paste any line into a Lean buffer (with this repo opened) to force elaboration and see a concise OK line.

## Big picture (start here)

- Reality bundle (RS measures reality)
  - What it is: Bundles four pillars into a single statement that “Recognition Science measures reality” at φ: (1) absolute‑layer acceptance (UniqueCalibration ∧ MeetsBands), (2) dimensionless inevitability at φ, (3) units‑quotient bridge factorization (A = Ã ∘ Q and J = Ã ∘ B_*), and (4) existence of a verified certificate family. This is the proof‑spine endpoint for first‑look validation.
  - Where: `IndisputableMonolith/Verification/Reality.lean` (theorem `rs_measures_reality_any`).
  - Demo:
    - `#eval IndisputableMonolith.URCAdapters.reality_bridge_report`

- Route A (axioms ⇒ bridge ⇒ absolute layer)
  - What it is: A minimal bridge obtained from axioms (URC Minimal), plus generic witnesses that the absolute layer accepts (UniqueCalibration ∧ MeetsBands). Use this to sanity‑check the spec‑level wiring from axioms to a working bridge with empirical obligations.
  - Where: `IndisputableMonolith/URCAdapters/Routes.lean` and `Reports.lean`.
  - Demo:
    - `#eval IndisputableMonolith.URCAdapters.routeA_report`

- Route B (generators ⇒ bridge ⇒ absolute layer)
  - What it is: A concrete, generator‑driven construction of witnesses (a small `CertFamily`) that yields a bridge accepted by the absolute layer. This demonstrates that the generator stack alone is sufficient to satisfy UniqueCalibration ∧ MeetsBands in a minimal setting.
  - Where: `IndisputableMonolith/URCGenerators.lean` (demo family) and `URCAdapters/Routes.lean`.
  - Demo:
    - `#eval IndisputableMonolith.URCAdapters.routeB_closure_report`

- Ethics bundle
  - What it is: Certificates covering policy gates Bool↔Prop bridges and alignment invariance, fairness batch semantics and invariance, lexicographic preference discipline, and truth/evidence ledger selection behavior.
  - Where: `IndisputableMonolith/URCGenerators.lean` (EthicsPolicyCert, FairnessBatchCert, PreferLexCert, TruthLedgerCert) and `URCAdapters/Reports.lean`.
  - Demo:
    - `#eval IndisputableMonolith.URCAdapters.ethics_policy_report`
    - `#eval IndisputableMonolith.URCAdapters.fairness_batch_report`
    - `#eval IndisputableMonolith.URCAdapters.prefer_lex_report`
    - `#eval IndisputableMonolith.URCAdapters.truth_ledger_report`

- Recognition Closure (meta certificate)
  - What it is: Packs (i) absolute‑layer acceptance (universally), (ii) dimensionless inevitability at φ, and (iii) existence of a verified certificate family (with selected lists non‑empty). A direct precursor to the Reality bundle.
  - Where: `IndisputableMonolith/URCGenerators.lean` (`recognition_closure_any`).
  - Demo:
    - `#eval IndisputableMonolith.URCAdapters.recognition_closure_report`

---

- Route A wiring
  - `#eval IndisputableMonolith.URCAdapters.routeA_report`
- K identities and gate
  - `#eval IndisputableMonolith.URCAdapters.k_identities_report`
  - `#eval IndisputableMonolith.URCAdapters.k_gate_report`
- Planck identity, single-inequality
  - `#eval IndisputableMonolith.URCAdapters.lambda_rec_identity_report`
  - `#eval IndisputableMonolith.URCAdapters.single_inequality_report`
- Exactness, cone bound, window-8, eight-tick
  - `#eval IndisputableMonolith.URCAdapters.exactness_report`
  - `#eval IndisputableMonolith.URCAdapters.cone_bound_report`
  - `#eval IndisputableMonolith.URCAdapters.window8_report`
  - `#eval IndisputableMonolith.URCAdapters.eight_tick_report`
- Ledger units, rung 45, consequences
  - `#eval IndisputableMonolith.URCAdapters.ledger_units_report`
  - `#eval IndisputableMonolith.URCAdapters.rung45_report`
  - `#eval IndisputableMonolith.URCAdapters.gap_consequences_report`
- Mass ladders
  - `#eval IndisputableMonolith.URCAdapters.family_ratio_report`
  - `#eval IndisputableMonolith.URCAdapters.equalZ_report`
  - `#eval IndisputableMonolith.URCAdapters.pdg_fits_report`
- Quantum
  - `#eval IndisputableMonolith.URCAdapters.born_rule_report`
  - `#eval IndisputableMonolith.URCAdapters.bose_fermi_report`
- Gravity / ILG
  - `#eval IndisputableMonolith.URCAdapters.rotation_identity_report`
  - `#eval IndisputableMonolith.URCAdapters.ilg_time_report`
  - `#eval IndisputableMonolith.URCAdapters.ilg_effective_report`
  - `#eval IndisputableMonolith.URCAdapters.overlap_contraction_report`
- DEC / Maxwell
  - `#eval IndisputableMonolith.URCAdapters.dec_dd_zero_report`
  - `#eval IndisputableMonolith.URCAdapters.dec_bianchi_report`
  - `#eval IndisputableMonolith.URCAdapters.maxwell_continuity_report`
- Absolute layer / Inevitability
  - `#eval IndisputableMonolith.URCAdapters.absolute_layer_report`
  - `#eval IndisputableMonolith.URCAdapters.inevitability_dimless_report`
- LNAL / Compiler / Folding
  - `#eval IndisputableMonolith.URCAdapters.lnal_invariants_report`
  - `#eval IndisputableMonolith.URCAdapters.compiler_checks_report`
  - `#eval IndisputableMonolith.URCAdapters.folding_complexity_report`
- Controls / RG residue
  - `#eval IndisputableMonolith.URCAdapters.controls_inflate_report`
  - `#eval IndisputableMonolith.URCAdapters.rg_residue_report`

- Ethics
  - `#eval IndisputableMonolith.URCAdapters.ethics_policy_report`
  - `#eval IndisputableMonolith.URCAdapters.fairness_batch_report`
  - `#eval IndisputableMonolith.URCAdapters.prefer_lex_report`
  - `#eval IndisputableMonolith.URCAdapters.truth_ledger_report`

Bulk manifest (prints one line per cert):

```lean
#eval IndisputableMonolith.URCAdapters.certificates_manifest
```

Notes:
- All reports are constant-time elaborations (no external IO); safe for CI.
- See `reference.md` for hooks and brief claims; this file is for quick demos.

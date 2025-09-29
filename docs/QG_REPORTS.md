## Quantum Gravity (ILG) Certificates and Reports

This page lists the ILG/QG certificates with their `#eval` report endpoints and expected outputs. Evaluate these inside `IndisputableMonolith/URCAdapters/Reports.lean` (Lean editor) or use them as references for CI harnessing.

### How to run

1) Build the project

```bash
lake build
```

2) In your editor, open `IndisputableMonolith/URCAdapters/Reports.lean` and place the cursor on a line with `#eval …` then run it. The corresponding string should print in the infoview.

---

### Consolidated harness

```lean
#eval IndisputableMonolith.URCAdapters.qg_harness_report
-- Expected: "QGHarness: PASS"

#eval IndisputableMonolith.URCAdapters.falsifiers_harness_report
-- Expected: "FalsifiersHarnessCert: OK"
```

---

### Weak‑field and linearization

```lean
#eval IndisputableMonolith.URCAdapters.weakfield_derive_report
-- Expected: "WeakFieldDeriveCert: OK"

#eval IndisputableMonolith.URCAdapters.w_link_O_report
-- Expected: "WLinkOCert: OK"
```

### PPN derivation

```lean
#eval IndisputableMonolith.URCAdapters.ppn_derive_report
-- Expected: "PPNDeriveCert: OK"
```

### Lensing and time delay

```lean
#eval IndisputableMonolith.URCAdapters.cluster_lensing_derive_report
-- Expected: "ClusterLensingDeriveCert: OK"
```

### FRW cosmology and growth

```lean
#eval IndisputableMonolith.URCAdapters.frw_derive_report
-- Expected: "FRWDeriveCert: OK"

#eval IndisputableMonolith.URCAdapters.growth_report
-- Expected: "GrowthCert: OK"

#eval IndisputableMonolith.URCAdapters.cmb_bao_bbn_bands_report
-- Expected: "CMBBAOBBNBandsCert: OK"

#eval IndisputableMonolith.URCAdapters.bands_from_params_report
-- Expected: "BandsFromParamsCert: OK"
```

### Gravitational waves

```lean
#eval IndisputableMonolith.URCAdapters.gw_derive_report
-- Expected: "GWDeriveCert: OK"

#eval IndisputableMonolith.URCAdapters.gw_quadratic_report
-- Expected: "GWQuadraticCert: OK"
```

### Compact objects (static BH proxy)

```lean
#eval IndisputableMonolith.URCAdapters.bh_derive_report
-- Expected: "BHDeriveCert: OK"
```

### Quantum substrate

```lean
#eval IndisputableMonolith.URCAdapters.micro_unitary_report
-- Expected: "MicroUnitaryCert: OK"

#eval IndisputableMonolith.URCAdapters.micro_unitary_completion_report
-- Expected: "MicroUnitaryCompletionCert: OK"
```

---

### Notes
- All reports return human‑readable "OK" strings when their certificate predicates elaborate.
- The consolidated harness intentionally touches representative reports across domains; any breakage will surface there first.
- These scaffolds are designed to compile now and provide gates for future, tighter derivations without changing public endpoints.



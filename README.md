# recognition

[![CI](https://github.com/jonwashburn/recognition/actions/workflows/ci.yml/badge.svg)](https://github.com/jonwashburn/recognition/actions/workflows/ci.yml)

Recognition Science begins from a single logical observation: absolute nothingness cannot recognize itself. From that minimal starting point, a structure of recognition events is forced, and with it a ledger that counts, balances, and conserves the cost of alteration. When one demands that this structure be self‑similar across scales and minimally costly, a unique scaling constant emerges—the golden ratio φ—and with it a clock of eight ticks, a gauge‑rigid bridge from proofs to observables, and a separation between the cost of computing and the cost of recognizing outcomes. This repository is the mechanized realization of that story. It is not a loose collection of ideas or a numerical fit, but a Lean‑verified spine where every claim is wired to a proof, a check, or a certificate that can be elaborated on your machine.

The codebase is organized so that a new reader can both grasp the high‑level picture and immediately validate it. The master “reality” bundle packages four pillars—absolute‑layer acceptance, dimensionless inevitability at φ, units‑quotient bridge factorization, and the existence of a verified certificate family—and proves them together. Around this spine sit domain certificates for measurement, causality, quantum statistics, mass ladders, and complexity. Reports expose human‑readable “OK” outputs for first‑look validation, and CI smoke targets ensure the toolchain stays green. No tunable parameters are introduced in the proofs; empirical landings live only at the bridge, where they belong.

## What this repository is

- A Lean 4/Lake project that assembles a proof spine from MP ⇒ ledger necessity ⇒ golden‑ratio scaling φ ⇒ 8‑beat temporality (2^3) ⇒ units‑quotient bridge ⇒ absolute‑layer acceptance ⇒ recognition/computation split. Core results are available as Lean theorems and certificate families.
- Designed for artifact‑backed verification: quick smoke checks, `#eval` reports, and navigable modules to validate claims at first look.

## What is formally proved (high‑level)

- MP holds (empty type cannot recognize itself): `IndisputableMonolith/Recognition.lean` (`mp_holds`).
- Bridge factorization (gauge‑rigid displays): `IndisputableMonolith/Verification/Verification.lean` (`bridge_factorizes`).
- Dimensionless inevitability at φ (spec witness): `IndisputableMonolith/RH/RS/Witness.lean`.
- Absolute‑layer acceptance (UniqueCalibration ∧ MeetsBands) via generators: `IndisputableMonolith/URCGenerators.lean` (`AbsoluteLayerCert.verified_any`).
- Recognition Closure (meta certificate): `IndisputableMonolith/URCGenerators.lean` (`recognition_closure_any`).
- RS measures reality (bundled): `IndisputableMonolith/Verification/Reality.lean` (`rs_measures_reality_any`).
- Complexity split (exemplar): `IndisputableMonolith/URCGenerators.lean` (`FoldingComplexityCert.verified_any`).

See also `Measurement.txt` for the human‑readable derivation (ledger necessity, φ from self‑similarity, eight‑beat minimality).

## Validate in under a minute

1) Install toolchain

```bash
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | bash -s -- -y
source "$HOME/.elan/env"
```

2) Build and smoke check

```bash
lake build
lake exe ci_checks
# prints: CI smoke: toolchain OK, minimal URC intact.
```

3) Optional: open `IndisputableMonolith/URCAdapters/Reports.lean` and evaluate report endpoints (editor `#eval`)

```lean
#eval IndisputableMonolith.URCAdapters.reality_bridge_report
#eval IndisputableMonolith.URCAdapters.recognition_closure_report
#eval IndisputableMonolith.URCAdapters.k_gate_report
#eval IndisputableMonolith.URCAdapters.k_identities_report
```

These report strings are wired through the proof spine and are convenient first‑look “OK” indicators in the editor.

## Key modules to browse first

- Reality bundle: `IndisputableMonolith/Verification/Reality.lean` (definition and theorem `rs_measures_reality_any`).
- Generators & certificates: `IndisputableMonolith/URCGenerators.lean` (`CertFamily`, `Verified`, `recognition_closure_any`).
- Reports (human‑readable checks): `IndisputableMonolith/URCAdapters/Reports.lean`.
- RS spec layer (structural obligations): `IndisputableMonolith/RH/RS/Spec.lean` and witnesses in `RH/RS/Witness.lean`.
- Certificate catalog: `reference.md` (plain‑language claims and hooks) and `CERTIFICATES.md` (copy‑paste `#eval` manifest).

## Core certificate families (sampler)

- Units/gauge/K‑gate: `UnitsInvarianceCert`, `UnitsQuotientFunctorCert`, `SpeedFromUnitsCert`, `KGateCert`, `KIdentitiesCert`, `LambdaRecIdentityCert`, `PlanckLengthIdentityCert`, `SingleInequalityCert`.
- Time/structure (8‑beat): `EightTickMinimalCert`, `EightBeatHypercubeCert`, `GrayCodeCycleCert`, `Window8NeutralityCert`.
- Causality/quantization: `ConeBoundCert`, `LedgerUnitsCert`, `UniqueUpToUnitsCert`.
- Mass/φ‑rungs & data: `MassCert`, `FamilyRatioCert`, `RGResidueCert`, `PDGFitsCert`, `AblationSensitivityCert`.
- Quantum/stat mech: `BornRuleCert`, `QuantumOccupancyCert`, `PathCostIsomorphismCert`.
- Complexity: `FoldingComplexityCert`.
- Meta: `AbsoluteLayerCert`, `InevitabilityDimlessCert`.

All are aggregated in `CertFamily` and checked by `Verified φ C` (`URCGenerators.lean`).

## Reproducibility

- Toolchain: see `lean-toolchain`; dependencies in `lake-manifest.json`.
- CI: GitHub Actions workflow installs elan, builds, and runs the smoke check.

## Contributing

- Add new results as small certificates: define `XCert`, specify `XCert.verified`, and prove `[simp] theorem XCert.verified_any`. Register in `CertFamily` and extend `Verified` as needed.

## Contact

- Email: washburn@recognitionphysics.org
- Twitter: @jonwashburn
- Or open issues/discussions on this repository.


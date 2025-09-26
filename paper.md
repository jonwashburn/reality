---
title: "Recognition Science: A Lean 4, Certificates‑First Verification Instrument"
tags:
  - Lean 4
  - formal methods
  - verification
  - physics foundations
  - reproducibility
authors:
  - name: Jonathan Washburn
    orcid: 0000-0000-0000-0000
    affiliation: 1
affiliations:
  - name: Independent Researcher
    index: 1
date: 2025-09-25
bibliography: paper.bib
---

# Summary

This software package is a Lean 4 verification instrument that exposes a certificates‑first, reproducible proof spine for a parameter‑free physics framework. From a single foundational proposition ("nothing cannot recognize itself"), the package derives and bundles verifiable statements into machine‑checked propositions with one‑line `#eval` reports on a pinned toolchain. The core artifact comprises:

- a reality bundle plus spec‑level closure (RSRealityMaster),
- a closed theorem stack (PrimeClosure) with a minimality result (MPMinimal),
- an exclusivity and bi‑interpretability upgrade at a uniquely pinned scale (ExclusiveRealityPlus),
- coherence of canonical units classes and a category‑theory equivalence at that scale, and
- an apex bundle (UltimateClosure) combining these properties with a uniqueness statement for the scale.

All checks are pure Lean terms with no external I/O. A minimal CI smoke (`lake exe ci_checks`) exercises the scaffold; a consolidated manifest prints an `OK` line per certificate. The codebase is open source (MIT) and designed as a reusable, deterministic instrument: any broken identity flips a report or prevents elaboration.

# Statement of need

Researchers need verifiable, open instruments to audit claims that are otherwise narrative or numerically fragile. This package provides a compact, pinned toolchain that turns key propositions into immediately checkable, machine‑verified reports. It is useful for communities working on formal methods in physics and mathematics, and for verification tooling more broadly: the architecture demonstrates how to expose complex proofs as reproducible gauges with one‑click reports, CI smoke, and no runtime data dependencies.

# Functionality

- Pinned Lean 4 toolchain and Lake build; constant‑time elaboration of reports.
- Reality bundle & spec closure: `#eval IndisputableMonolith.URCAdapters.reality_master_report`.
- Closed theorem stack (PrimeClosure), exclusivity+bi‑interpretability (ExclusiveRealityPlus), and apex UltimateClosure with uniqueness.
- Coherence of canonical units classes and categorical equivalence at the pinned scale.
- φ‑only evaluator for the inverse fine‑structure constant (Proven; compared by an automated comparator against measurements).
- CI: audit comparator is the hard gate; `ci_checks` is attempted but currently non‑gating while import cycles are being repaired; a consolidated manifest prints an `OK` per certificate.

# Quality control

The repository includes a deterministic CI smoke and a consolidated manifest of `#eval` checks. Reports are constructed as pure terms (no network/file I/O). The toolchain is pinned via `lean-toolchain` and dependencies locked in `lake-manifest.json` to ensure byte‑for‑byte reproducibility. A machine‑readable audit (`lake exe audit`) is compared against `measurements.json` by a non‑interactive comparator script (`./scripts/audit_compare.sh`) that fails the run on any Proven mismatch (exact or |z|>3), and treats Scaffold/Planned as non‑gating visibility.

# Example

```text
elan toolchain install $(cat lean-toolchain)
lake build
lake exe ci_checks
-- inside Lean editor, evaluate:
#eval IndisputableMonolith.URCAdapters.reality_master_report
```

Optional single‑line checks (examples):

```text
#eval IndisputableMonolith.URCAdapters.closed_theorem_stack_report
#eval IndisputableMonolith.URCAdapters.exclusive_reality_plus_report
#eval IndisputableMonolith.Verification.RecognitionReality.ultimate_closure_report
```

Audit (hard gate in CI):

```text
lake build
lake exe audit
./scripts/audit_compare.sh
```

# Installation

```text
elan toolchain install $(cat lean-toolchain)
source "$HOME/.elan/env"
lake build
```

# Usage

- In an editor (Lean 4), evaluate `#eval` reports such as:
  - `#eval IndisputableMonolith.URCAdapters.reality_master_report`
  - `#eval IndisputableMonolith.URCAdapters.closed_theorem_stack_report`
  - `#eval IndisputableMonolith.Verification.RecognitionReality.ultimate_closure_report`
- From the CLI, produce the consolidated summary:
  - `lake exe ok` (pretty JSON available via `--json`)
- Run the audit comparator (hard gate):
  - `lake exe audit` then `./scripts/audit_compare.sh`

# Testing

- The audit comparator enforces correctness of all Proven invariants against `measurements.json` (exact or z‑score ≤ 3). Scaffold/Planned items are surfaced as WARN/INFO but do not gate.
- A minimal CI smoke `lake exe ci_checks` is executed but currently non‑gating while upstream import cycles are being repaired; the audit comparator remains the hard CI gate.

# Software availability and archival

- License: MIT (see `LICENSE`).
- Source: `https://github.com/jonwashburn/recognition`.
- A release will be archived on Zenodo at acceptance; DOI badge is included in the README and will be updated upon archival.

# Acknowledgments

The author thanks collaborators and the Lean community for tooling and libraries that made this work possible.

# Conflict of interest

The author declares no competing interests.

# References

See the bibliography for related work and background.


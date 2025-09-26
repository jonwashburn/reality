## JOSS Submission Steps

This document collects the concrete steps and links needed to submit this repository to JOSS.

### 1) Prepare the repository
- Ensure the following files exist and are current:
  - `paper.md` and `paper.bib`
  - `README.md` (quickstart, usage, CI, audit surface)
  - `LICENSE`, `CITATION.cff`, `CODE_OF_CONDUCT.md`, `CONTRIBUTING.md`
  - `REVIEWERS.md` (quick verification path)
  - `CHANGELOG.md` (v1.0.0)
- Tag a release v1.0.0 and archive on Zenodo; record the DOI in `CITATION.cff` and README badge.

### 2) Verify artifact locally
```bash
elan toolchain install $(cat lean-toolchain)
source "$HOME/.elan/env"
lake build
lake exe ci_checks
lake exe audit | tee .out.json
./scripts/audit_compare.sh .out.json measurements.json
```
Expect PASS for all Proven items.

### 3) Submit to JOSS
- Go to the JOSS submission form: https://joss.theoj.org/papers/new
- Provide the repository URL, tagged version, and archive DOI.
- Paste the `paper.md` content and upload figures (if any).
- List suggested reviewers (Lean/PL + physics verification background), and include a link to `REVIEWERS.md`.

### 4) During review
- Track review issues in the JOSS reviews repo and mirror open tasks as GitHub issues here.
- Use the included CI (smoke + audit gate) to keep the artifact reproducible.

### 5) After acceptance
- Update README DOI badge with the final DOI.
- Create a GitHub release post summarizing v1.0.0 (link to `CHANGELOG.md`).


# v1.0.0 Release Notes

## Highlights
- UltimateClosure certificate; φ equality lemma; RecognitionReality bundle
- Exclusivity + bi-interpretability consolidated at the pinned φ
- φ-only α evaluator (Proven) matches PDG precision within comparator rules
- Unitless audit: JSON instrument + comparator (hard CI gate); cosmology tracked as non-gating
- Docs: machine-verified.tex updated; REVIEWERS.md and SUBMISSION.md added
- CI: smoke check + audit comparator; classical helper fenced

## Quick verification
```bash
elan toolchain install $(cat lean-toolchain)
source "$HOME/.elan/env"
lake build
lake exe ci_checks
lake exe audit | tee .out.json
./scripts/audit_compare.sh .out.json measurements.json
```
Expected: smoke OK; comparator PASS for Proven items, WARN for Scaffold, INFO for Planned.

## Notes
- Tagged v1.0.0; Zenodo archive prepared (see CITATION.cff/README badge for DOI).
- For a reviewer path, see REVIEWERS.md.

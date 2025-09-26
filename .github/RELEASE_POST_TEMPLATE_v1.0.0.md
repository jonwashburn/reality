# Recognition Science v1.0.0

This release tags the first complete, machine-verified spine and reproducible audit harness.

## Highlights
- UltimateClosure certificate; φ equality and RecognitionReality bundle
- Exclusivity + bi-interpretability at pinned φ (no knobs; units-quotient bridge; K-gate)
- φ-only α evaluator (Proven) and audit comparator as hard CI gate
- Docs: machine-verified.tex, REVIEWERS.md, SUBMISSION.md; CI smoke + audit gate

## Verify locally
```bash
elan toolchain install $(cat lean-toolchain)
source "$HOME/.elan/env"
lake build
lake exe ci_checks
lake exe audit | tee .out.json
./scripts/audit_compare.sh .out.json measurements.json
```

## Links
- Changelog: CHANGELOG.md
- Release notes: RELEASE_NOTES_v1.0.0.md
- Reviewer path: REVIEWERS.md
- JOSS prep: JOSS_PREP.md

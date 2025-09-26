---
name: JOSS Review Checklist
about: Checklist for JOSS editorial/reviewer tasks
title: "JOSS review: <replace-with-version>"
labels: review, joss
assignees: ''
---

- [ ] Repository is public, OSI license present
- [ ] Build instructions work (`elan`, `lake build`)
- [ ] Smoke check passes (`lake exe ci_checks`)
- [ ] Unitless audit comparator passes for Proven items
- [ ] Paper: `paper.md` + `paper.bib` present, scope and references OK
- [ ] Documentation quality (README quickstart, REVIEWERS.md, SUBMISSION.md)
- [ ] Functionality: artifact works as described (CLI summary, reports)
- [ ] Community standards: CONTRIBUTING, CODE_OF_CONDUCT, CITATION.cff
- [ ] Version/tag archived (Zenodo) and DOI recorded

Notes:

```
elan toolchain install $(cat lean-toolchain)
source "$HOME/.elan/env"
lake build
lake exe ci_checks
lake exe audit | tee .out.json
./scripts/audit_compare.sh .out.json measurements.json
```


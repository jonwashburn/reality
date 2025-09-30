# ILG Implementation Requeue Prompts

Use these prompts to continue ILG implementation in future sessions.

---

## Option 1: Continue Geometry (Phase 1)

```
@ILG_IMPLEMENTATION_PLAN.md @ILG_STATUS.md 

Please continue Phase 1 (Differential Geometry). The Manifold and Tensor modules compile successfully. Fix the type signature issues in Connection.lean (covariant derivative should return correct VectorField type) and get all geometry modules building. Then prove minkowski_riemann_zero and minkowski_ricci_zero without using 'sorry'.

Update ILG_IMPLEMENTATION_PLAN.md and ILG_STATUS.md with progress when done.
```

---

## Option 2: Honest Scaffolding Documentation (Recommended)

```
@ILG_IMPLEMENTATION_PLAN.md @ILG_STATUS.md

Follow the "Fallback Strategy (If Full Implementation Too Hard)" section. Update docs/QG_PRD.tex, docs/QG_DISCOVERY_INTERNAL.tex, and paper abstracts to:
1. Remove claims about "derived" field equations
2. Present ILG as "proposed framework with type-safe scaffolding"  
3. Emphasize proven recognition spine work (φ-rungs, particle masses, 3 generations)
4. Add clear "Scaffold vs Proven" sections

Create docs/ILG_README.md warning that modules are placeholders.

Update ILG_STATUS.md when complete.
```

---

## Option 3: Simplified Physics Approach

```
@ILG_IMPLEMENTATION_PLAN.md

Implement a simplified "physics notation" version of Phase 1 using:
- Matrices (Fin 4 × Fin 4 → ℝ) instead of abstract tensors
- Mathlib.Data.Matrix for det, inv operations  
- Direct formulas for Christoffel, Riemann without heavy abstraction

This sacrifices mathematical elegance but gets working code faster. Start by creating IndisputableMonolith/Relativity/MatrixGR/ with simpler structures.
```

---

## Option 4: Partner with Expert

```
I need help implementing differential geometry in Lean 4 for the ILG project. 

Context: See @ILG_IMPLEMENTATION_PLAN.md and @ILG_STATUS.md for current state.

Question: Should we:
(a) Use existing Mathlib.Geometry.Manifold structures?
(b) Build minimal matrix-based tensor calculus?
(c) Wait for Mathlib differential geometry to mature?

Current blocker: Type signatures for covariant derivatives and tensor indexing with Fin M.dim.
```

---

## Recommended Next Action

Based on timeline and goals, I recommend **Option 2** (Honest Documentation) because:

1. **Time**: Full GR formalization is 3-4 months minimum
2. **Expertise**: Requires differential geometry + Lean 4 expert
3. **Value**: Recognition spine work is already impressive and proven
4. **Honesty**: Protects credibility; shows what's real

After honest documentation, you can:
- Submit recognition spine papers (particle masses, 3 generations)
- Collaborate on ILG geometry later
- Keep phenomenological w(r) papers (rotation curves) separate

---

## Status Check Commands

Before requeueing, check current status:

```bash
lake build IndisputableMonolith.Relativity.Geometry
lake build IndisputableMonolith.Relativity.ILG.Action  
cat docs/ILG_STATUS.md
```

---

## Quick Win: Just Fix What's There

```
@ILG_STATUS.md

The existing ILG scaffold modules compile and pass CI. Add honest documentation to each:

1. Add to top of each IndisputableMonolith/Relativity/ILG/*.lean file:
   /-! WARNING: This module is a type-safe scaffold. Physics derivations are placeholders.
       Most predicates are defined as `True` and theorems proven by `trivial`.
       See docs/ILG_STATUS.md for implementation roadmap. -/

2. Update paper abstracts to match reality

3. Create docs/SCAFFOLD_DISCLAIMER.md explaining the approach

This takes 1 hour vs 3 months and lets you publish honestly.
```

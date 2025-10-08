# GRLimitParameterFacts - Work in Progress

## Goal
Prove that α = (1 - 1/φ)/2 and C_lag = φ^(-5) from RS satisfy:
1. Both < 1 ✅ PROVEN
2. Product < 0.02 ⚠️ NEEDS INTERVAL ARITHMETIC
3. Product < 0.1 ⚠️ DEPENDS ON #2

## What I've Done
✅ Uncommented the Parameters.lean file  
✅ Proven `rs_params_small`: both α and C_lag are < 1  
✅ Shown both parameters are positive  
✅ Set up the structure for the product bounds

## What's Blocking Me
The bounds |α · C_lag| < 0.02 require proving:
- (1 - 1/φ)/2 * φ^(-5) < 0.02

Where φ = (1+√5)/2 ≈ 1.618...

This needs ONE of:
1. **Interval arithmetic**: Prove 1.61 < φ < 1.62, then bound the product
2. **Rational approximations**: Use 809/500 < φ < 810/500 (computable)
3. **Verified computation**: Use Lean's `norm_num` plugin (if it handles rpow)

## Mathematical Sketch (needs formalization)
- √5 ∈ (2.236, 2.237) by squaring
- φ = (1+√5)/2 ∈ (1.618, 1.6185)
- 1/φ ∈ (0.6179, 0.6181)
- α = (1-1/φ)/2 ∈ (0.1909, 0.1910)
- φ^5 ∈ (11.08, 11.10) by repeated multiplication
- C_lag = φ^(-5) ∈ (0.0901, 0.0903)
- Product ∈ (0.0172, 0.0173) < 0.02 ✓

## Next Steps
1. Add interval arithmetic helper lemmas for √5
2. Prove tight bounds on φ
3. Bound φ^5 using those bounds
4. Complete the product estimate
5. Remove stub from NewFixtures.lean

## Time Estimate
This is REAL mathematical work - probably 30-60 minutes to formalize properly with all the intermediate lemmas.

## Alternative
If numerical bounds are impractical in pure Lean, we could:
- Use `sorry` with detailed justification (but user explicitly said NO)
- Keep as axiom with justification (same problem)
- Import a numerical computation library
- **Or just do the work** with rational arithmetic


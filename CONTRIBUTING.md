# Contributing to Recognition Science Formalization

Welcome! This repository contains the formal Lean proofs for Recognition Science, a zero-parameter framework for fundamental physics.

## Repository Structure

```
IndisputableMonolith/
├── Constants/          # φ, α, w₈, and other fundamental constants
├── Numerics/           # Interval arithmetic and numeric bounds
├── Astrophysics/       # M/L derivation and stellar structure
├── Consciousness/      # Light-consciousness theorem
├── Relativity/         # GR limit and cosmological tests
├── Cost/               # J-cost functional uniqueness
├── Foundation/         # Recognition operator and Hamiltonian emergence
├── Patterns/           # Eight-tick scheduler and Gray codes
├── Measurement/        # Born rule and path integrals
└── Verification/       # Exclusivity and parameter-freedom proofs

data/certificates/      # JSON certificates for numeric constants
scripts/                # Verification and CI tools
```

## Development Workflow

### 1. Adding Numeric Proofs

When adding bounds for a new constant:

#### Step 1: Interval Arithmetic
Use rational bounds to prove inequalities. Example from `Numerics/Interval.lean`:

```lean
theorem sqrt5_bounds :
  (2236067977 / 1000000000 : ℝ) < Real.sqrt 5 ∧
  Real.sqrt 5 < (2236067978 / 1000000000 : ℝ) := by
  constructor
  · -- Lower: prove (lower)² < 5
    have hsq : (2236067977 / 1000000000 : ℝ) ^ 2 < 5 := by norm_num
    -- Use sqrt monotonicity...
```

**Pattern**:
1. Choose rational endpoints `L`, `U` with `L < target < U`
2. Prove `L² < value²` (or use log, exp, etc.)
3. Apply monotonicity to get `L < value < U`
4. Chain inequalities to propagate bounds

#### Step 2: High-Precision Bounds
For tighter bounds, use Taylor series:

```lean
lemma log_one_add_bounds (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (n : ℕ) :
    (-(∑ i ∈ Finset.range n, (-t) ^ (i + 1) / (i + 1)) - t ^ (n + 1) / (1 - t) ≤
        Real.log (1 + t)) ∧
      (Real.log (1 + t) ≤
        -(∑ i ∈ Finset.range n, (-t) ^ (i + 1) / (i + 1)) + t ^ (n + 1) / (1 - t)) := by
  -- Use Real.abs_log_sub_add_sum_range_le from Mathlib
```

**Use `n=20` for 10-digit precision, `n=60` for ultra-precision**.

#### Step 3: Computational Certificate
For noncomputable values, provide external verification:

```json
// data/certificates/my_constant.json
{
  "my_constant": 2.71828182845,
  "tolerance": 1e-10,
  "checksum": "sha256:abc123...",
  "provenance": "Computed from series with n=100 terms"
}
```

Then add verification to `scripts/verify_certs.py`:

```python
def verify_my_constant():
    data = load_json('data/certificates/my_constant.json')
    # Recompute from definition
    computed = compute_my_constant_from_first_principles()
    if abs(computed - data['my_constant']) <= data['tolerance']:
        ok("my_constant within tolerance")
    else:
        fail(f"my_constant mismatch: {computed} vs {data['my_constant']}")
```

### 2. Axiom Guidelines

#### When to Use Axioms

**✅ Acceptable**:
- **Numeric certificates**: External computation with checksum
  ```lean
  axiom w8_value : w8_from_eight_tick = 2.488254397846
  ```
  *Must have*: JSON certificate + `verify_certs.py` check

- **Classical math results**: Standard theorems not yet in Mathlib
  ```lean
  axiom real_cosh_exp : ∀ t : ℝ, Real.cosh t = (Real.exp t + Real.exp (-t)) / 2
  ```
  *Must have*: Comment citing standard reference

- **Empirical constraints**: Observational data
  ```lean
  axiom RS_satisfies_cassini : |gamma_RS - 1| < 2.3e-5
  ```
  *Must have*: Citation to experiment (Cassini mission data)

- **Structural claims**: Core RS theoretical assertions
  ```lean
  axiom only_abelian_gauge : ∀ cp, gauge_group cp = U1
  ```
  *Must have*: Reference to Source.txt derivation + roadmap for proof

#### When to Prove

**⛔ Never use axiom for**:
- Consequences of existing axioms
- Pure logical/arithmetic facts
- Properties provable from definitions
- Anything computable in Lean

### 3. Code Style

#### Naming Conventions
- **Theorems**: `snake_case` describing what they prove
  - `phi_tight_bounds`, `log_phi_bounds`, `alpha_clag_product_bound`
- **Axioms**: `snake_case` with `_cert` suffix for certificates
  - `w8_value_cert`, `alphaInv_predicted_value_cert`
- **Definitions**: `camelCase` for structures, `snake_case` for functions
  - `StellarConfiguration`, `mass_to_light`

#### Documentation
Every axiom and major theorem needs a docstring:

```lean
/-- Brief one-line summary.

    Longer explanation with:
    - Physical motivation
    - Mathematical content
    - Provenance (where it comes from)
    
    References:
    - Source.txt lines X-Y
    - Paper.tex section Z
    - Notebook cell [hash] -/
axiom my_claim : Prop
```

#### Proof Strategy
- **Prefer explicit proofs** over tactics when teaching
- **Use `norm_num`** for numeric verification
- **Chain calc blocks** for multi-step inequalities
- **Factor common patterns** into helper lemmas

### 4. Testing

#### Before Committing
```bash
# Build everything
lake build

# Check for sorries
bash scripts/check_sorries.sh

# Verify certificates
python3 scripts/verify_certs.py

# Run axiom census
python3 scripts/axiom_census.py
```

#### CI Pipeline
All PRs must pass:
- `lake build` (full compilation)
- Sorry gate (no new sorries in `IndisputableMonolith/`)
- Certificate verification
- Axiom count stability (no unjustified increases)

### 5. Certificate Workflow

#### Creating a New Certificate

**Step 1**: Compute the value externally
```python
# notebooks/compute_my_constant.py
import mpmath
mpmath.dps = 50  # 50 decimal places

def compute_my_constant():
    # High-precision computation
    result = mpmath.log(mpmath.phi)
    return float(result)

value = compute_my_constant()
checksum = hashlib.sha256(str(value).encode()).hexdigest()
```

**Step 2**: Create JSON certificate
```json
{
  "my_constant": 0.4812118250596,
  "tolerance": 1e-12,
  "checksum": "sha256:...",
  "method": "mpmath with dps=50",
  "dependencies": ["phi"],
  "verified_date": "2025-10-30"
}
```

**Step 3**: Add Lean axiom
```lean
/-- My constant = ... (certificate-verified value).
    
    Computed externally using [method].
    Certificate: data/certificates/my_constant.json
    Checksum: sha256:... -/
axiom my_constant_value_cert : my_constant = 0.4812118250596

lemma my_constant_value : my_constant = 0.4812118250596 :=
  my_constant_value_cert
```

**Step 4**: Add verifier
```python
# In scripts/verify_certs.py
def verify_my_constant():
    data = load_json('data/certificates/my_constant.json')
    recomputed = compute_from_definition()
    assert abs(recomputed - data['my_constant']) <= data['tolerance']
```

**Step 5**: Document
Add to `AXIOM_INVENTORY.md` under "Numeric Certificate" category.

### 6. Eliminating Sorries

When you find a `sorry`:

#### Option A: Prove it
```lean
-- Before:
theorem my_claim : x < y := by sorry

-- After:
theorem my_claim : x < y := by
  have h1 : x < z := my_lemma
  have h2 : z < y := other_lemma
  exact lt_trans h1 h2
```

#### Option B: Convert to axiom (if justified)
```lean
-- Before:
theorem unprovable_claim : hard_statement := by sorry

-- After:
/-- Hard statement (pending proof).
    
    This is a core claim of Recognition Science. The classical derivation
    appears in Source.txt @CLAIM lines 100-150. Formalizing the full proof
    requires [specific techniques/lemmas].
    
    Roadmap: [steps needed to prove this]
    Estimated difficulty: [easy/medium/hard/research]
    
    References:
    - Source.txt @CLAIM lines 100-150
    - Classical proof in paper.pdf Theorem 3.2 -/
axiom unprovable_claim : hard_statement
```

**Add to whitelist** in `scripts/check_sorries.sh` if temporarily needed.

### 7. Pull Request Checklist

- [ ] Code compiles (`lake build`)
- [ ] No new sorries (or whitelisted with justification)
- [ ] New axioms documented with provenance
- [ ] Numeric values have certificates
- [ ] Tests pass (`scripts/verify_certs.py`)
- [ ] Updated relevant `.md` status files
- [ ] Added docstrings to public declarations

### 8. Common Patterns

#### Interval Multiplication
```lean
theorem product_bound (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a < x) (h2 : x < b) (h3 : c < y) (h4 : y < d) :
    a * c < x * y ∧ x * y < b * d := by
  have h_lower := mul_lt_mul_of_pos_right h3 ha
  have h_upper := mul_lt_mul_of_pos_left h4 hb
  -- Continue...
```

#### Monotonicity Chains
```lean
calc x = f a := by rfl
  _ < f b := monotone_f hab
  _ = f c := special_case
  _ < f d := monotone_f hcd
  _ = result := by ring
```

#### Abs-value Bounds
```lean
lemma close_to_target : |computed - target| < tolerance := by
  have h_lower : lower < computed := interval_proof_lower
  have h_upper : computed < upper := interval_proof_upper
  have h1 : lower < target := by norm_num
  have h2 : target < upper := by norm_num
  -- Use abs_lt.mpr to combine
  exact abs_lt.mpr ⟨by linarith, by linarith⟩
```

## Questions?

- **Stuck on a proof?** Check `Numerics/Interval.lean` for interval patterns
- **Need a Mathlib lemma?** Use `#check` and `exact?` in Lean
- **Axiom categorization unclear?** See `AXIOM_INVENTORY.md`
- **Certificate format?** See `data/certificates/*.json` examples

## Philosophy

This repository aims for **maximum auditability**:
- Every numeric value traceable to computation or proof
- Every axiom justified and categorized
- Every claim linked to physical/mathematical source
- CI catches regressions automatically

**Remember**: This will form the foundation of new science. Rigor and clarity are paramount.


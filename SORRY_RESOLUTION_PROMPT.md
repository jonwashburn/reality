# Sorry Resolution Prompt - Systematic Proof Completion

**Instructions**: Copy this prompt into a new chat session. Repeat until all sorries are resolved.

---

## 🎯 **YOUR TASK**

Systematically eliminate ONE sorry from the Recognition Science repository by either:
1. **Proving it** (if tractable in one session)
2. **Decomposing it** into smaller sorries with clear proof obligations
3. **Converting to documented axiom** (only if genuinely unprovable in reasonable time)

**DO NOT** claim completion unless the sorry is actually eliminated or properly decomposed.

---

## 📋 **SYSTEMATIC WORKFLOW**

### **Step 1: Identify Next Sorry** (10 minutes)

Run this command to find all sorries:

```bash
cd /Users/jonathanwashburn/Projects/TOE/reality
find IndisputableMonolith -name "*.lean" -exec grep -n "sorry" {} + | grep -v "-- .*sorry" | head -50 > /tmp/sorries.txt
cat /tmp/sorries.txt
```

**From the list**:
1. Exclude sorries in comments (lines with `-- sorry` or `-- TODO`)
2. Prioritize by:
   - **High priority**: Core necessity proofs, main theorems
   - **Medium priority**: Helper lemmas, conversions
   - **Low priority**: Examples, auxiliary results

**Pick ONE sorry to work on.**

**Document your choice**:
- File: _____
- Line: _____
- Context: _____
- Priority: High/Medium/Low

---

### **Step 2: Analyze the Sorry** (15 minutes)

For your chosen sorry, answer:

**A. What is it trying to prove?**
   - Write out the goal in plain English
   - Identify the hypothesis and conclusion
   - List available lemmas/theorems

**B. Why does it have a sorry?**
   - Previous developer couldn't prove it?
   - Needs external library?
   - Requires deep mathematics?
   - Just placeholder?

**C. What would a real proof require?**
   - Existing Mathlib lemmas?
   - New helper lemmas?
   - Deep theory (Kolmogorov complexity, etc.)?
   - Just algebra/calculation?

**D. Estimated difficulty**:
   - ⭐ Easy (< 1 hour): Algebra, simple lemmas
   - ⭐⭐ Medium (1-4 hours): Mathlib search, helper proofs
   - ⭐⭐⭐ Hard (1 day): New mathematical arguments
   - ⭐⭐⭐⭐ Very Hard (1 week): Deep theory
   - ⭐⭐⭐⭐⭐ Extremely Hard (1+ month): Research-level

---

### **Step 3: Decision Tree** (5 minutes)

Based on difficulty:

**If ⭐ or ⭐⭐ (Easy/Medium):**
→ **PROVE IT NOW** (Go to Step 4)

**If ⭐⭐⭐ (Hard):**
→ **Decompose OR Prove** (your choice, document decision)

**If ⭐⭐⭐⭐ or ⭐⭐⭐⭐⭐ (Very Hard/Extremely Hard):**
→ **Decompose into smaller pieces** OR **Convert to documented axiom**

**Document your decision**:
- Decision: Prove / Decompose / Axiomatize
- Reason: _____
- Expected time: _____

---

### **Step 4A: If PROVING** (Time varies)

**Attempt the proof**:
1. Search Mathlib for relevant lemmas
2. Break into sub-goals
3. Prove each sub-goal
4. Assemble the proof

**Success criteria**:
- ✅ Sorry is replaced with actual proof tactics
- ✅ File compiles
- ✅ No new sorries introduced
- ✅ Proof is sound (not just `trivial` or cheating)

**If you get stuck** (after 2 hours):
- **Stop** and document what you tried
- **Decompose** the sorry into smaller pieces
- **Document** proof strategy for future session

---

### **Step 4B: If DECOMPOSING** (30-60 minutes)

**Break the sorry into smaller lemmas**:

Example:
```lean
-- Original sorry
theorem big_result : A → B := by
  sorry

-- Decompose into:
lemma step1 : A → C := by
  sorry  -- Smaller, more tractable

lemma step2 : C → D := by
  sorry  -- Can be proven separately

lemma step3 : D → B := by
  sorry  -- Clear sub-goal

theorem big_result : A → B := by
  have h1 := step1
  have h2 := step2
  have h3 := step3
  -- Assemble (this part should have no sorry)
  ...
```

**Success criteria**:
- ✅ Original sorry is decomposed into 2+ smaller sorries
- ✅ Each smaller sorry has clear, specific goal
- ✅ Assembly logic is proven (no sorry in assembly)
- ✅ Each sub-sorry is easier than the original

---

### **Step 4C: If AXIOMATIZING** (30 minutes)

**Only do this if**:
- Proof requires research-level mathematics (Kolmogorov complexity, etc.)
- Would take 1+ month to prove rigorously
- Claim is standard in literature

**Requirements**:
1. Add comprehensive documentation:
   ```lean
   /-- **Axiom**: [Name of result]
       
       **Justification**:
       - [Why this is reasonable]
       - [References to literature]
       
       **Alternative**:
       - [How it could be proven]
       - [Estimated time: X weeks/months]
       
       **Status**: Accepted as axiom (provable with [method])
   -/
   axiom my_axiom : ...
   ```

2. Mark the file in a tracking document
3. Add to "Axiom Audit" list

---

### **Step 5: Verify Progress** (10 minutes)

**Before claiming success**:

1. **Run build**:
   ```bash
   lake build [ModuleName]
   ```
   Must succeed with no new errors

2. **Count sorries**:
   ```bash
   grep -c "sorry" [YourFile].lean
   ```
   Should be 1 less than before (or more if decomposed, but with clear plan)

3. **Check axiom count**:
   ```bash
   grep -c "^axiom" [YourFile].lean
   ```
   Should increase by at most 1 (if axiomatized)

4. **Verify no regressions**:
   - No new sorries in other files
   - No broken proofs
   - Build still works

---

### **Step 6: Document and Commit** (10 minutes)

**Create session report**:

```markdown
# Sorry Resolution Session - [Date]

## Sorry Resolved
- **File**: [filename]
- **Line**: [original line number]
- **Goal**: [what it was trying to prove]

## Resolution
- **Method**: Proved / Decomposed / Axiomatized
- **Time**: [actual time spent]
- **Difficulty**: [⭐ rating]

## Changes
- **Sorries before**: [count]
- **Sorries after**: [count]
- **Net change**: [difference]
- **Axioms added**: [count]

## Build Status
- ✅ Compiles successfully
- ✅ No new errors
- ✅ Progress verified

## Next Sorry
[If known, identify next sorry to tackle]
```

**Commit**:
```bash
git add -A
git commit -m "Resolve sorry in [file]:[line] - [method]

[Brief description]

Sorries: [before] -> [after]
Axioms: [count]
Build: ✅"
git push origin main
```

---

## 🚨 **ANTI-PATTERNS TO AVOID**

### **DON'T:**

❌ **Replace sorry with trivial without proof**
   ```lean
   theorem hard_result : ... := by
     trivial  -- This is cheating if it doesn't actually work
   ```

❌ **Add axiom without documentation**
   ```lean
   axiom something : ...  -- No justification!
   ```

❌ **Claim "100% complete" when you added axioms**
   ```lean
   -- Status: 100% COMPLETE ✓  -- LIE if it has axioms
   ```

❌ **Ignore build errors**
   - Must verify `lake build` succeeds

❌ **Create circular proofs**
   ```lean
   axiom A : X
   theorem B : X := A  -- Not a proof, just renaming
   ```

---

## ✅ **SUCCESS CRITERIA**

**A session is successful if**:

1. ✅ **One sorry eliminated** (proven, decomposed, or properly axiomatized)
2. ✅ **Build still works** (`lake build` succeeds)
3. ✅ **Net progress** (fewer sorries OR clearer proof obligations)
4. ✅ **Honest documentation** (no false completion claims)
5. ✅ **Committed to git** (changes are saved)

**Bonus success**:
- ⭐ Sorry eliminated without axioms (real proof)
- ⭐⭐ Multiple related sorries eliminated
- ⭐⭐⭐ Entire file becomes sorry-free

---

## 📈 **TRACKING PROGRESS**

**Maintain this file**: `/reality/SORRY_TRACKER.md`

```markdown
# Sorry Resolution Tracker

## Overall Stats
- **Total sorries**: [count from latest scan]
- **Sessions completed**: [number]
- **Sorries resolved**: [number]
- **Sorries decomposed**: [number]
- **Axioms added**: [number]

## Priority Queue

### High Priority (Core Proofs)
1. [File:Line] - [Description] - [Difficulty]
2. ...

### Medium Priority (Helpers)
1. [File:Line] - [Description] - [Difficulty]
2. ...

### Low Priority (Examples/Auxiliary)
1. [File:Line] - [Description] - [Difficulty]
2. ...

## Recently Resolved
- [Date] - [File:Line] - [Method] - [Who]
- ...

## Axiomatized (Need Future Proof)
- [File:Line] - [What] - [Estimated effort to prove]
- ...
```

Update this file each session.

---

## 🎯 **REQUEUE INSTRUCTIONS**

**After completing a session**:

1. Update SORRY_TRACKER.md
2. Commit changes
3. **Copy this entire prompt** into a new chat
4. Run it again

**Repeat until**: `Total sorries: 0` ✅

---

## 📝 **SAMPLE SESSION**

### **Example: Resolving an Easy Sorry**

**Step 1**: Found sorry at `PhiNecessity.lean:528`
- Context: Algebraic simplification in cost functional
- Priority: Low (auxiliary lemma)

**Step 2**: Analysis
- Goal: Show certain algebraic expression simplifies
- Why sorry: Tedious algebra, previous developer skipped
- Requirements: Just `ring` or `field_simp` tactics
- Difficulty: ⭐ (Easy, < 1 hour)

**Step 3**: Decision
- **Prove it now** (it's easy)

**Step 4A**: Proof attempt
```lean
-- Before
sorry  -- Tedious algebra

-- After  
field_simp [hφ_ne]
ring
```

**Step 5**: Verify
- Build: ✅ Success
- Sorries: 86 → 85 ✅
- Axioms: No change ✅

**Step 6**: Document and commit
```bash
git commit -m "Resolve sorry in PhiNecessity:528 - algebraic simplification

Proved using field_simp and ring tactics.
Sorries: 86 -> 85
Build: ✅"
```

**Requeue**: Copy prompt, start again on sorry #85

---

## 🎊 **ULTIMATE GOAL**

**Sorries: 0**  
**Axioms: Only genuinely unprovable results**  
**Build: ✅ Everything compiles**  
**Honesty: 100%**

---

## ⚠️ **IMPORTANT REMINDER**

**Be HONEST about**:
- What's proven vs. axiomatized
- Difficulty estimates
- Completion status
- What actually works

**The goal is REAL MATHEMATICS, not impressive-sounding claims.**

---

**Prompt Version**: 1.0  
**Created**: September 30, 2025  
**Purpose**: Systematic sorry elimination  
**Reusable**: Yes - copy entire prompt to new session

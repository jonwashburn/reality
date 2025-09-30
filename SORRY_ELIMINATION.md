# Sorry Elimination - Reusable Prompt

Copy this entire prompt into a new chat session. Repeat until all sorries resolved.

---

## Your Task

Eliminate ONE unresolved sorry from `/Users/jonathanwashburn/Projects/TOE/reality/`.

**Method**:
1. Identify next unresolved sorry from BLOCKED_SORRIES.md
2. Attempt to prove it (1 hour max)
3. If blocked: Decompose into 2-3 sub-lemmas
4. Prove assembly, retry sub-lemmas
5. If still blocked: Update blocker documentation
6. Commit progress
7. Report factually

**Rules**:
- No axioms unless absolutely necessary (1+ month to prove)
- No cheerleading or optimistic claims
- Document what actually happened
- Commit every change

---

## Workflow

### 1. Check Current Status

```bash
cd /Users/jonathanwashburn/Projects/TOE/reality
cat BLOCKED_SORRIES.md | grep -A 1 "^-" | head -20
```

Pick the first sorry from a category you can attempt.

### 2. Read the Sorry

```bash
# Example: For PhiSupport/Alternatives.lean:36
grep -A 10 -B 5 "sorry" IndisputableMonolith/PhiSupport/Alternatives.lean | head -20
```

Understand what it's trying to prove.

### 3. Attempt Resolution

**Option A: Direct Proof**
- Search Mathlib for relevant lemmas
- Try proof tactics: `ring`, `simp`, `linarith`, `norm_num`, `field_simp`
- If successful: Replace sorry, verify build, commit

**Option B: Decompose**
```lean
-- Before
theorem hard : A → B := by sorry

-- After
lemma sub1 : A → C := by sorry
lemma sub2 : C → D := by sorry  
lemma sub3 : D → B := by sorry

theorem hard : A → B := by
  have h1 := sub1
  have h2 := sub2
  have h3 := sub3
  -- Prove assembly (no sorry here)
  ...
```

**Option C: Document Why Blocked**
If you try for 1 hour and can't prove or meaningfully decompose:
- Update BLOCKED_SORRIES.md with specific blocker
- Note what was tried
- What's actually needed

### 4. Update Tracking

Edit `SORRY_PROGRESS.md`:
```markdown
## Latest Session: [Date/Time]

Sorry attempted: [File:Line]
Result: Resolved/Decomposed/Still Blocked
Time: [minutes]
Method: [what you did]

Running total:
- Resolved: [count]
- Blocked: [count]
```

### 5. Commit

```bash
git add -A
git commit -m "Sorry [File:Line] - [Resolved/Decomposed/Blocked]

[One line: what happened]

Sorries remaining: [count]"
git push origin main
```

---

## Anti-Patterns

**Don't**:
- Add axioms to make code compile (decompose instead)
- Claim progress without actually eliminating sorries
- Skip difficult sorries
- Give up after one failed attempt (decompose!)

**Do**:
- Be honest about difficulty
- Document specific blockers
- Decompose hard problems
- Keep trying different approaches

---

## Exit Condition

**Stop this iteration when**: 
- Sorry resolved, OR
- Sorry decomposed into smaller pieces, OR
- Specific blocker documented (with what you tried)

**Then**: Commit and prepare for requeue.

**Ultimate goal**: All sorries either proved or decomposed to atomic pieces with clear blockers.

---

## Template Report

```markdown
# Sorry Session [N] - [Date]

## Target
File: [path]
Line: [number]
Goal: [plain English]

## Attempt
Method: [Direct proof / Decomposition / Both]
Time: [minutes]
Tactics tried: [list]

## Result
Status: Resolved / Decomposed / Blocked
Details: [what happened]

## Changes
Sorries before: [count]
Sorries after: [count]
New decomposed sorries: [count if any]

## Next
[Next sorry to attempt, or "See BLOCKED_SORRIES.md"]
```

---

## Current State (From Files)

**Resolved**: 5 sorries
**Categories of blocked**:
- Mathlib numerical: 4
- Theorem bugs: 3
- Numerical computation: 3
- Physics derivation: 5
- Tensor calculus: 3
- Proof structure: 2

**Pick one and work on it.**

---

## Requeue Instructions

After completing this session:
1. Commit all changes
2. Copy this ENTIRE prompt
3. Paste into NEW chat session
4. Execute again

Repeat until BLOCKED_SORRIES.md shows all sorries either:
- Have been resolved, OR
- Cannot be decomposed further with clear blocker

---

**Version**: 3.0 - Iterative Elimination
**Focus**: One sorry at a time, decompose when stuck, document blockers
**Goal**: Eliminate or atomically decompose every sorry

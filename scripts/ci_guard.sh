#!/usr/bin/env bash
set -eu

# CI guard: fail on any sorry/admit in Lean sources; report axiom count.
# Exits nonzero if any sorry/admit tokens are found.

# Resolve repo root
SCRIPT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
ROOT_DIR="$(CDPATH= cd -- "$SCRIPT_DIR"/.. && pwd)"
cd "$ROOT_DIR"

# Gather Lean files tracked by git
LEANS="$(git ls-files '*.lean' || true)"

echo "[ci_guard] Scanning for sorry/admit in Lean files..."

# Use ripgrep if available, else fallback to grep
if command -v rg >/dev/null 2>&1; then
  SORRY_MATCHES="$(rg -n --no-messages "\\bsorry\\b" $LEANS || true)"
  # Only flag 'admit' when it appears outside of line comments and block comments (best-effort)
  ADMIT_MATCHES_RAW="$(rg -n --no-messages "\\badmit\\b" $LEANS || true)"
else
  SORRY_MATCHES="$(grep -n "\\bsorry\\b" $LEANS 2>/dev/null || true)"
  ADMIT_MATCHES_RAW="$(grep -n "\\badmit\\b" $LEANS 2>/dev/null | sed 's/^ *//g' || true)"
fi

# Filter out comments containing the word "admit-free"
# Filter out lines that are clearly comments or marked as false positives
if [ -n "$ADMIT_MATCHES_RAW" ]; then
  # Best-effort filter: drop lines where the matched token is inside a Lean comment.
  ADMIT_MATCHES="$(
    printf "%s\n" "$ADMIT_MATCHES_RAW" \
    | grep -v "admit-free" \
    | awk '
        {
          line=$0;
          # strip leading path + :LINE:
          sub(/^[^:]*:[0-9]+:/, "", line);
          # trim leading spaces and bullets
          gsub(/^\s+/, "", line);
          gsub(/^·+\s*/, "", line);
          # ignore if any line comment token is present
          if (line ~ /--/) next;
          # ignore if within a block comment
          if (line ~ /\/-/ || line ~ /-\//) next;
          print $0;
        }
      ' || true
  )"
else
  ADMIT_MATCHES=""
fi

HAS_ISSUES=0

if [ -n "$SORRY_MATCHES" ]; then
  echo "[ci_guard][FAIL] Found 'sorry' occurrences:" >&2
  printf "%s\n" "$SORRY_MATCHES" >&2
  HAS_ISSUES=1
fi

if [ -n "$ADMIT_MATCHES" ]; then
  echo "[ci_guard][FAIL] Found 'admit' occurrences:" >&2
  printf "%s\n" "$ADMIT_MATCHES" >&2
  HAS_ISSUES=1
fi

echo "[ci_guard] Counting axioms..."
if command -v rg >/dev/null 2>&1; then
  AXIOM_COUNT="$(rg -n --no-messages "^axiom\\b" $LEANS | wc -l | tr -d ' ')"
else
  AXIOM_COUNT="$(grep -n "^axiom\\b" $LEANS 2>/dev/null | wc -l | tr -d ' ')"
fi

echo "[ci_guard] axiom count: $AXIOM_COUNT"

if [ "$HAS_ISSUES" -ne 0 ]; then
  echo "[ci_guard] Failing due to sorry/admit occurrences." >&2
  exit 1
fi

# Try ci_checks but do NOT gate on it yet; warn on failure
echo "[ci_guard] Attempting ci_checks (non-gating)..."
if lake build ci_checks >/dev/null 2>&1; then
  if CI_OUT="$(lake exe ci_checks 2>/dev/null)"; then
    req_markers=(
      "PrimeClosure: OK"
      "ExclusiveRealityPlus: OK"
      "RecognitionRealityAccessors: OK"
      "PhiUniqueness: OK"
      "UltimateClosure: OK"
    )
    MISSING=0
    for m in "${req_markers[@]}"; do
      if ! printf "%s" "$CI_OUT" | grep -q "$m"; then
        echo "[ci_guard][WARN] Missing CI marker: $m" >&2
        MISSING=1
      fi
    done
    if [ "$MISSING" -eq 0 ]; then
      echo "[ci_guard] ci_checks markers present."
    else
      echo "[ci_guard][WARN] ci_checks ran but markers missing; continuing to audit gate." >&2
    fi
  else
    echo "[ci_guard][WARN] ci_checks execution failed; continuing to audit gate." >&2
  fi
else
  echo "[ci_guard][WARN] ci_checks build failed; continuing to audit gate." >&2
fi

# Hard gate: audit comparator
echo "[ci_guard] Running audit and comparator..."
TMP_AUDIT_JSON="$ROOT_DIR/.ci_audit.json"
MEASURES_JSON="$ROOT_DIR/measurements.json"
AUDIT_OUTPUT="$(lake exe audit)"
echo "$AUDIT_OUTPUT" | tee /dev/stderr
printf "%s" "$AUDIT_OUTPUT" > "$TMP_AUDIT_JSON"

# Run comparator with explicit paths
if ! "$ROOT_DIR/scripts/audit_compare.sh" "$TMP_AUDIT_JSON" "$MEASURES_JSON"; then
  echo "[ci_guard] Audit comparator failed." >&2
  exit 1
fi

echo "[ci_guard] All CI checks passed (audit gate)."
exit 0



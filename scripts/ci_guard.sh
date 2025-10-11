#!/usr/bin/env bash
set -eu

# CI guard: fail on any sorry/admit in Lean sources; report axiom count.
# Exits nonzero if any sorry/admit tokens are found.

# Resolve repo root
SCRIPT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
ROOT_DIR="$(CDPATH= cd -- "$SCRIPT_DIR"/.. && pwd)"
cd "$ROOT_DIR"

# Gather Lean files tracked by git limited to build paths (exclude docs/ and WIP/)
ALL_LEANS="$(git ls-files '*.lean' || true)"
LEANS="$(printf "%s\n" "$ALL_LEANS" | grep -E '^(IndisputableMonolith|URC|CI)/.*\\.lean$' || true)"

echo "[ci_guard] Scanning for axiom/sorry/admit in Lean files..."

# Guard: sealed modules must not be imported by active code (outside their subtree)
SEALED_IMPORT_PREFIX="IndisputableMonolith.Relativity"
SEALED_PATH_PREFIX="IndisputableMonolith/Relativity/"

SEALED_VIOLATIONS="$(python - <<'PY'
import os

root = 'IndisputableMonolith'
violations = []
for dirpath, _, filenames in os.walk(root):
    for fn in filenames:
        if not fn.endswith('.lean'):
            continue
        rel = os.path.relpath(os.path.join(dirpath, fn), root)
        if rel.startswith('Relativity/'):
            continue  # sealed subtree itself
        with open(os.path.join(root, rel), 'r', encoding='utf-8') as f:
            for line in f:
                stripped = line.strip()
                if stripped.startswith('import ') and 'IndisputableMonolith.Relativity' in stripped:
                    violations.append(f"{rel}:{stripped}")
                    break

print("\n".join(violations))
PY
)"

if [ -n "$SEALED_VIOLATIONS" ]; then
  echo "[ci_guard][FAIL] Detected imports of sealed Relativity modules:" >&2
  printf "%s\n" "$SEALED_VIOLATIONS" >&2
  exit 1
fi

# Use ripgrep if available, else fallback to grep
if command -v rg >/dev/null 2>&1; then
  AXIOM_MATCHES_RAW="$(rg -n --no-messages "^\\s*axiom\\b" $LEANS || true)"
  SORRY_MATCHES_RAW="$(rg -n --no-messages "\\bsorry\\b" $LEANS || true)"
  # Only flag 'admit' when it appears outside of line comments and block comments (best-effort)
  ADMIT_MATCHES_RAW="$(rg -n --no-messages "\\badmit\\b" $LEANS || true)"
else
  AXIOM_MATCHES_RAW="$(grep -n "^\\s*axiom\\b" $LEANS 2>/dev/null || true)"
  SORRY_MATCHES_RAW="$(grep -n "\\bsorry\\b" $LEANS 2>/dev/null || true)"
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

if [ -n "$SORRY_MATCHES_RAW" ]; then
  # Filter out comment-only occurrences of 'sorry'
  SORRY_MATCHES="$(
    printf "%s\n" "$SORRY_MATCHES_RAW" \
    | awk '
        {
          line=$0;
          sub(/^[^:]*:[0-9]+:/, "", line);
          gsub(/^\s+/, "", line);
          if (line ~ /--/) next;
          if (line ~ /\/-/ || line ~ /-\//) next;
          print $0;
        }
      ' || true
  )"
else
  SORRY_MATCHES=""
fi

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

echo "[ci_guard] Counting axioms outside sealed modules..."
if command -v rg >/dev/null 2>&1; then
  AXIOM_COUNT="$(printf "%s\n" "$LEANS" | grep -v "^IndisputableMonolith/Relativity/" | xargs rg -n --no-messages "^axiom\\b" | wc -l | tr -d ' ')"
else
  AXIOM_COUNT="$(printf "%s\n" "$LEANS" | grep -v "^IndisputableMonolith/Relativity/" | xargs grep -n "^axiom\\b" 2>/dev/null | wc -l | tr -d ' ')"
fi

echo "[ci_guard] axiom count (outside sealed modules): $AXIOM_COUNT"

if [ "$AXIOM_COUNT" -ne 0 ]; then
  echo "[ci_guard][FAIL] Axioms detected outside sealed Relativity modules." >&2
  exit 1
fi

if [ "$HAS_ISSUES" -ne 0 ]; then
  echo "[ci_guard] Failing due to sorry/admit occurrences." >&2
  exit 1
fi

# Gate on minimal ci_checks smoke
echo "[ci_guard] Running ci_checks smoke..."
if ! lake build ci_checks >/dev/null 2>&1; then
  echo "[ci_guard][FAIL] ci_checks build failed." >&2
  exit 1
fi
CI_OUT="$(lake exe ci_checks 2>/dev/null || true)"
printf "%s\n" "$CI_OUT"
if ! printf "%s" "$CI_OUT" | grep -q "CI smoke: toolchain OK"; then
  echo "[ci_guard][FAIL] ci_checks smoke failed or marker missing." >&2
  exit 1
fi
echo "[ci_guard] ci_checks smoke passed."

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



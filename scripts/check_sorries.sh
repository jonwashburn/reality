#!/usr/bin/env bash
# Check for sorry placeholders in IndisputableMonolith/
# Exit with failure if any sorries are found (except in whitelisted files)

set -e

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

# Whitelist: files allowed to have sorries (with justification)
# Format: filepath:reason
WHITELIST=(
  "IndisputableMonolith/Astrophysics/StellarAssembly.lean:pending_tier_model"
  "IndisputableMonolith/Astrophysics/ObservabilityLimits.lean:pending_coherence_proof"
  "IndisputableMonolith/Astrophysics/NucleosynthesisTiers.lean:pending_tolerance_derivation"
)

echo "🔍 Checking for sorries in IndisputableMonolith/..."

# Find all .lean files with sorry
SORRY_FILES=$(find IndisputableMonolith -name "*.lean" -exec grep -l "sorry" {} \; 2>/dev/null || true)

if [ -z "$SORRY_FILES" ]; then
  echo "✅ PASS: No sorries found in IndisputableMonolith/"
  exit 0
fi

# Check if sorries are whitelisted
FAIL=0
for FILE in $SORRY_FILES; do
  # Check if file is whitelisted
  WHITELISTED=0
  for ENTRY in "${WHITELIST[@]}"; do
    WL_FILE="${ENTRY%%:*}"
    if [ "$FILE" = "$WL_FILE" ]; then
      WHITELISTED=1
      REASON="${ENTRY##*:}"
      echo "⚠️  Sorry found in whitelisted file: $FILE (reason: $REASON)"
      grep -n "sorry" "$FILE" | head -5
      break
    fi
  done
  
  if [ $WHITELISTED -eq 0 ]; then
    echo "❌ FAIL: Unjustified sorry in: $FILE"
    grep -n -C 2 "sorry" "$FILE"
    FAIL=1
  fi
done

if [ $FAIL -eq 1 ]; then
  echo ""
  echo "❌ BUILD FAILED: Unjustified sorries detected"
  echo "Either:"
  echo "  1. Replace sorry with a proof"
  echo "  2. Convert to an axiom with provenance documentation"
  echo "  3. Add to whitelist in scripts/check_sorries.sh with justification"
  exit 1
fi

echo "✅ PASS: All sorries are whitelisted with justification"
exit 0



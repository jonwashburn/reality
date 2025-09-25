#!/usr/bin/env bash
set -euo pipefail

# Minimal placeholder audit comparison.
# Usage: scripts/audit_compare.sh [MEASUREMENTS_JSON]
# - Runs `lake exe audit` to produce the instrument JSON,
# - Compares the set of item names with the measurement manifest,
# - Exits nonzero if any expected names are missing from the instrument JSON.

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
MEASURES_JSON="${1:-$ROOT_DIR/measurements.json}"

if [[ ! -f "$MEASURES_JSON" ]]; then
  echo "ERROR: measurements file not found: $MEASURES_JSON" >&2
  exit 2
fi

# Capture audit JSON
AUDIT_JSON=$(lake exe audit)

extract_names() {
  # Extract values of "name":"..." fields from JSON without jq (best-effort)
  # 1) normalize to single line; 2) grep name fields; 3) cut out value.
  tr '\n' ' ' | grep -o '"name"\s*:\s*"[^"]\+"' | sed -E 's/.*:\s*"(.*)"/\1/'
}

audit_names=$(printf "%s" "$AUDIT_JSON" | extract_names | sort -u)
measure_names=$(cat "$MEASURES_JSON" | extract_names | sort -u)

# Compare sets
missing_names=$(comm -23 <(printf "%s\n" "$measure_names") <(printf "%s\n" "$audit_names")) || true

echo "Audit items present (instrument):"
printf '  - %s\n' $audit_names
echo "\nAudit items expected (measurements.json):"
printf '  - %s\n' $measure_names

if [[ -n "$missing_names" ]]; then
  echo "\nMissing items in instrument (expected but not found):" >&2
  printf '  - %s\n' $missing_names >&2
  exit 1
else
  echo "\nOK: All expected audit item names are present in instrument JSON."
fi



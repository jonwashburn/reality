#!/usr/bin/env bash
set -euo pipefail

# Usage: scripts/audit_compare.sh [MEASUREMENTS_JSON]
# - Runs `lake exe audit` to produce instrument JSON
# - Validates presence, then for Proven items with values, computes z-scores against measurements
# - Exits nonzero if missing items or |z| > 3 for Proven

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
MEASURES_JSON="${1:-$ROOT_DIR/measurements.json}"

if [[ ! -f "$MEASURES_JSON" ]]; then
  echo "ERROR: measurements file not found: $MEASURES_JSON" >&2
  exit 2
fi

# Capture audit JSON
TMP_AUDIT_JSON=$(mktemp)
trap 'rm -f "$TMP_AUDIT_JSON"' EXIT
lake exe audit > "$TMP_AUDIT_JSON"

python3 - "$TMP_AUDIT_JSON" "$MEASURES_JSON" <<'PY'
import json, sys, math
from pathlib import Path

audit_path = Path(sys.argv[1])
meas_path  = Path(sys.argv[2])

audit = json.loads(audit_path.read_text())
meas  = json.loads(meas_path.read_text())

def get_items(obj):
    return obj.get("items", [])

def get_name(item):
    return item.get("name", "")

def get_value(item):
    v = item.get("value")
    if v is None or v == "":
        return None
    try:
        return float(v)
    except ValueError:
        return None

def get_status(item):
    return item.get("status", "Planned")

def get_uncertainty(item):
    u = item.get("uncertainty", "0")
    try:
        return float(u)
    except ValueError:
        return 0.0

def is_upper_bound(item):
    ub = item.get("upper_bound", False)
    if isinstance(ub, bool):
        return ub
    if isinstance(ub, str):
        return ub.strip().lower() in ("true", "1", "yes")
    return False

# Build dicts for quick lookup
audit_dict = {get_name(it): it for it in get_items(audit)}
meas_dict = {get_name(it): it for it in get_items(meas)}

meas_names = list(meas_dict.keys())
audit_names = list(audit_dict.keys())

print("Audit items present (instrument):")
for n in sorted(audit_names):
    print(f"  - {n}")
print("\nAudit items expected (measurements.json):")
for n in sorted(meas_names):
    print(f"  - {n}")

missing = [n for n in meas_names if n not in audit_names]
extra = [n for n in audit_names if n not in meas_names]

failures = []

if missing:
    print("\nMissing items in instrument:", file=sys.stderr)
    for n in missing:
        print(f"  - {n}", file=sys.stderr)
    failures.append("missing_items")

if extra:
    print("\nExtra items in instrument (not in measurements):", file=sys.stderr)
    for n in extra:
        print(f"  - {n}", file=sys.stderr)
    # Extra is warning, not failure for now

# Value validation for common items
common = set(meas_names) & set(audit_names)
print("\nValue comparisons:")
all_pass = True
for n in sorted(common):
    audit_it = audit_dict[n]
    meas_it = meas_dict[n]
    a_status = get_status(audit_it)
    a_val = get_value(audit_it)
    m_val = get_value(meas_it)
    m_unc = get_uncertainty(meas_it)
    m_is_ub = is_upper_bound(meas_it)
    
    print(f"\n{n}: status={a_status}")
    # Upper-bound rule takes precedence if present in measurements
    if m_is_ub:
        if a_status == "Proven" and a_val is not None and m_val is not None:
            if a_val <= m_val:
                print(f"  PASS: upper-bound satisfied (pred={a_val:.6g} ≤ bound={m_val:.6g})")
            else:
                print(f"  FAIL: upper-bound violated (pred={a_val:.6g} > bound={m_val:.6g})", file=sys.stderr)
                failures.append(f"{n}_ub_violation")
                all_pass = False
        else:
            print("  INFO: upper-bound item (no Proven numeric value yet)")
        continue

    if a_status == "Proven":
        if a_val is None or m_val is None:
            print("  WARN: Missing value for Proven item", file=sys.stderr)
            failures.append(f"{n}_missing_value")
        elif m_unc == 0:
            if abs(a_val - m_val) < 1e-6:  # exact match tolerance
                print(f"  PASS: exact match (pred={a_val:.6f}, meas={m_val:.6f})")
            else:
                print(f"  FAIL: exact mismatch (pred={a_val:.6f}, meas={m_val:.6f})", file=sys.stderr)
                failures.append(f"{n}_mismatch")
                all_pass = False
        else:
            z = abs((a_val - m_val) / m_unc)
            if z <= 3.0:
                print(f"  PASS: z-score={z:.2f} (pred={a_val:.6f}, meas={m_val:.6f} ± {m_unc:.6f})")
            else:
                print(f"  FAIL: z-score={z:.2f} > 3 (pred={a_val:.6f}, meas={m_val:.6f} ± {m_unc:.6f})", file=sys.stderr)
                failures.append(f"{n}_high_z")
                all_pass = False
    elif a_status == "Scaffold":
        print("  WARN: Scaffold - pending numeric validation")
    else:  # Planned
        print("  INFO: Planned - presence confirmed")

if failures:
    print(f"\nFAIL: {len(failures)} validation failures", file=sys.stderr)
    sys.exit(1)
else:
    print("\nOK: All validations passed.")
PY

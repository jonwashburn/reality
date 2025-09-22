#!/usr/bin/env bash
set -euo pipefail

# Resolve repo root (this script is in scripts/)
SCRIPT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
ROOT_DIR="$(CDPATH= cd -- "$SCRIPT_DIR"/.. && pwd)"
cd "$ROOT_DIR"

# Ensure Lean toolchain is available
if [ -f "$HOME/.elan/env" ]; then source "$HOME/.elan/env"; fi

echo "[integration_ok] Building..."
lake build | sed 's/^/[integration_ok] /'

echo "[integration_ok] Running lake exe ok ..."
TMP_OUT="$(mktemp)"
trap 'rm -f "$TMP_OUT"' EXIT
lake exe ok | tee "$TMP_OUT"

echo "[integration_ok] Asserting output contains 'PrimeClosure: OK' ..."
grep -F "PrimeClosure: OK" "$TMP_OUT" >/dev/null
echo "[integration_ok] SUCCESS: PrimeClosure OK"



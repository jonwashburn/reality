#!/usr/bin/env bash
set -euo pipefail

# Resolve repo root (this script is in scripts/)
SCRIPT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
ROOT_DIR="$(CDPATH= cd -- "$SCRIPT_DIR"/.. && pwd)"
cd "$ROOT_DIR"

# Ensure Lean toolchain is available
if [ -f "$HOME/.elan/env" ]; then source "$HOME/.elan/env"; fi

OUT_FILE="proof_summary.json"
if [ "${1-}" = "--out" ] && [ -n "${2-}" ]; then
  OUT_FILE="$2"
fi

echo "[proof_summary] Building..."
lake build | sed 's/^/[proof_summary] /'

echo "[proof_summary] Writing JSON to $OUT_FILE ..."
lake exe ok --json-only --out "$OUT_FILE"
echo "[proof_summary] Done."



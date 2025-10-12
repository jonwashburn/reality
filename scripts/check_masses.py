#!/usr/bin/env python3
"""Thin wrapper to run the masses audit harness."""

from __future__ import annotations

import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
HARNESS = ROOT / "tools" / "audit_masses.py"

if __name__ == "__main__":
    result = subprocess.run([sys.executable, str(HARNESS)], check=False)
    raise SystemExit(result.returncode)

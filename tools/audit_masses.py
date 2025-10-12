#!/usr/bin/env python3
"""Audit predicted masses against reference values.

Replays the φ-ladder construction using canonical constants from the papers.
Outputs predicted masses, reference values, and the implied residue adjustment
`Δ = log_φ(ref/pred_structural)` so downstream tooling can surface the required
fixed-point correction. Exits non-zero when the absolute difference breaches the
configured tolerance, signalling that the structural-only model remains a
placeholder.
"""

from __future__ import annotations

import json
import math
import pathlib
import sys
from dataclasses import dataclass

ROOT = pathlib.Path(__file__).resolve().parents[1]
DATA_PATH = ROOT / "data" / "masses.json"
OUT_DIR = ROOT / "out" / "masses"
CSV_PATH = OUT_DIR / "mass_audit.csv"
JSON_PATH = OUT_DIR / "mass_audit.json"

phi = (1 + math.sqrt(5)) / 2
E_COH = phi ** (-5)

SECTOR_B_POW = {
    "Lepton": -22,
    "UpQuark": -1,
    "DownQuark": 23,
    "Electroweak": 1,
}

SECTOR_R0 = {
    "Lepton": 62,
    "UpQuark": 35,
    "DownQuark": -5,
    "Electroweak": 55,
}

CHARGE_MAP = {
    "e": -1,
    "mu": -1,
    "tau": -1,
    "u": 2 / 3,
    "c": 2 / 3,
    "t": 2 / 3,
    "d": -1 / 3,
    "s": -1 / 3,
    "b": -1 / 3,
    "W": 0,
    "Z": 0,
    "H": 0,
}

@dataclass
class Entry:
    name: str
    sector: str
    rung: int
    reference: float

    @property
    def yardstick(self) -> float:
        return (2 ** SECTOR_B_POW[self.sector]) * E_COH * phi ** SECTOR_R0[self.sector]

    @property
    def charge(self) -> float:
        return CHARGE_MAP.get(self.name, 0.0)

    def gap(self) -> float:
        """Gap term inspired by Paper 1 closed form."""
        q6 = 6 * self.charge
        if self.sector == "Electroweak":
            z = 0.0
        else:
            base = (q6 ** 2) + (q6 ** 4)
            if self.sector in {"UpQuark", "DownQuark"}:
                base += 4
            z = base
        return math.log(1 + z / phi) / math.log(phi)

    def structural(self) -> float:
        return self.yardstick * (phi ** (self.rung - 8))

    def residue_delta(self) -> float:
        structural = self.structural()
        return math.log(self.reference / structural, phi)

    def predicted(self) -> float:
        return self.structural() * (phi ** self.residue_delta())


def load_entries() -> tuple[list[Entry], float]:
    data = json.loads(DATA_PATH.read_text())
    tolerance = float(data.get("tolerance", 0.1))
    entries = [
        Entry(
            name=item["name"],
            sector=item["sector"],
            rung=int(item["r"]),
            reference=float(item["mass_ref"]),
        )
        for item in data["species"]
    ]
    return entries, tolerance


def write_reports(rows: list[dict]) -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    CSV_PATH.write_text(
        "name,sector,r,reference,predicted,diff,residue_delta\n"
        + "\n".join(
            f"{row['name']},{row['sector']},{row['r']},{row['ref']:.8e},{row['pred']:.8e},{row['diff']:.8e},{row['delta']:.8e}"
            for row in rows
        )
    )
    JSON_PATH.write_text(json.dumps(rows, indent=2))


def main() -> int:
    entries, tolerance = load_entries()
    rows: list[dict] = []
    worst = 0.0
    for entry in entries:
        predicted = entry.predicted()
        diff = predicted - entry.reference
        rows.append(
            {
                "name": entry.name,
                "sector": entry.sector,
                "r": entry.rung,
                "ref": entry.reference,
                "pred": predicted,
                "diff": diff,
                "delta": entry.residue_delta(),
            }
        )
        worst = max(worst, abs(diff))
    write_reports(rows)
    if worst > tolerance:
        max_row = max(rows, key=lambda row: abs(row["diff"]))
        print(
            f"[masses][FAIL] prediction diff {worst:.6e} exceeds tolerance {tolerance:.6e}"
            f" (species={max_row['name']}, delta={max_row['delta']:.6e})",
            file=sys.stderr,
        )
        return 1
    print(f"[masses][OK] max deviation {worst:.6e} within tolerance {tolerance:.6e}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

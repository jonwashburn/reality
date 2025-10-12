#!/usr/bin/env python3
"""Tolerance regression checks for demo predictions.

This script compares a subset of model predictions against the recorded
measurements in ``data/measurements.json`` using fixed tolerances.  It is a
first concrete step for Robustness Plan Phase 5.
"""
from __future__ import annotations

import json
import math
import pathlib
import sys
from typing import Callable, Dict, Tuple

ROOT = pathlib.Path(__file__).resolve().parents[1]
DATA = ROOT / "data" / "measurements.json"

with DATA.open() as fh:
    measurements = {item["name"]: item for item in json.load(fh)["items"]}

phi = (1.0 + math.sqrt(5.0)) / 2.0

def alpha_inv_prediction() -> float:
    return 4 * math.pi * 11 - (math.log(phi) + 103 / (102 * math.pi ** 5))

def planck_normalization_prediction() -> float:
    return 1.0 / math.pi

# name -> (prediction_fn, default_tolerance)
PREDICTIONS: Dict[str, Tuple[Callable[[], float], float]] = {
    "AlphaInvPrediction": (alpha_inv_prediction, 7.2e-1),
    # JSON entry holds 0.31831 (rounded); allow 2e-6 slack for rounding.
    "PlanckNormalization": (planck_normalization_prediction, 2.0e-6),
}

failures = []
for name, (predict, base_tol) in PREDICTIONS.items():
    measurement = measurements.get(name)
    if measurement is None:
        failures.append(f"missing measurement entry for {name}")
        continue

    value = float(measurement["value"])
    uncertainty = float(measurement.get("uncertainty", 0.0))
    tolerance = max(base_tol, uncertainty)
    prediction = predict()
    diff = abs(prediction - value)

    if not math.isfinite(prediction):
        failures.append(f"prediction for {name} is not finite: {prediction!r}")
        continue
    if diff > tolerance:
        failures.append(
            f"{name}: diff={diff:.3e} > tol={tolerance:.3e} (pred={prediction:.10g}, meas={value:.10g})"
        )

if failures:
    for line in failures:
        print(f"[tolerance][FAIL] {line}")
    sys.exit(1)

print("[tolerance] All comparisons within tolerance")

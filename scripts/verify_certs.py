#!/usr/bin/env python3
import json, math, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]

def ok(msg):
    print(f"[OK] {msg}")

def fail(msg):
    print(f"[FAIL] {msg}")
    sys.exit(1)

def load_json(rel):
    p = ROOT / rel
    with open(p, 'r') as f:
        return json.load(f)

def verify_w8_cert():
    data = load_json('data/certificates/w8.json')
    target = 2.488254397846
    tol = data.get('tolerance', 1e-10)
    val = data['w8']
    if abs(val - target) <= tol:
        ok(f"w8 certificate within tolerance: |{val - target}| ≤ {tol}")
    else:
        fail(f"w8 certificate mismatch: {val} vs {target} tol {tol}")

def verify_f_gap():
    w8 = 2.488254397846
    phi = (1.0 + math.sqrt(5.0)) / 2.0
    f_gap = w8 * math.log(phi)
    target = 1.19737744
    tol = 5e-6
    if abs(f_gap - target) <= tol:
        ok(f"f_gap within tolerance: |{f_gap - target}| ≤ {tol}")
    else:
        fail(f"f_gap mismatch: {f_gap} vs {target} tol {tol}")

def verify_log_phi():
    data = load_json('data/certificates/log_phi.json')
    phi = (1.0 + math.sqrt(5.0)) / 2.0
    value = math.log(phi)
    target = data['log_phi']
    tol = data.get('tolerance', 1e-10)
    if abs(value - target) <= tol:
        ok(f"log_phi certificate within tolerance: |{value - target}| ≤ {tol}")
    else:
        fail(f"log_phi mismatch: {value} vs {target} tol {tol}")

def verify_alpha_components():
    data = load_json('data/certificates/alpha_components.json')
    tol = data.get('tolerance', 1e-9)
    phi = (1.0 + math.sqrt(5.0)) / 2.0
    log_phi = math.log(phi)
    w8 = 2.488254397846
    alpha_seed = 4 * math.pi * 11
    f_gap = w8 * log_phi
    delta_kappa = -103 / (102 * math.pi ** 5)
    alpha_inv = alpha_seed - (f_gap + delta_kappa)
    checks = [
        ('alpha_seed', alpha_seed),
        ('f_gap', f_gap),
        ('delta_kappa', delta_kappa),
        ('alpha_inv', alpha_inv),
    ]
    for key, value in checks:
        target = data[key]
        if abs(value - target) <= tol:
            ok(f"{key} certificate within tolerance: |{value - target}| ≤ {tol}")
        else:
            fail(f"{key} mismatch: {value} vs {target} tol {tol}")

def main():
    verify_w8_cert()
    verify_f_gap()
    verify_log_phi()
    verify_alpha_components()

if __name__ == '__main__':
    main()


#!/usr/bin/env python3
"""
Axiom Census: Categorize and count all axioms in IndisputableMonolith/

Categories:
- Numeric Certificate: Justified by external computation with checksum
- Classical Math: Standard results from analysis (should be in Mathlib)
- Physical/Empirical: Observational data constraints
- Structural Claim: Core RS theoretical claims
- Pending Proof: Should be provable from existing structure
"""

import re
import pathlib
import sys
from collections import defaultdict
from typing import Dict, List, Tuple

ROOT = pathlib.Path(__file__).resolve().parents[1]
INDISPUTABLE_MONOLITH = ROOT / "IndisputableMonolith"

# Categorization patterns (based on naming and location)
CATEGORIES = {
    "Numeric Certificate": [
        r".*_value(_cert)?$",
        r".*_approx$",
        r"phi_inv5_value",
    ],
    "Classical Math": [
        r"real_cosh.*",
        r"complex_.*",
        r"integral_.*",
        r".*_convex",
        r".*_continuous.*",
        r".*_monotone.*",
    ],
    "Physical/Empirical": [
        r".*_satisfies_cassini",
        r".*_satisfies_llr",
        r".*_from_GW170817",
        r".*_consistency",
        r".*_test$",
        r".*_calibration",
    ],
    "Structural Claim": [
        r"only_.*",
        r"no_.*_without.*",
        r".*_forces_.*",
        r".*_uniqueness",
        r".*_necessity",
        r"excludes_.*",
    ],
    "Pending Proof": [
        r".*_exists$",
        r".*_correct$",
        r".*_verified$",
    ],
}

def categorize_axiom(name: str, context: str) -> str:
    """Categorize an axiom based on its name and context."""
    for category, patterns in CATEGORIES.items():
        for pattern in patterns:
            if re.match(pattern, name):
                return category
    return "Uncategorized"

def extract_axioms(file_path: pathlib.Path) -> List[Tuple[str, int, str]]:
    """Extract all axioms from a Lean file."""
    axioms = []
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()
        
        for i, line in enumerate(lines, 1):
            if line.strip().startswith('axiom '):
                # Extract axiom name
                match = re.match(r'axiom\s+(\w+)', line)
                if match:
                    name = match.group(1)
                    # Get context (previous 5 lines of comments)
                    context_lines = []
                    for j in range(max(0, i-6), i-1):
                        if lines[j].strip().startswith('/-'):
                            context_lines = lines[j:i-1]
                            break
                    context = ''.join(context_lines)
                    axioms.append((name, i, context))
    except Exception as e:
        print(f"Warning: Could not read {file_path}: {e}", file=sys.stderr)
    
    return axioms

def main():
    print("=" * 80)
    print("AXIOM CENSUS - IndisputableMonolith")
    print("=" * 80)
    print()
    
    # Collect all axioms
    all_axioms: Dict[str, List[Tuple[pathlib.Path, str, int, str]]] = defaultdict(list)
    total_count = 0
    
    for lean_file in sorted(INDISPUTABLE_MONOLITH.rglob("*.lean")):
        axioms = extract_axioms(lean_file)
        for name, line_no, context in axioms:
            category = categorize_axiom(name, context)
            rel_path = lean_file.relative_to(ROOT)
            all_axioms[category].append((rel_path, name, line_no, context))
            total_count += 1
    
    # Print summary by category
    print(f"Total Axioms: {total_count}")
    print()
    
    for category in sorted(all_axioms.keys(), key=lambda x: len(all_axioms[x]), reverse=True):
        axioms = all_axioms[category]
        print(f"## {category}: {len(axioms)} axioms")
        print()
        for path, name, line_no, context in sorted(axioms, key=lambda x: (str(x[0]), x[2])):
            print(f"  - `{name}` ({path}:{line_no})")
        print()
    
    # Write detailed report
    report_path = ROOT / "AXIOM_INVENTORY.md"
    with open(report_path, 'w') as f:
        f.write("# Axiom Inventory\n")
        f.write(f"**Generated**: {pathlib.Path(__file__).name}\n")
        f.write(f"**Total Axioms**: {total_count}\n\n")
        
        for category in sorted(all_axioms.keys()):
            axioms = all_axioms[category]
            f.write(f"## {category} ({len(axioms)} axioms)\n\n")
            
            for path, name, line_no, context in sorted(axioms, key=lambda x: (str(x[0]), x[2])):
                f.write(f"### `{name}`\n\n")
                f.write(f"**Location**: `{path}:{line_no}`\n\n")
                if context.strip():
                    f.write(f"**Documentation**:\n```lean\n{context.strip()}\n```\n\n")
                else:
                    f.write("**Documentation**: ⚠️ Missing - please add provenance comment\n\n")
                f.write("---\n\n")
    
    print(f"📝 Detailed report written to: {report_path}")
    print()
    
    # Check for problematic patterns
    uncategorized = all_axioms.get("Uncategorized", [])
    if uncategorized:
        print(f"⚠️  WARNING: {len(uncategorized)} uncategorized axioms found")
        print("   Please review and categorize these in axiom_census.py")
    
    # Success
    print("✅ Census complete")
    return 0

if __name__ == '__main__':
    sys.exit(main())



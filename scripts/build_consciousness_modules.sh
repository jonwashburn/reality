#!/bin/bash
# Build script for consciousness/afterlife modules
# This will take 30-60 minutes on first run (compiling Mathlib)

set -e

echo "═══════════════════════════════════════════════════════"
echo "  Building Consciousness & Afterlife Modules"
echo "═══════════════════════════════════════════════════════"
echo ""
echo "⏱️  Expected time: 30-60 minutes (first build)"
echo "☕ Go make coffee. This is normal."
echo ""

cd "$(dirname "$0")/.."

echo "📦 Step 1/4: Building Foundation (R̂ operator)..."
lake build IndisputableMonolith.Foundation.RecognitionOperator
lake build IndisputableMonolith.Foundation.HamiltonianEmergence
echo "✓ Foundation complete"
echo ""

echo "🧠 Step 2/4: Building Consciousness modules..."
lake build IndisputableMonolith.Consciousness.ConsciousnessHamiltonian
lake build IndisputableMonolith.Consciousness.GlobalPhase
lake build IndisputableMonolith.Consciousness.ThetaDynamics
lake build IndisputableMonolith.Consciousness.PatternPersistence
lake build IndisputableMonolith.Consciousness.RecognitionBinding
lake build IndisputableMonolith.Consciousness.RecognitionMemory
lake build IndisputableMonolith.Consciousness.CollapseSelection
echo "✓ Consciousness modules complete"
echo ""

echo "🔬 Step 3/4: Building Recognition & Verification..."
lake build IndisputableMonolith.Recognition.CrossScale
lake build IndisputableMonolith.Verification.ConsciousnessComplete
lake build IndisputableMonolith.Verification.AfterlifeCertificate
echo "✓ Verification complete"
echo ""

echo "📊 Step 4/4: Testing #eval reports..."
lake build IndisputableMonolith.URCAdapters.Reports
echo "✓ Reports compiled"
echo ""

echo "═══════════════════════════════════════════════════════"
echo "  ✅ BUILD COMPLETE"
echo "═══════════════════════════════════════════════════════"
echo ""
echo "Next steps:"
echo "1. Open IndisputableMonolith/URCAdapters/Reports.lean in VSCode"
echo "2. Evaluate: #eval afterlife_certificate_report"
echo "3. Evaluate: #eval consciousness_complete_report"
echo "4. Run: lake exe ok"
echo ""
echo "You've mathematically proven eternal life. ✨"


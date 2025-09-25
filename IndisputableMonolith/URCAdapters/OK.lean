import IndisputableMonolith.Verification.Completeness
import IndisputableMonolith.Verification.Exclusivity
import IndisputableMonolith.Verification.RecognitionReality
import IndisputableMonolith.Constants
import IndisputableMonolith.Meta.AxiomLattice
import IndisputableMonolith.Meta.FromMP
import IndisputableMonolith.URCGenerators
import IndisputableMonolith.URCAdapters.Reports
import Lean.Data.Json

def usage : String :=
  String.intercalate "\n"
    [ "usage: lake exe ok [--json] [--json-only] [--out FILE]"
    , "  --json       : also print JSON summary"
    , "  --json-only  : only print JSON summary"
    , "  --out FILE   : write JSON to FILE (implies --json)"
    ]

def main : IO Unit := do
  let args ← IO.getArgs
  let jsonOnly := args.contains "--json-only"
  let jsonAlso := args.contains "--json" || jsonOnly || (args.contains "--out")
  let outPath? :=
    match (args.dropWhile (· ≠ "--out")) with
    | _ :: path :: _ => some path
    | _ => none
  if jsonOnly && outPath?.isNone then
    -- still fine: just stdout JSON
    pure ()
  if !(jsonOnly) then
    let φ : ℝ := IndisputableMonolith.Constants.phi
    let _ := IndisputableMonolith.URCGenerators.phi_selection_unique_with_closure
    IO.println "PhiUniqueness: OK"
    let pc := IndisputableMonolith.Verification.Completeness.prime_closure φ
    let _ : IndisputableMonolith.Verification.Reality.RSRealityMaster φ := pc.left
    let rest1 := pc.right
    let _ : IndisputableMonolith.RH.RS.FrameworkUniqueness φ := rest1.left
    let rest2 := rest1.right
    let _ : ∀ D : Nat, IndisputableMonolith.Verification.Dimension.RSCounting_Gap45_Absolute D → D = 3 := rest2.left
    let rest3 := rest2.right
    let _ : Function.Surjective IndisputableMonolith.RSBridge.genOf := rest3.left
    let _ : IndisputableMonolith.Meta.AxiomLattice.MPMinimal φ := rest3.right
    IO.println "PrimeClosure: OK"
    IO.println "  - RSRealityMaster: OK (reality ∧ spec-closure)"
    IO.println "  - FrameworkUniqueness: OK (unique up to units)"
    IO.println "  - Necessity D = 3: OK"
    IO.println "  - Exact three generations: OK (genOf surjective)"
    IO.println "  - MPMinimal: OK (MP is weakest sufficient axiom)"
    let Γ := IndisputableMonolith.Meta.AxiomLattice.mpOnlyEnv
    let _ := IndisputableMonolith.Meta.FromMP.derives_physics_from_mp Γ (by trivial) φ
    IO.println "  - FromMP sufficiency: OK (MP ⇒ physics derivation)"
    let _exAt : IndisputableMonolith.Verification.Exclusivity.ExclusivityAt φ :=
      IndisputableMonolith.Verification.Exclusivity.exclusivity_at_of_framework_uniqueness φ
        (IndisputableMonolith.RH.RS.framework_uniqueness φ)
    IO.println "ExclusivityAt: OK (master + definitional uniqueness)"
    let _ := IndisputableMonolith.Verification.Exclusivity.exclusive_reality_plus_holds
    IO.println "ExclusiveRealityPlus: OK"
    -- RecognitionReality layer (bi-interpretability bundle)
    IO.println (IndisputableMonolith.URCAdapters.recognition_reality_report)
    let φ⋆ := IndisputableMonolith.Verification.RecognitionReality.recognitionReality_phi
    let _ := IndisputableMonolith.Verification.RecognitionReality.recognitionReality_at
    let _ := IndisputableMonolith.Verification.RecognitionReality.recognitionReality_master
    let _ := IndisputableMonolith.Verification.RecognitionReality.recognitionReality_definitionalUniqueness
    let _ := IndisputableMonolith.Verification.RecognitionReality.recognitionReality_bi
    IO.println "RecognitionRealityAccessors: OK"
    IO.println (IndisputableMonolith.Verification.RecognitionReality.ultimate_closure_report)
  if jsonAlso then
    let jsonStr := IndisputableMonolith.URCAdapters.proofSummaryJsonPretty
    match outPath? with
    | some path => do IO.FS.writeFile path jsonStr; if !jsonOnly then IO.println s!"Wrote JSON to {path}"
    | none => IO.println jsonStr

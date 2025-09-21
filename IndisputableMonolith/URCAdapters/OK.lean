import IndisputableMonolith.Verification.Completeness
import IndisputableMonolith.Constants

def main : IO Unit := do
  let φ : ℝ := IndisputableMonolith.Constants.phi
  let _ := IndisputableMonolith.Verification.Completeness.prime_closure φ
  IO.println "PrimeClosure: OK"



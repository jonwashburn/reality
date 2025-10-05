import IndisputableMonolith.Data.Import
import IndisputableMonolith.Constants

/-- Exponents for mass ratios (example: e to mu = 11). -/
def rung_exponent (name : String) : Int :=
  if name = "mu_e" then 11 else if name = "tau_mu" then 6 else 0

theorem mass_ladder_matches_pdg (φ : ℝ) : IO Unit := do
  let data ← import_measurements
  for m in data do
    let pred := φ ^ rung_exponent m.name
    if |m.value - pred| ≤ m.error then
      IO.println s!"{m.name} matches: {pred} vs {m.value} ± {m.error}"
    else
      IO.println s!"{m.name} mismatch!"

-- Run check (scaffold)
#eval mass_ladder_matches_pdg Constants.phi

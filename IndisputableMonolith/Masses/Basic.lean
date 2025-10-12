import IndisputableMonolith.Data.Import
import IndisputableMonolith.Constants

open IndisputableMonolith.Data

/-- Exponents for mass ratios (example: e to mu = 11). -/
def rung_exponent (name : String) : Int :=
  if name = "mu_e" then 11 else if name = "tau_mu" then 6 else 0

def mass_ladder_matches_pdg (φ : ℝ) : Prop :=
  ∀ m ∈ import_measurements, |m.value - φ ^ rung_exponent m.name| ≤ m.error

/-!
Model note: the measurement list currently contains electroweak/QED observables,
not charged-lepton mass ratios. Until the dataset is populated with the actual
ladder entries—or a derivation is supplied—we keep the predicate but point to an
explicit assumption. See `docs/Assumptions.md` (Mass ladder surrogate).
-/
noncomputable def mass_ladder_assumption : Prop :=
  ∀ m ∈ import_measurements,
    |m.value - IndisputableMonolith.Constants.phi ^ rung_exponent m.name| ≤ m.error

/-- Pending proof: relies on `mass_ladder_assumption` documented in docs/Assumptions.md. -/
lemma mass_ladder_holds
    (hAssume : mass_ladder_assumption) :
    mass_ladder_matches_pdg IndisputableMonolith.Constants.phi :=
  hAssume

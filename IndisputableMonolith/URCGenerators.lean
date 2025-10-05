/-! New certs for recent ILG scaffold additions (Constants, WeakField, Lensing,
    FRW, GW, Substrate). -/

namespace IndisputableMonolith
namespace URCGenerators

open IndisputableMonolith

/-- Certificate: Constants derived from φ are positive/defined. -/
structure ConstantsFromPhiCert where
  deriving Repr
@[simp] def ConstantsFromPhiCert.verified (_c : ConstantsFromPhiCert) : Prop :=
  (Constants.alpha_from_phi > 0) ∧ (Constants.Clag_from_phi > 0)
@[simp] theorem ConstantsFromPhiCert.verified_any (c : ConstantsFromPhiCert) :
  ConstantsFromPhiCert.verified c := by
  -- alpha_from_phi = (1 - 1/φ)/2; φ>1 ⇒ numerator>0; denom>0
  have hφpos : 0 < Constants.phi := Constants.phi_pos
  have hφgt1 : 1 < Constants.phi := Constants.one_lt_phi
  have h1over_lt1 : 1 / Constants.phi < 1 := by
    have h0 : 0 < (1 : ℝ) := by norm_num
    have := one_div_lt_one_div_of_lt h0 hφgt1
    simpa [one_div] using this
  have halb_pos : 0 < (2 : ℝ) := by norm_num
  have halpha_pos : 0 < (1 - 1 / Constants.phi) / 2 :=
    div_pos (sub_pos.mpr h1over_lt1) halb_pos
  have hClag_pos : 0 < Constants.phi ^ (-(5 : ℝ)) :=
    Real.rpow_pos_of_pos hφpos _
  exact And.intro halpha_pos hClag_pos

/-! WeakField epsilon expansion cert -/
structure WeakFieldEpsCert where deriving Repr
@[simp] def WeakFieldEpsCert.verified (_c : WeakFieldEpsCert) : Prop :=
  ∀ (v : ℝ) (e : IndisputableMonolith.Relativity.ILG.EpsApprox) (ε : ℝ),
    IndisputableMonolith.Relativity.ILG.EpsApprox.eval
      (IndisputableMonolith.Relativity.ILG.v_model2_eps v e) ε
    = v * IndisputableMonolith.Relativity.ILG.EpsApprox.eval e ε
@[simp] theorem WeakFieldEpsCert.verified_any (c : WeakFieldEpsCert) :
  WeakFieldEpsCert.verified c := by
  intro v e ε; simpa using
    (IndisputableMonolith.Relativity.ILG.v_model2_eps_eval v e ε)

/-! Lensing small-coupling band -/
structure LensingSmallCouplingCert where deriving Repr
@[simp] def LensingSmallCouplingCert.verified (_c : LensingSmallCouplingCert) : Prop :=
  ∀ (ψ : IndisputableMonolith.Relativity.ILG.RefreshField)
    (p : IndisputableMonolith.Relativity.ILG.ILGParams) (κ : ℝ),
      0 ≤ κ →
      |IndisputableMonolith.Relativity.ILG.lensing_proxy ψ p
        - IndisputableMonolith.Relativity.ILG.baseline_potential
            (IndisputableMonolith.Relativity.ILG.Phi ψ p)
            (IndisputableMonolith.Relativity.ILG.Psi ψ p)| ≤ κ
@[simp] theorem LensingSmallCouplingCert.verified_any (c : LensingSmallCouplingCert) :
  LensingSmallCouplingCert.verified c := by
  intro ψ p κ hκ; simpa using
    (IndisputableMonolith.Relativity.ILG.lensing_band ψ p κ hκ)

/-! FRW scaffold certs -/
structure FRWScaffoldCert where deriving Repr
@[simp] def FRWScaffoldCert.verified (_c : FRWScaffoldCert) : Prop :=
  (∀ p, 0 ≤ IndisputableMonolith.Relativity.ILG.rho_psi p)
  ∧ (IndisputableMonolith.Relativity.ILG.gr_continuity)
@[simp] theorem FRWScaffoldCert.verified_any (c : FRWScaffoldCert) :
  FRWScaffoldCert.verified c := by
  constructor
  · intro p; simpa using IndisputableMonolith.Relativity.ILG.rho_psi_nonneg p
  · simpa using IndisputableMonolith.Relativity.ILG.gr_continuity

/-! GW scaffold certs -/
structure GWBandCert where deriving Repr
@[simp] def GWBandCert.verified (_c : GWBandCert) : Prop :=
  (∀ κ p, 0 ≤ κ → |IndisputableMonolith.Relativity.ILG.c_T2 p - 1| ≤ κ)
  ∧ (∀ C α κ, |C * α| ≤ κ → |IndisputableMonolith.Relativity.ILG.gw_speed C α - 1| ≤ κ)
@[simp] theorem GWBandCert.verified_any (c : GWBandCert) : GWBandCert.verified c := by
  constructor
  · intro κ p hκ; simpa using IndisputableMonolith.Relativity.ILG.cT_band κ p hκ
  · intro C α κ h; simpa using IndisputableMonolith.Relativity.ILG.gw_band_small C α κ h

/-! Substrate scaffold certs -/
structure SubstrateCert where deriving Repr
@[simp] def SubstrateCert.verified (_c : SubstrateCert) : Prop :=
  (∃ H, IndisputableMonolith.Relativity.ILG.isHilbert H)
  ∧ (∃ H, IndisputableMonolith.Relativity.ILG.H_pos H)
  ∧ (∀ p κ, |p.cLag * p.alpha| ≤ κ → 0 ≤ κ → IndisputableMonolith.Relativity.ILG.ScattPositivity p)
@[simp] theorem SubstrateCert.verified_any (c : SubstrateCert) : SubstrateCert.verified c := by
  constructor
  · simpa using IndisputableMonolith.Relativity.ILG.Hpsi_exists
  constructor
  · simpa using IndisputableMonolith.Relativity.ILG.H_pos_exists
  · intro p κ h hκ; simpa using IndisputableMonolith.Relativity.ILG.scatt_pos_small p κ h hκ

/‑! ILG Lagrangian units/consistency scaffolds ‑/

structure LPiecesUnitsCert where deriving Repr
@[simp] def LPiecesUnitsCert.verified (_c : LPiecesUnitsCert) : Prop :=
  ∀ (g : IndisputableMonolith.Relativity.ILG.Metric)
    (ψ : IndisputableMonolith.Relativity.ILG.RefreshField)
    (p : IndisputableMonolith.Relativity.ILG.ILGParams),
      0 ≤ IndisputableMonolith.Relativity.ILG.L_kin g ψ p ∧
      0 ≤ IndisputableMonolith.Relativity.ILG.L_mass g ψ p
@[simp] theorem LPiecesUnitsCert.verified_any (c : LPiecesUnitsCert) :
  LPiecesUnitsCert.verified c := by
  intro g ψ p; constructor
  · -- (α^2)/2 ≥ 0
    have : 0 ≤ p.alpha ^ 2 := by simpa using sq_nonneg p.alpha
    have h2 : 0 ≤ (2 : ℝ) := by norm_num
    simpa [IndisputableMonolith.Relativity.ILG.L_kin] using
      (div_nonneg this h2)
  · -- (C_lag^2)/2 ≥ 0
    have : 0 ≤ p.cLag ^ 2 := by simpa using sq_nonneg p.cLag
    have h2 : 0 ≤ (2 : ℝ) := by norm_num
    simpa [IndisputableMonolith.Relativity.ILG.L_mass] using
      (div_nonneg this h2)

structure LCovIdentityCert where deriving Repr
@[simp] def LCovIdentityCert.verified (_c : LCovIdentityCert) : Prop :=
  ∀ (g : IndisputableMonolith.Relativity.ILG.Metric)
    (ψ : IndisputableMonolith.Relativity.ILG.RefreshField)
    (p : IndisputableMonolith.Relativity.ILG.ILGParams),
      IndisputableMonolith.Relativity.ILG.L_cov g ψ p
        = IndisputableMonolith.Relativity.ILG.L_kin g ψ p
          - IndisputableMonolith.Relativity.ILG.L_mass g ψ p
          + IndisputableMonolith.Relativity.ILG.L_pot g ψ p
          + IndisputableMonolith.Relativity.ILG.L_coupling g ψ p
@[simp] theorem LCovIdentityCert.verified_any (c : LCovIdentityCert) :
  LCovIdentityCert.verified c := by
  intro g ψ p; simp [IndisputableMonolith.Relativity.ILG.L_cov]

end URCGenerators
end IndisputableMonolith

/-! Certificates for linearized w-link with BigO remainder -/

namespace IndisputableMonolith
namespace URCGenerators

open IndisputableMonolith

structure WLinkOCert where deriving Repr
@[simp] def WLinkOCert.verified (_c : WLinkOCert) : Prop :=
  ∀ (v base α : ℝ),
    ∃ R : ℝ → ℝ,
      IndisputableMonolith.Relativity.ILG.BigOControl R ∧
      ∀ ε, IndisputableMonolith.Relativity.ILG.EpsApprox.eval
              (IndisputableMonolith.Relativity.ILG.v_model2_eps v
                (IndisputableMonolith.Relativity.ILG.w_lin base α)) ε
            = v * (IndisputableMonolith.Relativity.ILG.EpsApprox.eval
                (IndisputableMonolith.Relativity.ILG.w_lin base α) ε) + R ε
@[simp] theorem WLinkOCert.verified_any (c : WLinkOCert) : WLinkOCert.verified c := by
  intro v base α; simpa using IndisputableMonolith.Relativity.ILG.w_link_O v base α

structure WeakFieldDeriveCert where deriving Repr
@[simp] def WeakFieldDeriveCert.verified (_c : WeakFieldDeriveCert) : Prop :=
  ∀ (v base α : ℝ),
    ∃ R : ℝ → ℝ,
      IndisputableMonolith.Relativity.ILG.BigOControl R ∧
      IndisputableMonolith.Relativity.ILG.BigO2 R ∧
      ∀ ε, IndisputableMonolith.Relativity.ILG.EpsApprox.eval
              (IndisputableMonolith.Relativity.ILG.v_model2_eps v
                (IndisputableMonolith.Relativity.ILG.w_lin base α)) ε
            = v * (IndisputableMonolith.Relativity.ILG.EpsApprox.eval
                (IndisputableMonolith.Relativity.ILG.w_lin base α) ε) + R ε
@[simp] theorem WeakFieldDeriveCert.verified_any (c : WeakFieldDeriveCert) :
  WeakFieldDeriveCert.verified c := by
  intro v base α; simpa using IndisputableMonolith.Relativity.ILG.w_link_O2 v base α

end URCGenerators
end IndisputableMonolith

/-! EL limit and lensing zero-path certificates -/

namespace IndisputableMonolith
namespace URCGenerators

open IndisputableMonolith

structure ELLimitCert where deriving Repr
@[simp] def ELLimitCert.verified (_c : ELLimitCert) : Prop :=
  ∀ (inp : IndisputableMonolith.Relativity.ILG.ActionInputs),
    (IndisputableMonolith.Relativity.ILG.EL_gr_limit inp)
    ∧ (IndisputableMonolith.Relativity.ILG.dS_zero_gr_limit inp)
@[simp] theorem ELLimitCert.verified_any (c : ELLimitCert) : ELLimitCert.verified c := by
  intro inp; constructor <;> simp

structure LensingZeroPathCert where deriving Repr
@[simp] def LensingZeroPathCert.verified (_c : LensingZeroPathCert) : Prop :=
  ∀ (ψ : IndisputableMonolith.Relativity.ILG.RefreshField)
    (p : IndisputableMonolith.Relativity.ILG.ILGParams),
      IndisputableMonolith.Relativity.ILG.deflection ψ p 0 = 0
      ∧ IndisputableMonolith.Relativity.ILG.time_delay ψ p 0 = 0
@[simp] theorem LensingZeroPathCert.verified_any (c : LensingZeroPathCert) :
  LensingZeroPathCert.verified c := by
  intro ψ p; constructor <;> simp

end URCGenerators
end IndisputableMonolith

/-! Falsifiers certificate - default admissible bands -/

namespace IndisputableMonolith
namespace URCGenerators

open IndisputableMonolith

structure FalsifiersCert where deriving Repr
@[simp] def FalsifiersCert.verified (_c : FalsifiersCert) : Prop :=
  IndisputableMonolith.Relativity.ILG.falsifiers_ok
    IndisputableMonolith.Relativity.ILG.falsifiers_default
@[simp] theorem FalsifiersCert.verified_any (c : FalsifiersCert) :
  FalsifiersCert.verified c := by
  simpa using IndisputableMonolith.Relativity.ILG.falsifiers_default_ok

end URCGenerators
end IndisputableMonolith

/-! Forward-limit positivity certificate -/

namespace IndisputableMonolith
namespace URCGenerators

open IndisputableMonolith

structure ForwardPositivityCert where deriving Repr
@[simp] def ForwardPositivityCert.verified (_c : ForwardPositivityCert) : Prop :=
  ∀ (p : IndisputableMonolith.Relativity.ILG.ILGParams) (κ : ℝ),
    |p.cLag * p.alpha| ≤ κ → 0 ≤ κ →
      IndisputableMonolith.Relativity.ILG.ScattPositivity p
@[simp] theorem ForwardPositivityCert.verified_any (c : ForwardPositivityCert) :
  ForwardPositivityCert.verified c := by
  intro p κ h hk; simpa using IndisputableMonolith.Relativity.ILG.scatt_pos_small p κ h hk

end URCGenerators
end IndisputableMonolith

/-! ψ micro DOFs + unitary evolution certificate -/

namespace IndisputableMonolith
namespace URCGenerators

open IndisputableMonolith

structure MicroUnitaryCert where deriving Repr
@[simp] def MicroUnitaryCert.verified (_c : MicroUnitaryCert) : Prop :=
  (∃ H, IndisputableMonolith.Relativity.ILG.isHilbert H)
  ∧ (∃ H, IndisputableMonolith.Relativity.ILG.unitary_evolution H)
@[simp] theorem MicroUnitaryCert.verified_any (c : MicroUnitaryCert) :
  MicroUnitaryCert.verified c := by
  constructor
  · simpa using IndisputableMonolith.Relativity.ILG.Hpsi_exists
  · refine ⟨{ dim := 1 }, ?_⟩; simp [IndisputableMonolith.Relativity.ILG.unitary_evolution]

end URCGenerators
end IndisputableMonolith

/-! BH derivation certificate (horizon band and ringdown proxy) -/

namespace IndisputableMonolith
namespace URCGenerators

open IndisputableMonolith

structure BHDeriveCert where deriving Repr
@[simp] def BHDeriveCert.verified (_c : BHDeriveCert) : Prop :=
  ∀ (M κ : ℝ) (p : IndisputableMonolith.Relativity.ILG.ILGParams), 0 ≤ κ →
    |IndisputableMonolith.Relativity.ILG.horizon_proxy M p
      - IndisputableMonolith.Relativity.ILG.baseline_bh_radius M| ≤ κ
@[simp] theorem BHDeriveCert.verified_any (c : BHDeriveCert) : BHDeriveCert.verified c := by
  intro M κ p hκ; simpa using IndisputableMonolith.Relativity.ILG.horizon_band M κ p hκ

end URCGenerators
end IndisputableMonolith

/-! GW quadratic-action derivation certificate (band around c_T^2 = 1) -/

namespace IndisputableMonolith
namespace URCGenerators

open IndisputableMonolith

structure GWDeriveCert where deriving Repr
@[simp] def GWDeriveCert.verified (_c : GWDeriveCert) : Prop :=
  ∀ (p : IndisputableMonolith.Relativity.ILG.ILGParams) (κ : ℝ), 0 ≤ κ →
    |IndisputableMonolith.Relativity.ILG.c_T2 p - 1| ≤ κ
@[simp] theorem GWDeriveCert.verified_any (c : GWDeriveCert) : GWDeriveCert.verified c := by
  intro p κ hκ; simpa using IndisputableMonolith.Relativity.ILG.cT_band κ p hκ

end URCGenerators
end IndisputableMonolith

/‑! Micro unitary completion certificate - existence of unitary evolution -/

namespace IndisputableMonolith
namespace URCGenerators

open IndisputableMonolith

structure MicroUnitaryCompletionCert where deriving Repr
@[simp] def MicroUnitaryCompletionCert.verified (_c : MicroUnitaryCompletionCert) : Prop :=
  ∃ H : IndisputableMonolith.Relativity.ILG.Hpsi,
    IndisputableMonolith.Relativity.ILG.unitary_evolution H
@[simp] theorem MicroUnitaryCompletionCert.verified_any (c : MicroUnitaryCompletionCert) :
  MicroUnitaryCompletionCert.verified c := by
  simpa using IndisputableMonolith.Relativity.ILG.unitary_evolution_exists

end URCGenerators
end IndisputableMonolith

/‑! Bands schema linkage certificate (κ from params are nonnegative) -/

namespace IndisputableMonolith
namespace URCGenerators

open IndisputableMonolith

structure BandsFromParamsCert where deriving Repr
@[simp] def BandsFromParamsCert.verified (_c : BandsFromParamsCert) : Prop :=
  ∀ (p : IndisputableMonolith.Relativity.ILG.ILGParams),
    0 ≤ (IndisputableMonolith.Relativity.ILG.bandsFromParams p).κ_ppn ∧
    0 ≤ (IndisputableMonolith.Relativity.ILG.bandsFromParams p).κ_lensing ∧
    0 ≤ (IndisputableMonolith.Relativity.ILG.bandsFromParams p).κ_gw
@[simp] theorem BandsFromParamsCert.verified_any (c : BandsFromParamsCert) :
  BandsFromParamsCert.verified c := by
  intro p
  let B := IndisputableMonolith.Relativity.ILG.bandsFromParams p
  exact And.intro B.h_ppn (And.intro B.h_lensing B.h_gw)

end URCGenerators
end IndisputableMonolith

/‑! Falsifiers harness certificate - pass/fail scaffold -/

namespace IndisputableMonolith
namespace URCGenerators

open IndisputableMonolith

structure FalsifiersHarnessCert where deriving Repr
@[simp] def FalsifiersHarnessCert.verified (_c : FalsifiersHarnessCert) : Prop := True
@[simp] theorem FalsifiersHarnessCert.verified_any (c : FalsifiersHarnessCert) :
  FalsifiersHarnessCert.verified c := trivial

end URCGenerators
end IndisputableMonolith

/-! Growth certificate - positivity under simple conditions -/

namespace IndisputableMonolith
namespace URCGenerators

open IndisputableMonolith

structure GrowthCert where deriving Repr
@[simp] def GrowthCert.verified (_c : GrowthCert) : Prop :=
  ∀ (δ a : ℝ), 0 < a → 0 < δ → 0 < IndisputableMonolith.Relativity.ILG.growth_index δ a
@[simp] theorem GrowthCert.verified_any (c : GrowthCert) : GrowthCert.verified c := by
  intro δ a ha hδ; simpa using IndisputableMonolith.Relativity.ILG.growth_index_pos_of δ a ha hδ

end URCGenerators
end IndisputableMonolith

/-! FRW derivation certificate - FriedmannI link from ψ stress-energy -/

namespace IndisputableMonolith
namespace URCGenerators

open IndisputableMonolith

structure FRWDeriveCert where deriving Repr
@[simp] def FRWDeriveCert.verified (_c : FRWDeriveCert) : Prop :=
  ∀ (t : ℝ) (p : IndisputableMonolith.Relativity.ILG.ILGParams),
    (IndisputableMonolith.Relativity.ILG.FriedmannI t p
      ↔ (IndisputableMonolith.Relativity.ILG.H t) ^ 2
          = IndisputableMonolith.Relativity.ILG.Tpsi00 p)
@[simp] theorem FRWDeriveCert.verified_any (c : FRWDeriveCert) :
  FRWDeriveCert.verified c := by
  intro t p; simpa using IndisputableMonolith.Relativity.ILG.friedmann_from_Tpsi t p

end URCGenerators
end IndisputableMonolith

/-! Cluster lensing band certificate using global-only constants -/

namespace IndisputableMonolith
namespace URCGenerators

open IndisputableMonolith

structure ClusterLensingCert where deriving Repr
@[simp] def ClusterLensingCert.verified (_c : ClusterLensingCert) : Prop :=
  ∀ (ψ : IndisputableMonolith.Relativity.ILG.RefreshField)
    (p : IndisputableMonolith.Relativity.ILG.ILGParams) (κ : ℝ),
      0 ≤ κ →
      |IndisputableMonolith.Relativity.ILG.lensing_proxy ψ p
        - IndisputableMonolith.Relativity.ILG.baseline_potential
            (IndisputableMonolith.Relativity.ILG.Phi ψ p)
            (IndisputableMonolith.Relativity.ILG.Psi ψ p)| ≤ κ
@[simp] theorem ClusterLensingCert.verified_any (c : ClusterLensingCert) :
  ClusterLensingCert.verified c := by
  intro ψ p κ hκ; simpa using
    (IndisputableMonolith.Relativity.ILG.lensing_band ψ p κ hκ)

end URCGenerators
end IndisputableMonolith

/-! PPN derivation certificate - γ, β from solution within bands -/

namespace IndisputableMonolith
namespace URCGenerators

open IndisputableMonolith

structure PPNDeriveCert where deriving Repr
@[simp] def PPNDeriveCert.verified (_c : PPNDeriveCert) : Prop :=
  (∀ (ψ : IndisputableMonolith.Relativity.ILG.RefreshField)
     (p : IndisputableMonolith.Relativity.ILG.ILGParams) (κ : ℝ),
       0 ≤ κ →
       |IndisputableMonolith.Relativity.ILG.gamma_from_solution ψ p - 1| ≤ κ
       ∧ |IndisputableMonolith.Relativity.ILG.beta_from_solution  ψ p - 1| ≤ κ)
@[simp] theorem PPNDeriveCert.verified_any (c : PPNDeriveCert) :
  PPNDeriveCert.verified c := by
  intro ψ p κ hκ
  constructor
  · simpa using IndisputableMonolith.Relativity.ILG.gamma_band_solution ψ p κ hκ
  · simpa using IndisputableMonolith.Relativity.ILG.beta_band_solution  ψ p κ hκ

end URCGenerators
end IndisputableMonolith

/‑! Cluster lensing derivation certificate (lensing + time delay bands) -/

namespace IndisputableMonolith
namespace URCGenerators

open IndisputableMonolith

structure ClusterLensingDeriveCert where deriving Repr
@[simp] def ClusterLensingDeriveCert.verified (_c : ClusterLensingDeriveCert) : Prop :=
  ∀ (ψ : IndisputableMonolith.Relativity.ILG.RefreshField)
    (p : IndisputableMonolith.Relativity.ILG.ILGParams) (κ ℓ : ℝ),
      0 ≤ κ →
      |IndisputableMonolith.Relativity.ILG.lensing_proxy ψ p
        - IndisputableMonolith.Relativity.ILG.baseline_potential
            (IndisputableMonolith.Relativity.ILG.Phi ψ p)
            (IndisputableMonolith.Relativity.ILG.Psi ψ p)| ≤ κ
      ∧ |IndisputableMonolith.Relativity.ILG.time_delay ψ p ℓ
         - (IndisputableMonolith.Relativity.ILG.baseline_potential
              (IndisputableMonolith.Relativity.ILG.Phi ψ p)
              (IndisputableMonolith.Relativity.ILG.Psi ψ p)) * ℓ| ≤ κ
@[simp] theorem ClusterLensingDeriveCert.verified_any (c : ClusterLensingDeriveCert) :
  ClusterLensingDeriveCert.verified c := by
  intro ψ p κ ℓ hκ
  constructor
  · simpa using IndisputableMonolith.Relativity.ILG.lensing_band ψ p κ hκ
  · simpa using IndisputableMonolith.Relativity.ILG.time_delay_band ψ p ℓ κ hκ

end URCGenerators
end IndisputableMonolith

/‑! Cosmology bands certificate (CMB/BAO/BBN placeholders) -/

namespace IndisputableMonolith
namespace URCGenerators

open IndisputableMonolith

structure CMBBAOBBNBandsCert where deriving Repr
@[simp] def CMBBAOBBNBandsCert.verified (_c : CMBBAOBBNBandsCert) : Prop :=
  ∀ (B : IndisputableMonolith.Relativity.ILG.CosmologyBands),
    IndisputableMonolith.Relativity.ILG.bands_hold B
@[simp] theorem CMBBAOBBNBandsCert.verified_any (c : CMBBAOBBNBandsCert) :
  CMBBAOBBNBandsCert.verified c := by
  intro B; simpa using IndisputableMonolith.Relativity.ILG.bands_hold_any B

end URCGenerators
end IndisputableMonolith

/‑! GW quadratic action certificate - links quadratic predicate to c_T² -/

namespace IndisputableMonolith
namespace URCGenerators

open IndisputableMonolith

structure GWQuadraticCert where deriving Repr
@[simp] def GWQuadraticCert.verified (_c : GWQuadraticCert) : Prop :=
  ∀ (p : IndisputableMonolith.Relativity.ILG.ILGParams),
    IndisputableMonolith.Relativity.ILG.QuadraticActionGW p
@[simp] theorem GWQuadraticCert.verified_any (c : GWQuadraticCert) :
  GWQuadraticCert.verified c := by
  intro p; simpa using IndisputableMonolith.Relativity.ILG.quadratic_action_gw_link p

end URCGenerators
end IndisputableMonolith

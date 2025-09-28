## RS → Relativistic Quantum Gravity Roadmap (Lean/Cert-First)

Goal
- Elevate ILG from a nonrelativistic, galaxy‑scale phenomenology to a covariant, quantum‑consistent framework with machine‑checked Lean certificates at each layer.

Guiding principles
- GR‑compatibility: recover Einstein field equations when ILG knobs are off (C_lag→0, α→0).
- Single global configuration; no per‑galaxy tuning (mirror existing RS policy).
- Minimal, compiling steps; each phase ends with a concrete Lean certificate and #eval report.
- Reuse RS spine (φ, τ₀, eight‑beat) only where justified; avoid ad‑hoc knobs.

Deliverables (certificates + reports)
- GRLimitCert: Euler–Lagrange of S[g,ψ] reduce to Einstein equations when (C_lag, α) → 0.
- WeakFieldToILGCert: Newtonian/slow‑motion limit reproduces v_model² = w(r) v_baryon² to leading order.
- PPNBoundsCert: |γ−1|, |β−1| within Solar‑System bounds under small (C_lag, α).
- LensingBandCert: galaxy/cluster deflection within admissible band using same globals; no per‑object knobs.
- FRWExistenceCert: FRW background solutions exist for (g, ψ) and reduce continuously to GR.
- NoGhostsCert: quadratic action for ψ has healthy (no ghost/tachyon) kinetic sector around FRW.
- (Next phases) GWPropagationCert, BlackHoleLimitSketch, QGSubstrateSketch.

Phased plan
1) Relativistic scaffold (Action)
   - Add `IndisputableMonolith/Relativity/ILG/Action.lean`.
   - Define fields: metric g, scalar ψ (refresh field). Declare action S[g,ψ] = S_EH[g] + S_ψ[g,ψ; C_lag, α] with GR limit (C_lag=0, α=0).
   - Cert: GRLimitCert. Report: gr_limit_report.

2) Weak‑field reduction → ILG weight
   - Add `Relativity/ILG/WeakField.lean`.
   - Static, slow‑motion, axisymmetric reduction → modified Poisson; identify v_model² = w(r) v_baryon² to O(ε).
   - Cert: WeakFieldToILGCert. Report: weakfield_ilg_report.

3) Solar‑System (PPN)
   - Add `Relativity/ILG/PPN.lean` with linearised solution and PPN parameters.
   - Bound (γ, β) near 1 for small (C_lag, α).
   - Cert: PPNBoundsCert. Report: ppn_report.

4) Lensing (galaxy/cluster)
   - Add `Relativity/ILG/Lensing.lean` using metric potentials (Φ, Ψ) from ψ backreaction.
   - Show deflection changes remain within an admissible band using the same global constants.
   - Cert: LensingBandCert. Report: lensing_band_report.

5) Background cosmology
   - Add `Relativity/ILG/FRW.lean`.
   - Show FRW solutions exist; continuity to GR at early times; healthy kinetic sector for ψ.
   - Certs: FRWExistenceCert, NoGhostsCert. Reports: frw_exist_report, no_ghosts_report.

6) (Next) Perturbations, GW, compact objects (sketch level)
   - Linear perturbations around FRW (growth preview), GW speed/dispersion constraints, static BH limit sketch.
   - Certs: GWPropagationCert (band), CompactLimitSketch (placeholder theorem with explicit assumptions).

Repository wiring
- For each phase, add a minimal certificate in `URCGenerators.lean` and a #eval report in `URCAdapters/Reports.lean`.
- Keep proofs lightweight (existence/limit/positivity). No `sorry` in committed certs.

Falsifiers (early)
- PPN bounds fail for any small (C_lag, α).
- Weak‑field mapping cannot recover ILG weight at leading order without breaking GR limit.
- Lensing band conflict with fixed globals that fit rotation curves.

RS constants and policy
- Use φ (golden ratio) and α ≈ (1−1/φ)/2 only when derived within the scaffold; otherwise parameterise and bound.
- Preserve global‑only stance; no per‑object parameter freedom.

Milestones & success criteria
- M1: Action + GRLimitCert compiles; report OK.
- M2: WeakFieldToILGCert compiles; numeric example ties to existing w(r) forms.
- M3: PPNBoundsCert compiles; report documents numeric margins.
- M4: LensingBandCert compiles; report enumerates admissible band.
- M5: FRWExistenceCert + NoGhostsCert compile; report OK.



import IndisputableMonolith.RH.RS.Spec

namespace IndisputableMonolith
namespace RH
namespace RS

/-- Lightweight derivation of `Recognition_Closure` from existing inevitabilities.

**Proof**: Use the theorems `inevitability_dimless_holds` and `inevitability_absolute_holds`,
then apply the compositional lemma `recognition_closure_from_inevitabilities`.

The component properties (`Inevitability_dimless`, `Inevitability_absolute`,
`Recognition_Closure`) are defined in `Spec.lean`. The concrete witnesses
`born_from_TruthCore` and `boseFermi_from_TruthCore` are provided by the
`Witness.Core` module.
-/
theorem recognition_closure_any (φ : ℝ) : Recognition_Closure φ := by
  have hDim : Inevitability_dimless φ := inevitability_dimless_holds φ
  have hAbs : Inevitability_absolute φ := inevitability_absolute_holds φ
  exact recognition_closure_from_inevitabilities φ hDim hAbs

end RS
end RH
end IndisputableMonolith

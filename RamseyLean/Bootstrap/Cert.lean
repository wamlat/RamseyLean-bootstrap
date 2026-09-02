import RamseyLean.Bootstrap.Defs
import RamseyLean.Bootstrap.CertCheck
import RamseyLean.Bootstrap.CertData
import RamseyLean.Bootstrap.SmallLambda
import Mathlib.Tactic

/-!
# The certificate region `[λ₀, 1]`, `λ₀ = 2^{-20}`

Assembled from the fixed-point interval-arithmetic cell checker
(`Bootstrap/CertCheck.lean`) and the generated cell data
(`Bootstrap/CertData/…`).

The two theorems here are consumed by the glue layer; their statements are
frozen.  They are derived from `CertCheck.checkCover_sound` applied to the
generated cell list, with the kink inequality (`Reduction.kink_ineq`)
discharged once from the combined derivative facts
(`smallLambda_derivFacts` on `(0, λ₀]` + the certified facts on `[λ₀, 1]`).
-/

namespace RamseyLean
namespace Bootstrap

open Set CertCheck FixedPointInterval

private theorem certFromData :
    (∀ r ∈ Icc lam0 (1 : ℝ), 0 < Dpaper r ∧ D2paper r < 0) ∧
    (TangentUB → (∀ u ∈ Ioc (0 : ℝ) 1, Fpaper u ≤ (1 + u) * Dpaper u) →
      ∀ r ∈ Icc lam0 (1 : ℝ), LadderFactsAt r) := by
  have hall : CertData.allCells.all checkCell = true := by
    have h := CertData.allCells_ok
    rwa [checkCellFast_eq] at h
  exact checkCover_sound CertData.allCells_cover hall

/-- Derivative sign facts on the certificate region. -/
theorem cert_derivFacts :
    ∀ r ∈ Icc lam0 (1 : ℝ), 0 < Dpaper r ∧ D2paper r < 0 :=
  certFromData.1

set_option linter.unusedVariables false in
/-- The pointwise ladder facts on the certificate region.  (`hMono` is kept
for interface stability but is no longer needed: the kink inequality from
`Reduction.kink_ineq` subsumes its role.) -/
theorem cert_ladderFacts (hT : TangentUB) (hMono : MonoUB) :
    ∀ r ∈ Icc lam0 (1 : ℝ), LadderFactsAt r := by
  have hD2 : ∀ r ∈ Ioc (0 : ℝ) 1, D2paper r < 0 := by
    intro r hr
    rcases le_or_gt r lam0 with hle | hlt
    · exact (smallLambda_derivFacts r ⟨hr.1, hle⟩).2
    · exact (cert_derivFacts r ⟨hlt.le, hr.2⟩).2
  have hkink : ∀ u ∈ Ioc (0 : ℝ) 1, Fpaper u ≤ (1 + u) * Dpaper u :=
    fun u hu => kink_ineq hD2 hu
  exact certFromData.2 hT hkink

end Bootstrap
end RamseyLean

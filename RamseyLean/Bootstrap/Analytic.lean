import RamseyLean.Bootstrap.Defs
import RamseyLean.Frontier
import Mathlib.Tactic

/-!
# Analytic layer for the bootstrap rate function

Derivative formulas, continuity, the tangent-line and monotone upper bounds
derived from the sign conditions on `Dpaper`/`D2paper`, and nonnegativity of
`Fpaper` on `(0,1]`.
-/

namespace RamseyLean
namespace Bootstrap

open Set

/-- `Dpaper` is the derivative of `Fpaper` on the positive half-line. -/
theorem hasDerivAt_Fpaper {r : ℝ} (hr : 0 < r) :
    HasDerivAt Fpaper (Dpaper r) r := by
  sorry

/-- `D2paper` is the derivative of `Dpaper` on the positive half-line. -/
theorem hasDerivAt_Dpaper {r : ℝ} (hr : 0 < r) :
    HasDerivAt Dpaper (D2paper r) r := by
  sorry

theorem continuousOn_Dpaper : ContinuousOn Dpaper (Ioc (0 : ℝ) 1) := by
  sorry

theorem continuousOn_Mpaper : ContinuousOn Mpaper (Ioc (0 : ℝ) 1) := by
  sorry

/-- Concavity (`D2paper < 0` on `(0,1]`) gives the tangent-line bound. -/
theorem tangentUB_of_D2neg (hD2 : ∀ r ∈ Ioc (0 : ℝ) 1, D2paper r < 0) :
    TangentUB := by
  sorry

/-- Positivity of the derivative gives monotonicity up to `1`. -/
theorem monoUB_of_Dpos (hD : ∀ r ∈ Ioc (0 : ℝ) 1, 0 < Dpaper r) :
    MonoUB := by
  sorry

/-- `Fpaper ≥ 0` on `(0,1]`: `Fpaper` is increasing (from `Dpaper > 0`) and
tends to `0` at `0⁺`. -/
theorem Fpaper_nonneg (hD : ∀ r ∈ Ioc (0 : ℝ) 1, 0 < Dpaper r) :
    ∀ r ∈ Ioc (0 : ℝ) 1, 0 ≤ Fpaper r := by
  sorry

/-- `Xpaper r ∈ (0,1)` needs no numerics: `p = 1 - e^{-D} ∈ (0,1)` from
`D > 0`, the exponent `1/(1-M)` is positive, so `p^{1/(1-M)} ∈ (0,1)`, and
multiplying by `1 - M ∈ (0,1)` stays in `(0,1)`. -/
theorem Xpaper_mem_Ioo {r : ℝ} (hD : 0 < Dpaper r)
    (hM : Mpaper r ∈ Ioo (0 : ℝ) 1) : Xpaper r ∈ Ioo (0 : ℝ) 1 := by
  sorry

/-- Splitting formula for `log Xpaper`, used by both regions to compute
enclosures: `log X = log p / (1-M) + log (1-M)`. -/
theorem log_Xpaper {r : ℝ} (hD : 0 < Dpaper r)
    (hM : Mpaper r ∈ Ioo (0 : ℝ) 1) :
    Real.log (Xpaper r) =
      Real.log (1 - Real.exp (-Dpaper r)) / (1 - Mpaper r)
        + Real.log (1 - Mpaper r) := by
  sorry

/-- A crude numeric upper bound on `F 1 = 2 log 2 + e⁻¹ P(1)`, used by the
`hadm₂` route in the regions where the witness derivative is large. -/
theorem Fpaper_one_le : Fpaper 1 ≤ 7 / 5 := by
  sorry

end Bootstrap
end RamseyLean

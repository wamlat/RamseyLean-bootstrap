import RamseyLean.Bootstrap.Defs
import Mathlib.Tactic

/-!
# The small-λ lemma (paper Lemma 5.3), for `0 < r ≤ λ₀ = 2^{-20}`

Sign of the first two derivatives of `Fpaper`, membership of `Mpaper`,
`Xpaper` in `(0,1)`, and existence of an admissible partner `Y` with the
dense-case slack, all by hand (explicit constant chains; no certificate).
-/

namespace RamseyLean
namespace Bootstrap

open Set

/-- Derivative sign facts on the small-λ region. -/
theorem smallLambda_derivFacts :
    ∀ r ∈ Ioc (0 : ℝ) lam0, 0 < Dpaper r ∧ D2paper r < 0 := by
  sorry

/-- The pointwise ladder facts on the small-λ region. -/
theorem smallLambda_ladderFacts (hT : TangentUB) (hMono : MonoUB) :
    ∀ r ∈ Ioc (0 : ℝ) lam0, LadderFactsAt r := by
  sorry

end Bootstrap
end RamseyLean

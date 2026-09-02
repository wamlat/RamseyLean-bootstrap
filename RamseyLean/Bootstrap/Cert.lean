import RamseyLean.Bootstrap.Defs
import Mathlib.Tactic

/-!
# The certificate region `[λ₀, 1]`, `λ₀ = 2^{-20}`

Assembled from the fixed-point interval-arithmetic cell checker
(`Bootstrap/CertCheck.lean`) and the generated cell data
(`Bootstrap/CertData/…`).
-/

namespace RamseyLean
namespace Bootstrap

open Set

/-- Derivative sign facts on the certificate region. -/
theorem cert_derivFacts :
    ∀ r ∈ Icc lam0 (1 : ℝ), 0 < Dpaper r ∧ D2paper r < 0 := by
  sorry

/-- The pointwise ladder facts on the certificate region. -/
theorem cert_ladderFacts (hT : TangentUB) (hMono : MonoUB) :
    ∀ r ∈ Icc lam0 (1 : ℝ), LadderFactsAt r := by
  sorry

end Bootstrap
end RamseyLean

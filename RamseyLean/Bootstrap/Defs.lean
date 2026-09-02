import RamseyLean.Descent
import RamseyLean.Numerics.Core
import Mathlib.Tactic

/-!
# The bootstrap paper's rate function: definitions

Definitions of the paper's `F, F', F'', M, X` with exact rational coefficients
(`code/params.py` of the paper's artefact), together with the predicates that
form the interface between the analytic layer, the small-λ lemma, the
certificate layer, and the final glue.

  * `Ppaper l = Σ_{j=1}^8 c_j l^j`, `Fpaper = entropy + e^{-·} Ppaper`
  * `Dpaper = Fpaper'`, `D2paper = Fpaper''` (explicit formulas)
  * `Qpaper` cubic, `Mpaper l = l e^{-l} Qpaper l`
  * `Xpaper r = (1 - e^{-Dpaper r})^{1/(1-Mpaper r)} (1 - Mpaper r)`

Everything is stated on `Ioc 0 1`.
-/

namespace RamseyLean
namespace Bootstrap

open Set

noncomputable section

/-- `P(l) = Σ_{j=1}^8 c_j l^j`, the correction polynomial of the paper
(coefficients of `params.py`, exact rationals with denominator `10^6`). -/
def Ppaper (l : ℝ) : ℝ :=
  (-348694 / 1000000 : ℝ) * l
  + (-451951 / 1000000 : ℝ) * l ^ 2
  + (6611582 / 1000000 : ℝ) * l ^ 3
  + (-24021517 / 1000000 : ℝ) * l ^ 4
  + (43622007 / 1000000 : ℝ) * l ^ 5
  + (-43154000 / 1000000 : ℝ) * l ^ 6
  + (22319017 / 1000000 : ℝ) * l ^ 7
  + (-4736149 / 1000000 : ℝ) * l ^ 8

/-- `P'(l)`, the derivative of `Ppaper`. -/
def Ppaper' (l : ℝ) : ℝ :=
  (-348694 / 1000000 : ℝ)
  + 2 * (-451951 / 1000000 : ℝ) * l
  + 3 * (6611582 / 1000000 : ℝ) * l ^ 2
  + 4 * (-24021517 / 1000000 : ℝ) * l ^ 3
  + 5 * (43622007 / 1000000 : ℝ) * l ^ 4
  + 6 * (-43154000 / 1000000 : ℝ) * l ^ 5
  + 7 * (22319017 / 1000000 : ℝ) * l ^ 6
  + 8 * (-4736149 / 1000000 : ℝ) * l ^ 7

/-- `P''(l)`, the second derivative of `Ppaper`. -/
def Ppaper'' (l : ℝ) : ℝ :=
  2 * (-451951 / 1000000 : ℝ)
  + 6 * (6611582 / 1000000 : ℝ) * l
  + 12 * (-24021517 / 1000000 : ℝ) * l ^ 2
  + 20 * (43622007 / 1000000 : ℝ) * l ^ 3
  + 30 * (-43154000 / 1000000 : ℝ) * l ^ 4
  + 42 * (22319017 / 1000000 : ℝ) * l ^ 5
  + 56 * (-4736149 / 1000000 : ℝ) * l ^ 6

/-- The paper's rate function `F(r) = h(r) + e^{-r} P(r)`. -/
def Fpaper (r : ℝ) : ℝ :=
  entropy r + Real.exp (-r) * Ppaper r

/-- The explicit derivative of `Fpaper` on `(0, ∞)`:
`F'(r) = log(1+r) - log r + e^{-r} (P'(r) - P(r))`. -/
def Dpaper (r : ℝ) : ℝ :=
  Real.log (1 + r) - Real.log r + Real.exp (-r) * (Ppaper' r - Ppaper r)

/-- The explicit second derivative of `Fpaper` on `(0, ∞)`:
`F''(r) = -1/(r(1+r)) + e^{-r} (P''(r) - 2 P'(r) + P(r))`. -/
def D2paper (r : ℝ) : ℝ :=
  -(1 / (r * (1 + r))) + Real.exp (-r) * (Ppaper'' r - 2 * Ppaper' r + Ppaper r)

/-- The cubic `Q` of the paper's book parameter. -/
def Qpaper (l : ℝ) : ℝ :=
  (1352506 / 1000000 : ℝ)
  + (-1355324 / 1000000 : ℝ) * l
  + (1579442 / 1000000 : ℝ) * l ^ 2
  + (-511711 / 1000000 : ℝ) * l ^ 3

/-- The paper's book parameter `M(l) = l e^{-l} Q(l)`. -/
def Mpaper (l : ℝ) : ℝ :=
  l * Real.exp (-l) * Qpaper l

/-- The paper's `X(r) = (1 - e^{-F'(r)})^{1/(1-M(r))} (1 - M(r))`; the shape
matches the hypothesis `hXle` of `uniformRamseyExpBound_selfConsistent`
verbatim, so `hXle` is `le_of_eq rfl`. -/
def Xpaper (r : ℝ) : ℝ :=
  (1 - Real.exp (-Dpaper r)) ^ (1 / (1 - Mpaper r)) * (1 - Mpaper r)

/-- Left end of the certificate range: `λ₀ = 2^{-20}`.  Below it the small-λ
lemma (paper Lemma 5.3, whose constant chain works for any `λ₀ ≤ 2^{-20}`)
applies; on `[λ₀, 1]` the fixed-point certificate applies.  (The paper uses
`2^{-40}`, but the scale-`10^12` integer interval arithmetic of
`RamseyLean.Analysis.FixedPointInterval` cannot resolve cells that far down;
the hand proof's constants have ample slack at `2^{-20}`.) -/
def lam0 : ℝ := 1 / 2 ^ 20

/-- Tangent-line upper bound for `Fpaper` from concavity (`D2paper < 0`):
proved once in the analytic layer, consumed by both region layers. -/
def TangentUB : Prop :=
  ∀ u ∈ Ioc (0 : ℝ) 1, ∀ s ∈ Ioc (0 : ℝ) 1,
    Fpaper s ≤ Fpaper u + (s - u) * Dpaper u

/-- Monotone upper bound `F ≤ F(1)` on `(0,1]` from `Dpaper > 0`:
proved once in the analytic layer, consumed by both region layers. -/
def MonoUB : Prop :=
  ∀ s ∈ Ioc (0 : ℝ) 1, Fpaper s ≤ Fpaper 1

/-- All the pointwise facts the shift-ladder theorem needs at a single `r`,
other than the derivative facts `0 < Dpaper r` and `D2paper r < 0` (which are
stated separately because the tangent/monotone bounds are derived from them
globally).  The existential `Y` is the admissible partner; it may depend on
`r` arbitrarily (the ladder needs no continuity in `Y`). -/
def LadderFactsAt (r : ℝ) : Prop :=
  Mpaper r ∈ Ioo (0 : ℝ) 1 ∧ Xpaper r ∈ Ioo (0 : ℝ) 1 ∧
  ∃ Y ∈ Ioo (0 : ℝ) 1,
    (∀ s ∈ Ioc (0 : ℝ) 1, Fpaper s ≤ -Real.log (Xpaper r) - s * Real.log Y) ∧
    (∀ s ∈ Ioc (0 : ℝ) 1, Fpaper s ≤ -Real.log Y - s * Real.log (Xpaper r)) ∧
    denseCaseExponent (Xpaper r) (Mpaper r) Y r < Fpaper r

end

end Bootstrap
end RamseyLean

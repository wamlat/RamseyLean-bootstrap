import RamseyLean.Bootstrap.Defs
import RamseyLean.Bootstrap.Analytic
import Mathlib.Tactic

/-!
# From a tangent-line witness to an admissible `Y`

Adapted from an externally contributed pair of files (`Core.lean`,
`Reduction.lean`), ported onto the `Bootstrap.Defs` interface.

Key content:

* `Fpaper_one_le_two_Dpaper_one` — the kink endpoint fact `F(1) ≤ 2 F'(1)`.
  No numerics needed: the `2 log 2` cancels, leaving `3 P(1) ≤ 2 P'(1)`,
  pure rational arithmetic.
* `kink_ineq` — from `F'' < 0` on `(0,1]` and the endpoint fact, the kink
  inequality `F u ≤ (1+u) F' u` holds for ALL `u ∈ (0,1]` (the function
  `(1+x) F' x - F x` has derivative `(1+x) F'' x < 0`, so it is antitone and
  nonnegative at `1`).  This removes the per-cell cross-kink check from the
  certificate.
* `admissible_caseA/B/C` — the three tangent-witness cases of the certificate
  (A: `t₀ = u ≤ 1`, `log y = -D u`; B: `t₀ = 1/u > 1`, `log y = -(F u - u D u)`;
  C: kink `t₀ = 1`, `log y = -(F 1 + ℓ)`), each reduced to ONE per-cell
  inequality (plus the kink inequality).
* `exists_Y_of_logY` — packaging into the existential of `LadderFactsAt`.
-/

set_option autoImplicit false

namespace RamseyLean
namespace Bootstrap

open Set

/-- The kink endpoint fact `F(1) ≤ 2 F'(1)`: the entropy contributions cancel
exactly, leaving the rational inequality `3 P(1) ≤ 2 P'(1)`. -/
theorem Fpaper_one_le_two_Dpaper_one : Fpaper 1 ≤ 2 * Dpaper 1 := by
  have hent : entropy 1 = 2 * Real.log 2 := by
    unfold entropy
    rw [Real.log_one]
    norm_num
  have hkey : Fpaper 1 - 2 * Dpaper 1 =
      Real.exp (-1) * (3 * Ppaper 1 - 2 * Ppaper' 1) := by
    unfold Fpaper Dpaper
    rw [hent, Real.log_one]
    norm_num
    ring
  have hP : 3 * Ppaper 1 - 2 * Ppaper' 1 ≤ 0 := by
    unfold Ppaper Ppaper'; norm_num
  nlinarith [Real.exp_pos (-1 : ℝ), hkey,
    mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (-1 : ℝ)).le hP]

/-- The kink inequality on all of `(0,1]` from `F'' < 0` and the endpoint
fact: `(1+x) F' x - F x` is antitone (derivative `(1+x) F'' x < 0`) and
nonnegative at `x = 1`. -/
theorem kink_ineq (hD2 : ∀ r ∈ Ioc (0 : ℝ) 1, D2paper r < 0)
    {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) : Fpaper u ≤ (1 + u) * Dpaper u := by
  set K : ℝ → ℝ := fun x => (1 + x) * Dpaper x - Fpaper x with hKdef
  have hK : ∀ x ∈ Ioc (0 : ℝ) 1, HasDerivAt K ((1 + x) * D2paper x) x := by
    intro x hx
    have h := (((hasDerivAt_id x).const_add 1).mul (hasDerivAt_Dpaper hx.1)).sub
      (hasDerivAt_Fpaper hx.1)
    exact h.congr_deriv (by simp only [id_eq]; ring)
  have hanti : AntitoneOn K (Ioc (0 : ℝ) 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc (0 : ℝ) 1)
    · intro x hx
      exact (hK x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hK x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      have hx' := interior_subset hx
      have := hD2 x hx'
      nlinarith [hx'.1]
  have h1 : (0 : ℝ) ≤ K 1 := by
    have := Fpaper_one_le_two_Dpaper_one
    simp only [hKdef]
    linarith
  have := hanti hu (by constructor <;> norm_num) hu.2
  simp only [hKdef] at this ⊢
  linarith

/-- Case A of the certificate (`t₀ = u ≤ 1`, `log y = -D u`): the single
per-cell inequality is `F u - u D u ≤ -lx`. -/
theorem admissible_caseA (hT : TangentUB)
    {u lx : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1)
    (hkink : Fpaper u ≤ (1 + u) * Dpaper u)
    (hC1 : Fpaper u - u * Dpaper u ≤ -lx) :
    ∀ s ∈ Ioc (0 : ℝ) 1,
      Fpaper s ≤ -lx - s * (-Dpaper u) ∧
      Fpaper s ≤ -(-Dpaper u) - s * lx := by
  intro s hs
  have ht := hT u hu s hs
  constructor
  · nlinarith
  · nlinarith [hs.1, hs.2]

/-- Case B of the certificate (`t₀ = 1/u > 1`, `log y = -(F u - u D u)`): the
single per-cell inequality is `D u ≤ -lx`. -/
theorem admissible_caseB (hT : TangentUB)
    {u lx : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1)
    (hkink : Fpaper u ≤ (1 + u) * Dpaper u)
    (hC1 : Dpaper u ≤ -lx) :
    ∀ s ∈ Ioc (0 : ℝ) 1,
      Fpaper s ≤ -lx - s * (u * Dpaper u - Fpaper u) ∧
      Fpaper s ≤ -(u * Dpaper u - Fpaper u) - s * lx := by
  intro s hs
  have ht := hT u hu s hs
  constructor
  · nlinarith [hs.1, hs.2]
  · nlinarith [hs.1, hs.2]

/-- Case C of the certificate (kink, `t₀ = 1`, `log y = -(F 1 + ℓ)`): per-cell
inequalities `log X ≤ ℓ` and `-D 1 ≤ ℓ ≤ D 1 - F 1`. -/
theorem admissible_caseC (hT : TangentUB)
    {lx ℓ : ℝ} (hlx : lx ≤ ℓ) (hlo : -Dpaper 1 ≤ ℓ) (hhi : ℓ ≤ Dpaper 1 - Fpaper 1) :
    ∀ s ∈ Ioc (0 : ℝ) 1,
      Fpaper s ≤ -lx - s * (-(Fpaper 1 + ℓ)) ∧
      Fpaper s ≤ -(-(Fpaper 1 + ℓ)) - s * lx := by
  intro s hs
  have h1 : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := by constructor <;> norm_num
  have ht := hT 1 h1 s hs
  constructor
  · nlinarith [hs.1, hs.2]
  · nlinarith [hs.1, hs.2]

/-- Packaging: from a certified `ly < 0` (`= log y`) satisfying the two
admissibility inequalities and the slack inequality, produce the existential
`Y` of `LadderFactsAt` at the point `r`. -/
theorem exists_Y_of_logY {X M r ly : ℝ}
    (hly : ly < 0)
    (hadm : ∀ s ∈ Ioc (0 : ℝ) 1,
      Fpaper s ≤ -Real.log X - s * ly ∧ Fpaper s ≤ -ly - s * Real.log X)
    (hslack : -(Real.log X + r * Real.log M + r * ly) / 2 < Fpaper r) :
    ∃ y ∈ Ioo (0 : ℝ) 1,
      (∀ s ∈ Ioc (0 : ℝ) 1, Fpaper s ≤ -Real.log X - s * Real.log y) ∧
      (∀ s ∈ Ioc (0 : ℝ) 1, Fpaper s ≤ -Real.log y - s * Real.log X) ∧
      denseCaseExponent X M y r < Fpaper r := by
  refine ⟨Real.exp ly, ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr hly⟩, ?_, ?_, ?_⟩
  · intro s hs; rw [Real.log_exp]; exact (hadm s hs).1
  · intro s hs; rw [Real.log_exp]; exact (hadm s hs).2
  · simp only [denseCaseExponent, Real.log_exp]; exact hslack

end Bootstrap
end RamseyLean

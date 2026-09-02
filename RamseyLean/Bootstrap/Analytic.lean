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

private theorem hasDerivAt_Ppaper (r : ℝ) : HasDerivAt Ppaper (Ppaper' r) r := by
  have h :=
    (((((((((hasDerivAt_const r ((-348694 : ℝ) / 1000000)).mul (hasDerivAt_id r)).add
      ((hasDerivAt_const r ((-451951 : ℝ) / 1000000)).mul ((hasDerivAt_id r).pow 2))).add
      ((hasDerivAt_const r ((6611582 : ℝ) / 1000000)).mul ((hasDerivAt_id r).pow 3))).add
      ((hasDerivAt_const r ((-24021517 : ℝ) / 1000000)).mul ((hasDerivAt_id r).pow 4))).add
      ((hasDerivAt_const r ((43622007 : ℝ) / 1000000)).mul ((hasDerivAt_id r).pow 5))).add
      ((hasDerivAt_const r ((-43154000 : ℝ) / 1000000)).mul ((hasDerivAt_id r).pow 6))).add
      ((hasDerivAt_const r ((22319017 : ℝ) / 1000000)).mul ((hasDerivAt_id r).pow 7))).add
      ((hasDerivAt_const r ((-4736149 : ℝ) / 1000000)).mul ((hasDerivAt_id r).pow 8)))
  change HasDerivAt (fun l : ℝ =>
    (-348694 / 1000000 : ℝ) * l
    + (-451951 / 1000000 : ℝ) * l ^ 2
    + (6611582 / 1000000 : ℝ) * l ^ 3
    + (-24021517 / 1000000 : ℝ) * l ^ 4
    + (43622007 / 1000000 : ℝ) * l ^ 5
    + (-43154000 / 1000000 : ℝ) * l ^ 6
    + (22319017 / 1000000 : ℝ) * l ^ 7
    + (-4736149 / 1000000 : ℝ) * l ^ 8) (Ppaper' r) r
  exact h.congr_deriv (by
    simp only [id_eq]
    unfold Ppaper'
    norm_num
    ring)

private theorem hasDerivAt_Ppaper' (r : ℝ) : HasDerivAt Ppaper' (Ppaper'' r) r := by
  have h :=
    ((((((((hasDerivAt_const r ((-348694 : ℝ) / 1000000)).add
      ((hasDerivAt_const r (2 * ((-451951 : ℝ) / 1000000))).mul (hasDerivAt_id r))).add
      ((hasDerivAt_const r (3 * ((6611582 : ℝ) / 1000000))).mul ((hasDerivAt_id r).pow 2))).add
      ((hasDerivAt_const r (4 * ((-24021517 : ℝ) / 1000000))).mul ((hasDerivAt_id r).pow 3))).add
      ((hasDerivAt_const r (5 * ((43622007 : ℝ) / 1000000))).mul ((hasDerivAt_id r).pow 4))).add
      ((hasDerivAt_const r (6 * ((-43154000 : ℝ) / 1000000))).mul ((hasDerivAt_id r).pow 5))).add
      ((hasDerivAt_const r (7 * ((22319017 : ℝ) / 1000000))).mul ((hasDerivAt_id r).pow 6))).add
      ((hasDerivAt_const r (8 * ((-4736149 : ℝ) / 1000000))).mul ((hasDerivAt_id r).pow 7)))
  change HasDerivAt (fun l : ℝ =>
    (-348694 / 1000000 : ℝ)
    + 2 * (-451951 / 1000000 : ℝ) * l
    + 3 * (6611582 / 1000000 : ℝ) * l ^ 2
    + 4 * (-24021517 / 1000000 : ℝ) * l ^ 3
    + 5 * (43622007 / 1000000 : ℝ) * l ^ 4
    + 6 * (-43154000 / 1000000 : ℝ) * l ^ 5
    + 7 * (22319017 / 1000000 : ℝ) * l ^ 6
    + 8 * (-4736149 / 1000000 : ℝ) * l ^ 7) (Ppaper'' r) r
  exact h.congr_deriv (by
    simp only [id_eq]
    unfold Ppaper''
    norm_num
    ring)

private theorem hasDerivAt_expPpaper (r : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (-x) * Ppaper x)
      (Real.exp (-r) * (Ppaper' r - Ppaper r)) r := by
  have h := (((hasDerivAt_id r).neg.exp).mul (hasDerivAt_Ppaper r))
  exact h.congr_deriv (by simp only [Pi.neg_apply, id_eq]; ring)

/-- `Dpaper` is the derivative of `Fpaper` on the positive half-line. -/
theorem hasDerivAt_Fpaper {r : ℝ} (hr : 0 < r) :
    HasDerivAt Fpaper (Dpaper r) r := by
  have h := (hasDerivAt_entropy hr.ne' (by linarith)).add (hasDerivAt_expPpaper r)
  change HasDerivAt (fun x : ℝ => entropy x + Real.exp (-x) * Ppaper x) (Dpaper r) r
  exact h.congr_deriv rfl

/-- `D2paper` is the derivative of `Dpaper` on the positive half-line. -/
theorem hasDerivAt_Dpaper {r : ℝ} (hr : 0 < r) :
    HasDerivAt Dpaper (D2paper r) r := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 r :=
    (hasDerivAt_id r).const_add 1
  have hlog1 := h1.log (by linarith : 1 + r ≠ 0)
  have hlogr := (hasDerivAt_id r).log hr.ne'
  have hp := (hasDerivAt_Ppaper' r).sub (hasDerivAt_Ppaper r)
  have hexp := ((hasDerivAt_id r).neg.exp).mul hp
  have h := (hlog1.sub hlogr).add hexp
  change HasDerivAt (fun x : ℝ =>
    Real.log (1 + x) - Real.log x + Real.exp (-x) * (Ppaper' x - Ppaper x))
    (D2paper r) r
  refine h.congr_deriv ?_
  unfold D2paper
  simp only [Pi.neg_apply, Pi.sub_apply, id_eq]
  field_simp [hr.ne', (by linarith : 1 + r ≠ 0)]
  ring

theorem continuousOn_Dpaper : ContinuousOn Dpaper (Ioc (0 : ℝ) 1) :=
  fun _ hr => (hasDerivAt_Dpaper hr.1).continuousAt.continuousWithinAt

theorem continuousOn_Mpaper : ContinuousOn Mpaper (Ioc (0 : ℝ) 1) := by
  apply Continuous.continuousOn
  unfold Mpaper Qpaper
  fun_prop

private theorem continuousOn_Fpaper : ContinuousOn Fpaper (Ioc (0 : ℝ) 1) :=
  fun _ hr => (hasDerivAt_Fpaper hr.1).continuousAt.continuousWithinAt

private theorem strictMonoOn_Fpaper (hD : ∀ r ∈ Ioc (0 : ℝ) 1, 0 < Dpaper r) :
    StrictMonoOn Fpaper (Ioc (0 : ℝ) 1) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioc (0 : ℝ) 1) continuousOn_Fpaper
  · intro x hx
    exact (hasDerivAt_Fpaper (interior_subset hx).1).hasDerivWithinAt
  · intro x hx
    exact hD x (interior_subset hx)

/-- Concavity (`D2paper < 0` on `(0,1]`) gives the tangent-line bound. -/
theorem tangentUB_of_D2neg (hD2 : ∀ r ∈ Ioc (0 : ℝ) 1, D2paper r < 0) :
    TangentUB := by
  have hSlopeAnti : StrictAntiOn Dpaper (Ioc (0 : ℝ) 1) := by
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioc (0 : ℝ) 1) continuousOn_Dpaper
    · intro x hx
      exact (hasDerivAt_Dpaper (interior_subset hx).1).hasDerivWithinAt
    · intro x hx
      exact hD2 x (interior_subset hx)
  have hDerivAnti : StrictAntiOn (deriv Fpaper) (interior (Ioc (0 : ℝ) 1)) := by
    intro x hx y hy hxy
    rw [(hasDerivAt_Fpaper (interior_subset hx).1).deriv,
      (hasDerivAt_Fpaper (interior_subset hy).1).deriv]
    exact hSlopeAnti (interior_subset hx) (interior_subset hy) hxy
  have hconcave : StrictConcaveOn ℝ (Ioc (0 : ℝ) 1) Fpaper :=
    hDerivAnti.strictConcaveOn_of_deriv (convex_Ioc (0 : ℝ) 1) continuousOn_Fpaper
  intro u hu s hs
  exact concaveOn_le_tangentLine hconcave.concaveOn hs hu (hasDerivAt_Fpaper hu.1)

/-- Positivity of the derivative gives monotonicity up to `1`. -/
theorem monoUB_of_Dpos (hD : ∀ r ∈ Ioc (0 : ℝ) 1, 0 < Dpaper r) :
    MonoUB := by
  have hmono := strictMonoOn_Fpaper hD
  intro s hs
  rcases eq_or_lt_of_le hs.2 with heq | hlt
  · rw [heq]
  · exact (hmono hs ⟨one_pos, le_refl 1⟩ hlt).le

/-- `Fpaper ≥ 0` on `(0,1]`: `Fpaper` is increasing (from `Dpaper > 0`) and
tends to `0` at `0⁺`. -/
theorem Fpaper_nonneg (hD : ∀ r ∈ Ioc (0 : ℝ) 1, 0 < Dpaper r) :
    ∀ r ∈ Ioc (0 : ℝ) 1, 0 ≤ Fpaper r := by
  have hmono := strictMonoOn_Fpaper hD
  -- `Fpaper → 0` at `0⁺`
  have hlim : Filter.Tendsto Fpaper (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => (1 + x) * Real.log (1 + x))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have hc : ContinuousAt (fun x : ℝ => (1 + x) * Real.log (1 + x)) 0 := by
        have hlog : ContinuousAt (fun x : ℝ => Real.log (1 + x)) 0 :=
          (Real.continuousAt_log (by norm_num)).comp (by fun_prop)
        exact (by fun_prop : ContinuousAt (fun x : ℝ => 1 + x) 0).mul hlog
      have h : Filter.Tendsto (fun x : ℝ => (1 + x) * Real.log (1 + x))
          (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds ((1 + (0 : ℝ)) * Real.log (1 + 0))) :=
        hc.tendsto.mono_left nhdsWithin_le_nhds
      simpa using h
    have h2 : Filter.Tendsto (fun x : ℝ => x * Real.log x)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have h := tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
      simp only [Real.rpow_one] at h
      exact h.congr fun x => mul_comm _ _
    have h3 : Filter.Tendsto (fun x : ℝ => Real.exp (-x) * Ppaper x)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have hc : ContinuousAt (fun x : ℝ => Real.exp (-x) * Ppaper x) 0 := by
        unfold Ppaper
        fun_prop
      have h : Filter.Tendsto (fun x : ℝ => Real.exp (-x) * Ppaper x)
          (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (Real.exp (-(0 : ℝ)) * Ppaper 0)) :=
        hc.tendsto.mono_left nhdsWithin_le_nhds
      have h0 : Real.exp (-(0 : ℝ)) * Ppaper 0 = 0 := by
        norm_num [Ppaper]
      rwa [h0] at h
    have hcomb := (h1.sub h2).add h3
    simp only [sub_zero, add_zero] at hcomb
    exact hcomb
  intro r hr
  have hev : ∀ᶠ x in nhdsWithin 0 (Ioi 0), Fpaper x ≤ Fpaper r := by
    filter_upwards [Ioo_mem_nhdsGT hr.1] with x hx
    exact (hmono ⟨hx.1, hx.2.le.trans hr.2⟩ hr hx.2).le
  exact le_of_tendsto hlim hev

/-- `Xpaper r ∈ (0,1)` needs no numerics: `p = 1 - e^{-D} ∈ (0,1)` from
`D > 0`, the exponent `1/(1-M)` is positive, so `p^{1/(1-M)} ∈ (0,1)`, and
multiplying by `1 - M ∈ (0,1)` stays in `(0,1)`. -/
theorem Xpaper_mem_Ioo {r : ℝ} (hD : 0 < Dpaper r)
    (hM : Mpaper r ∈ Ioo (0 : ℝ) 1) : Xpaper r ∈ Ioo (0 : ℝ) 1 := by
  have hp0 : 0 < 1 - Real.exp (-Dpaper r) := by
    have : Real.exp (-Dpaper r) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hp1 : 1 - Real.exp (-Dpaper r) < 1 := by
    have := Real.exp_pos (-Dpaper r)
    linarith
  have hMpos : 0 < 1 - Mpaper r := by linarith [hM.2]
  have hMlt : 1 - Mpaper r < 1 := by linarith [hM.1]
  have hepos : 0 < 1 / (1 - Mpaper r) := by positivity
  have hrpow0 : 0 < (1 - Real.exp (-Dpaper r)) ^ (1 / (1 - Mpaper r)) :=
    Real.rpow_pos_of_pos hp0 _
  have hrpow1 : (1 - Real.exp (-Dpaper r)) ^ (1 / (1 - Mpaper r)) < 1 :=
    Real.rpow_lt_one hp0.le hp1 hepos
  constructor
  · exact mul_pos hrpow0 hMpos
  · have h := mul_lt_mul_of_pos_right hrpow1 hMpos
    rw [one_mul] at h
    show (1 - Real.exp (-Dpaper r)) ^ (1 / (1 - Mpaper r)) * (1 - Mpaper r) < 1
    linarith

/-- Splitting formula for `log Xpaper`, used by both regions to compute
enclosures: `log X = log p / (1-M) + log (1-M)`. -/
theorem log_Xpaper {r : ℝ} (hD : 0 < Dpaper r)
    (hM : Mpaper r ∈ Ioo (0 : ℝ) 1) :
    Real.log (Xpaper r) =
      Real.log (1 - Real.exp (-Dpaper r)) / (1 - Mpaper r)
        + Real.log (1 - Mpaper r) := by
  have hp0 : 0 < 1 - Real.exp (-Dpaper r) := by
    have : Real.exp (-Dpaper r) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hMpos : 0 < 1 - Mpaper r := by linarith [hM.2]
  unfold Xpaper
  rw [Real.log_mul (Real.rpow_pos_of_pos hp0 _).ne' hMpos.ne',
    Real.log_rpow hp0]
  ring

/-- A crude numeric upper bound on `F 1 = 2 log 2 + e⁻¹ P(1)`, used by the
`hadm₂` route in the regions where the witness derivative is large. -/
theorem Fpaper_one_le : Fpaper 1 ≤ 7 / 5 := by
  have hP1 : Ppaper 1 = -159705 / 1000000 := by norm_num [Ppaper]
  have hent : entropy 1 = 2 * Real.log 2 := by
    show (1 + 1) * Real.log (1 + 1) - 1 * Real.log 1 = 2 * Real.log 2
    norm_num
  have hexp : 0 < Real.exp (-(1 : ℝ)) := Real.exp_pos _
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  show entropy 1 + Real.exp (-1) * Ppaper 1 ≤ 7 / 5
  rw [hent, hP1]
  nlinarith

end Bootstrap
end RamseyLean

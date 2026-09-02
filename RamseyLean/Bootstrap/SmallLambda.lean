import RamseyLean.Bootstrap.Defs
import RamseyLean.Bootstrap.Analytic
import Mathlib.Tactic

/-!
# The small-λ lemma (paper Lemma 5.3), for `0 < r ≤ λ₀ = 2^{-20}`

Sign of the first two derivatives of `Fpaper`, membership of `Mpaper`,
`Xpaper` in `(0,1)`, and existence of an admissible partner `Y` with the
dense-case slack, all by hand (explicit constant chains; no certificate).

The proof follows the paper's Lemma 5.3 with `λ₀ = 2^{-20}` instead of
`2^{-40}`; the constant chain has ample slack (final dense-case slack
`ψ(r) ≥ 0.135 r` instead of the paper's `0.1 r`).  All auxiliary bounds on
the region `0 < t ≤ 10^{-5}` (the paper's `T₀`), which covers both `r ≤ λ₀`
and the tangent witness `t₀ ≤ 2.79 λ₀`.

Numeric enclosures used (all certified by exact rational arithmetic):
`a₀ = e^{0.348694} ∈ [1.40678, 1.42836]` (via `(1 ± x/8)^{±8}`),
`e^{-D(r)} ∈ [1.4057 r, 1.4306 r]`, `M(r) ∈ [1.3525 r, 1.35251 r]`,
`v = -log X(r) ∈ [2.758 r, 2.785 r]`, `t₀ = v(1-1000v) ≥ 2.75 r`,
`log 2.75 ≥ 1.0115`, `log Q(r) ≥ 0.26`.
-/

namespace RamseyLean
namespace Bootstrap

open Set

/-! ### Elementary inequalities -/

private lemma one_sub_le_exp_neg (u : ℝ) : 1 - u ≤ Real.exp (-u) := by
  have := Real.add_one_le_exp (-u); linarith

private lemma exp_mul_one_sub_le (x : ℝ) : Real.exp x * (1 - x) ≤ 1 := by
  calc Real.exp x * (1 - x) ≤ Real.exp x * Real.exp (-x) :=
        mul_le_mul_of_nonneg_left (one_sub_le_exp_neg x) (Real.exp_nonneg x)
    _ = 1 := by rw [← Real.exp_add]; simp

private lemma exp_le_one_add_two_mul {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1/2) :
    Real.exp u ≤ 1 + 2*u := by
  have h := exp_mul_one_sub_le u
  have hpos : (0:ℝ) < 1 - u := by linarith
  nlinarith [Real.exp_pos u]

private lemma one_sub_inv_le_log {x : ℝ} (hx : 0 < x) : 1 - 1/x ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1/x by positivity)
  rw [one_div, Real.log_inv] at h
  have : (1:ℝ)/x = x⁻¹ := one_div x
  linarith

private lemma log_ge_two_sub_div {x : ℝ} (hx : 0 < x) :
    2 - Real.exp 1 / x ≤ Real.log x := by
  have h1 : Real.log (Real.exp 1 / x) ≤ Real.exp 1 / x - 1 :=
    Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos 1) hx)
  have h2 : Real.log (Real.exp 1 / x) = 1 - Real.log x := by
    rw [Real.log_div (Real.exp_ne_zero 1) (ne_of_gt hx), Real.log_exp]
  linarith

private lemma inv_one_sub_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1/2) :
    1/(1-u) ≤ 1 + 2*u := by
  have hpos : (0:ℝ) < 1 - u := by linarith
  rw [div_le_iff₀ hpos]; nlinarith

private lemma neg_log_one_sub_le {u : ℝ} (_h0 : 0 ≤ u) (h1 : u ≤ 1/2) :
    -Real.log (1-u) ≤ u + 2*u^2 := by
  have hpos : (0:ℝ) < 1 - u := by linarith
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1/(1-u) by positivity)
  rw [one_div, Real.log_inv] at h
  have h3 : (1-u)⁻¹ ≤ 1 + u + 2*u^2 := by
    rw [← one_div, div_le_iff₀ hpos]; nlinarith
  linarith

private lemma exp_neg_mul_le_of_abs_le {t x c : ℝ} (h0 : 0 ≤ t) (hx : |x| ≤ c) :
    -c ≤ Real.exp (-t) * x ∧ Real.exp (-t) * x ≤ c := by
  have hE1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have habs : |Real.exp (-t) * x| ≤ c := by
    rw [abs_mul, Real.abs_exp]
    calc Real.exp (-t) * |x| ≤ 1 * |x| :=
          mul_le_mul_of_nonneg_right hE1 (abs_nonneg x)
      _ = |x| := one_mul _
      _ ≤ c := hx
  exact ⟨(abs_le.mp habs).1, (abs_le.mp habs).2⟩

/-! ### Numeric bounds on `a₀ = e^{0.348694}` (via eighth powers) -/

private lemma a0_lb : (140678/100000 : ℝ) ≤ Real.exp (348694/1000000) := by
  have h8 : Real.exp (348694/1000000 : ℝ) = Real.exp (174347/4000000) ^ 8 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hx : (1 : ℝ) + 174347/4000000 ≤ Real.exp (174347/4000000) := by
    have := Real.add_one_le_exp (174347/4000000 : ℝ); linarith
  calc (140678/100000 : ℝ) ≤ ((1:ℝ) + 174347/4000000)^8 := by norm_num
    _ ≤ Real.exp (174347/4000000) ^ 8 :=
        pow_le_pow_left₀ (by norm_num) hx 8
    _ = Real.exp (348694/1000000) := h8.symm

private lemma a0_ub : Real.exp (348694/1000000 : ℝ) ≤ 142836/100000 := by
  have h8 : Real.exp (348694/1000000 : ℝ) = Real.exp (174347/4000000) ^ 8 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hx : Real.exp (174347/4000000 : ℝ) ≤ 4000000/3825653 := by
    have h := exp_mul_one_sub_le (174347/4000000 : ℝ)
    nlinarith [Real.exp_pos (174347/4000000 : ℝ)]
  calc Real.exp (348694/1000000 : ℝ) = Real.exp (174347/4000000) ^ 8 := h8
    _ ≤ ((4000000:ℝ)/3825653)^8 :=
        pow_le_pow_left₀ (Real.exp_nonneg _) hx 8
    _ ≤ 142836/100000 := by norm_num

/-! ### Polynomial coefficient bounds (paper (i): `A ≤ 145`, `B ≤ 788`, `B₂ ≤ 3699`) -/

private lemma Ppaper_bounds {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (-348694/1000000 : ℝ)*t - 145*t^2 ≤ Ppaper t ∧
      Ppaper t ≤ (-348694/1000000 : ℝ)*t + 145*t^2 := by
  have q3 : t^3 ≤ t^2 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  have q4 : t^4 ≤ t^2 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  have q5 : t^5 ≤ t^2 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  have q6 : t^6 ≤ t^2 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  have q7 : t^7 ≤ t^2 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  have q8 : t^8 ≤ t^2 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  have n3 : 0 ≤ t^3 := by positivity
  have n4 : 0 ≤ t^4 := by positivity
  have n5 : 0 ≤ t^5 := by positivity
  have n6 : 0 ≤ t^6 := by positivity
  have n7 : 0 ≤ t^7 := by positivity
  have n8 : 0 ≤ t^8 := by positivity
  unfold Ppaper
  constructor <;> nlinarith [q3, q4, q5, q6, q7, q8, n3, n4, n5, n6, n7, n8]

private lemma Ppaper'_bounds {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (-348694/1000000 : ℝ) - 788*t ≤ Ppaper' t ∧
      Ppaper' t ≤ (-348694/1000000 : ℝ) + 788*t := by
  have p2 : t^2 ≤ t := by
    simpa using pow_le_pow_of_le_one h0 h1 (by norm_num : 1 ≤ 2)
  have p3 : t^3 ≤ t := by
    simpa using pow_le_pow_of_le_one h0 h1 (by norm_num : 1 ≤ 3)
  have p4 : t^4 ≤ t := by
    simpa using pow_le_pow_of_le_one h0 h1 (by norm_num : 1 ≤ 4)
  have p5 : t^5 ≤ t := by
    simpa using pow_le_pow_of_le_one h0 h1 (by norm_num : 1 ≤ 5)
  have p6 : t^6 ≤ t := by
    simpa using pow_le_pow_of_le_one h0 h1 (by norm_num : 1 ≤ 6)
  have p7 : t^7 ≤ t := by
    simpa using pow_le_pow_of_le_one h0 h1 (by norm_num : 1 ≤ 7)
  have n2 : 0 ≤ t^2 := by positivity
  have n3 : 0 ≤ t^3 := by positivity
  have n4 : 0 ≤ t^4 := by positivity
  have n5 : 0 ≤ t^5 := by positivity
  have n6 : 0 ≤ t^6 := by positivity
  have n7 : 0 ≤ t^7 := by positivity
  unfold Ppaper'
  constructor <;> nlinarith [p2, p3, p4, p5, p6, p7, n2, n3, n4, n5, n6, n7]

private lemma Ppaper''_bounds {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (-3699 : ℝ) ≤ Ppaper'' t ∧ Ppaper'' t ≤ 3699 := by
  have p2 : t^2 ≤ t := by
    simpa using pow_le_pow_of_le_one h0 h1 (by norm_num : 1 ≤ 2)
  have p3 : t^3 ≤ t := by
    simpa using pow_le_pow_of_le_one h0 h1 (by norm_num : 1 ≤ 3)
  have p4 : t^4 ≤ t := by
    simpa using pow_le_pow_of_le_one h0 h1 (by norm_num : 1 ≤ 4)
  have p5 : t^5 ≤ t := by
    simpa using pow_le_pow_of_le_one h0 h1 (by norm_num : 1 ≤ 5)
  have p6 : t^6 ≤ t := by
    simpa using pow_le_pow_of_le_one h0 h1 (by norm_num : 1 ≤ 6)
  have n2 : 0 ≤ t^2 := by positivity
  have n3 : 0 ≤ t^3 := by positivity
  have n4 : 0 ≤ t^4 := by positivity
  have n5 : 0 ≤ t^5 := by positivity
  have n6 : 0 ≤ t^6 := by positivity
  unfold Ppaper''
  constructor <;> nlinarith [p2, p3, p4, p5, p6, n2, n3, n4, n5, n6, h0, h1]

private lemma Qpaper_bounds {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (1352506/1000000 : ℝ) - 345/100*t ≤ Qpaper t ∧
      Qpaper t ≤ (1352506/1000000 : ℝ) + 345/100*t := by
  have p2 : t^2 ≤ t := by
    simpa using pow_le_pow_of_le_one h0 h1 (by norm_num : 1 ≤ 2)
  have p3 : t^3 ≤ t := by
    simpa using pow_le_pow_of_le_one h0 h1 (by norm_num : 1 ≤ 3)
  have n2 : 0 ≤ t^2 := by positivity
  have n3 : 0 ≤ t^3 := by positivity
  unfold Qpaper
  constructor <;> nlinarith [p2, p3, n2, n3]

/-! ### The exponential-polynomial term `g'(t) - entropy'` bounds (paper (i)) -/

/-- `|e^{-t}(P'(t) - P(t)) - c₁| ≤ 789 t` on `0 < t ≤ 10^{-5}`. -/
private lemma gp_bounds {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1/100000) :
    (-348694/1000000 : ℝ) - 789*t ≤ Real.exp (-t) * (Ppaper' t - Ppaper t) ∧
      Real.exp (-t) * (Ppaper' t - Ppaper t) ≤ (-348694/1000000 : ℝ) + 789*t := by
  have ht1 : t ≤ 1 := le_trans h1 (by norm_num)
  obtain ⟨hPl, hPu⟩ := Ppaper_bounds h0.le ht1
  obtain ⟨hP'l, hP'u⟩ := Ppaper'_bounds h0.le ht1
  have hE1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hE2 : 1 - t ≤ Real.exp (-t) := one_sub_le_exp_neg t
  have ht2 : t^2 ≤ 1/100000 * t := by nlinarith
  have hu_neg : Ppaper' t - Ppaper t ≤ 0 := by nlinarith
  constructor
  · -- lower: e^{-t} u ≥ 1 * u  (u ≤ 0, e^{-t} ≤ 1)
    have h1' : 1 * (Ppaper' t - Ppaper t) ≤ Real.exp (-t) * (Ppaper' t - Ppaper t) :=
      mul_le_mul_of_nonpos_right hE1 hu_neg
    nlinarith
  · -- upper: e^{-t} u ≤ (1-t) u ≤ (1-t) u_hi
    have h2' : Real.exp (-t) * (Ppaper' t - Ppaper t) ≤
        (1 - t) * (Ppaper' t - Ppaper t) :=
      mul_le_mul_of_nonpos_right hE2 hu_neg
    have h3' : (1 - t) * (Ppaper' t - Ppaper t) ≤
        (1 - t) * ((-348694/1000000 : ℝ) + 788*t - (-348694/1000000)*t + 145*t^2) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      linarith
    nlinarith [mul_pos (mul_pos h0 h0) h0]

/-! ### Derivative bounds on `0 < t ≤ 10^{-5}` (paper (ii)) -/

/-- `Dpaper t ≥ 16 log 2 - 0.36 > 10` on `0 < t ≤ 10^{-5}`. -/
private lemma Dpaper_ge_two {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1/100000) :
    2 ≤ Dpaper t := by
  obtain ⟨hg, _⟩ := gp_bounds h0 h1
  have hlog1 : 0 ≤ Real.log (1+t) := Real.log_nonneg (by linarith)
  have hlogt : Real.log t ≤ Real.log (1/65536) := Real.log_le_log h0 (by linarith)
  have h65536 : Real.log (1/65536 : ℝ) = -(16 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (65536:ℝ) = 2^16 by norm_num, Real.log_pow]
    norm_num
  rw [h65536] at hlogt
  have hl2 := Real.log_two_gt_d9
  unfold Dpaper
  linarith

/-- `Dpaper t ≤ -log t + c₁ + 790 t` on `0 < t ≤ 10^{-5}`. -/
private lemma Dpaper_ub {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1/100000) :
    Dpaper t ≤ -Real.log t + (-348694/1000000) + 790*t := by
  obtain ⟨_, hg⟩ := gp_bounds h0 h1
  have hlog : Real.log (1+t) ≤ t := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1+t by linarith)
    linarith
  unfold Dpaper
  linarith

/-- `D2paper r < 0` on `0 < r ≤ λ₀`. -/
private lemma D2paper_neg {r : ℝ} (h0 : 0 < r) (h1 : r ≤ lam0) :
    D2paper r < 0 := by
  have hl : r ≤ 1/2^20 := by rw [lam0] at h1; exact h1
  have ht1 : r ≤ 1 := le_trans hl (by norm_num)
  obtain ⟨hPl, hPu⟩ := Ppaper_bounds h0.le ht1
  obtain ⟨hP'l, hP'u⟩ := Ppaper'_bounds h0.le ht1
  obtain ⟨hP''l, hP''u⟩ := Ppaper''_bounds h0.le ht1
  have habs : |Ppaper'' r - 2 * Ppaper' r + Ppaper r| ≤ 3701 := by
    rw [abs_le]
    constructor <;> nlinarith
  obtain ⟨_, hEw⟩ := exp_neg_mul_le_of_abs_le h0.le habs
  have hden_pos : (0:ℝ) < r * (1+r) := by positivity
  have hden_ub : r * (1+r) ≤ 1/524288 := by nlinarith
  have hfrac : (524288 : ℝ) ≤ 1/(r*(1+r)) := by
    calc (524288 : ℝ) = 1/(1/524288) := by norm_num
      _ ≤ 1/(r*(1+r)) := one_div_le_one_div_of_le hden_pos hden_ub
  unfold D2paper
  linarith

/-! ### Goal 1: the derivative sign facts -/

/-- Derivative sign facts on the small-λ region. -/
theorem smallLambda_derivFacts :
    ∀ r ∈ Ioc (0 : ℝ) lam0, 0 < Dpaper r ∧ D2paper r < 0 := by
  rintro r ⟨hr0, hr1⟩
  have hr5 : r ≤ 1/100000 := by
    rw [lam0] at hr1; norm_num at hr1 ⊢; linarith
  exact ⟨lt_of_lt_of_le (by norm_num) (Dpaper_ge_two hr0 hr5), D2paper_neg hr0 hr1⟩

/-! ### Helpers for the ladder facts -/

/-- The tangent defect `F(t) - t F'(t)` in closed form (pure algebra, no
integration): the entropy parts collapse to `log(1+t)`. -/
private lemma F_sub_mul_D (t : ℝ) :
    Fpaper t - t * Dpaper t =
      Real.log (1+t) + Real.exp (-t) * ((1+t) * Ppaper t - t * Ppaper' t) := by
  unfold Fpaper Dpaper entropy
  ring

/-- Paper (iv): `F(t) - t F'(t) ≤ t + 934 t²` on `0 < t ≤ 10^{-5}`. -/
private lemma defect_le {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1/100000) :
    Fpaper t - t * Dpaper t ≤ t + 934*t^2 := by
  rw [F_sub_mul_D]
  have ht1 : t ≤ 1 := le_trans h1 (by norm_num)
  obtain ⟨hPl, hPu⟩ := Ppaper_bounds h0.le ht1
  obtain ⟨hP'l, hP'u⟩ := Ppaper'_bounds h0.le ht1
  have hlog : Real.log (1+t) ≤ t := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1+t by linarith)
    linarith
  have habs : |(1+t) * Ppaper t - t * Ppaper' t| ≤ 934*t^2 := by
    have e1 : (1+t) * Ppaper t ≤ (1+t) * ((-348694/1000000 : ℝ)*t + 145*t^2) :=
      mul_le_mul_of_nonneg_left hPu (by linarith)
    have e2 : (1+t) * ((-348694/1000000 : ℝ)*t - 145*t^2) ≤ (1+t) * Ppaper t :=
      mul_le_mul_of_nonneg_left hPl (by linarith)
    have e3 : t * Ppaper' t ≤ t * ((-348694/1000000 : ℝ) + 788*t) :=
      mul_le_mul_of_nonneg_left hP'u h0.le
    have e4 : t * ((-348694/1000000 : ℝ) - 788*t) ≤ t * Ppaper' t :=
      mul_le_mul_of_nonneg_left hP'l h0.le
    rw [abs_le]
    constructor <;> nlinarith [mul_pos (mul_pos h0 h0) h0]
  obtain ⟨_, h⟩ := exp_neg_mul_le_of_abs_le h0.le habs
  linarith

/-- `log 2.75 ≥ 1.0115` (via `log x ≥ 2 - e/x` and `e < 2.7182818286`). -/
private lemma log_275_lb : (10115/10000 : ℝ) ≤ Real.log (275/100) := by
  have h := log_ge_two_sub_div (show (0:ℝ) < 275/100 by norm_num)
  have he := Real.exp_one_lt_d9
  have h2 : Real.exp 1 / (275/100 : ℝ) = Real.exp 1 * (100/275) := by ring
  have h3 : Real.exp 1 * (100/275 : ℝ) ≤ 2.7182818286 * (100/275) :=
    mul_le_mul_of_nonneg_right he.le (by norm_num)
  rw [h2] at h
  norm_num at h3 ⊢
  linarith

/-- Enclosure `1.3525 r ≤ M(r) ≤ 1.35251 r` on `0 < r ≤ λ₀`. -/
private lemma Mpaper_bounds {r : ℝ} (h0 : 0 < r) (h1 : r ≤ lam0) :
    (13525/10000 : ℝ) * r ≤ Mpaper r ∧ Mpaper r ≤ (135251/100000 : ℝ) * r := by
  have hl : r ≤ 1/2^20 := by rw [lam0] at h1; exact h1
  have ht1 : r ≤ 1 := le_trans hl (by norm_num)
  obtain ⟨hQl, hQu⟩ := Qpaper_bounds h0.le ht1
  have hE1 : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hE2 : 1 - r ≤ Real.exp (-r) := one_sub_le_exp_neg r
  have hE0 : (0:ℝ) < Real.exp (-r) := Real.exp_pos _
  have hQpos : (0:ℝ) < Qpaper r := by nlinarith
  constructor
  · have s1 : (1 - r) * ((1352506/1000000 : ℝ) - 345/100*r) ≤
        Real.exp (-r) * Qpaper r :=
      mul_le_mul hE2 hQl (by nlinarith) hE0.le
    have s2 : (13525/10000 : ℝ) ≤ (1 - r) * ((1352506/1000000 : ℝ) - 345/100*r) := by
      nlinarith
    calc (13525/10000 : ℝ) * r = r * (13525/10000) := by ring
      _ ≤ r * (Real.exp (-r) * Qpaper r) :=
          mul_le_mul_of_nonneg_left (le_trans s2 s1) h0.le
      _ = Mpaper r := by unfold Mpaper; ring
  · have s1 : Real.exp (-r) * Qpaper r ≤ 1 * ((1352506/1000000 : ℝ) + 345/100*r) :=
      mul_le_mul hE1 hQu hQpos.le (by norm_num)
    have s2 : (1:ℝ) * ((1352506/1000000 : ℝ) + 345/100*r) ≤ 135251/100000 := by
      nlinarith
    calc Mpaper r = r * (Real.exp (-r) * Qpaper r) := by unfold Mpaper; ring
      _ ≤ r * (135251/100000) :=
          mul_le_mul_of_nonneg_left (le_trans s1 s2) h0.le
      _ = (135251/100000 : ℝ) * r := by ring

/-- Paper (v), first term: `F(r) ≥ -r log r + (1+c₁) r - 146 r²` on `0 < r ≤ λ₀`. -/
private lemma Fpaper_lb {r : ℝ} (h0 : 0 < r) (h1 : r ≤ lam0) :
    -(r * Real.log r) + (651306/1000000 : ℝ) * r - 146*r^2 ≤ Fpaper r := by
  have hl : r ≤ 1/2^20 := by rw [lam0] at h1; exact h1
  have ht1 : r ≤ 1 := le_trans hl (by norm_num)
  obtain ⟨hPl, _⟩ := Ppaper_bounds h0.le ht1
  have hE1 : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hE0 : (0:ℝ) < Real.exp (-r) := Real.exp_pos _
  -- entropy r ≥ r - r log r
  have hent : r - r * Real.log r ≤ entropy r := by
    have hlg : 1 - 1/(1+r) ≤ Real.log (1+r) := one_sub_inv_le_log (by linarith)
    have h3 : (1+r) * (1 - 1/(1+r)) ≤ (1+r) * Real.log (1+r) :=
      mul_le_mul_of_nonneg_left hlg (by linarith)
    have h4 : (1+r) * (1 - 1/(1+r)) = r := by
      field_simp
      ring
    unfold entropy; linarith
  -- e^{-r} P(r) ≥ c₁ r - 146 r²
  have hcor : (-348694/1000000 : ℝ)*r - 146*r^2 ≤ Real.exp (-r) * Ppaper r := by
    have hb : (-348694/1000000 : ℝ)*r - 145*r^2 ≤ 0 := by nlinarith
    have s1 : Real.exp (-r) * ((-348694/1000000 : ℝ)*r - 145*r^2) ≤
        Real.exp (-r) * Ppaper r := mul_le_mul_of_nonneg_left hPl hE0.le
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ -((-348694/1000000 : ℝ)*r - 145*r^2))
      (by linarith : (0:ℝ) ≤ 1 - Real.exp (-r))]
  unfold Fpaper
  linarith

/-! ### Goal 2: the ladder facts -/

set_option maxHeartbeats 1600000 in
/-- The pointwise ladder facts on the small-λ region. -/
theorem smallLambda_ladderFacts (hT : TangentUB) (hMono : MonoUB) :
    ∀ r ∈ Ioc (0 : ℝ) lam0, LadderFactsAt r := by
  rintro r ⟨hr0, hrl⟩
  have hl : r ≤ 1/2^20 := by rw [lam0] at hrl; exact hrl
  have hr1 : r ≤ 1 := le_trans hl (by norm_num)
  have hr5 : r ≤ 1/100000 := le_trans hl (by norm_num)
  have h1r : (0:ℝ) < 1 + r := by linarith
  -- M enclosure and membership
  obtain ⟨hM_lb, hM_ub⟩ := Mpaper_bounds hr0 hrl
  have hM0 : 0 < Mpaper r := lt_of_lt_of_le (by positivity) hM_lb
  have hM1 : Mpaper r < 1 := by nlinarith
  have hM : Mpaper r ∈ Ioo (0:ℝ) 1 := ⟨hM0, hM1⟩
  -- derivative positivity, X membership
  have hD : 0 < Dpaper r := lt_of_lt_of_le (by norm_num) (Dpaper_ge_two hr0 hr5)
  have hX : Xpaper r ∈ Ioo (0:ℝ) 1 := Xpaper_mem_Ioo hD hM
  unfold LadderFactsAt
  -- q = e^{-D(r)} enclosure (paper (iii))
  obtain ⟨hgl, hgu⟩ := gp_bounds hr0 hr5
  have hq_eq : Real.exp (-Dpaper r) =
      r / (1+r) * Real.exp (-(Real.exp (-r) * (Ppaper' r - Ppaper r))) := by
    have hDeq : -Dpaper r =
        Real.log r - Real.log (1+r) + -(Real.exp (-r) * (Ppaper' r - Ppaper r)) := by
      unfold Dpaper; ring
    rw [hDeq, Real.exp_add, Real.exp_sub, Real.exp_log hr0, Real.exp_log h1r]
  have hexpG_ub : Real.exp (-(Real.exp (-r) * (Ppaper' r - Ppaper r))) ≤
      142836/100000 * (1 + 1578*r) := by
    have h1 : Real.exp (-(Real.exp (-r) * (Ppaper' r - Ppaper r))) ≤
        Real.exp (348694/1000000 + 789*r) := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_add] at h1
    have h2 : Real.exp (789*r) ≤ 1 + 2*(789*r) :=
      exp_le_one_add_two_mul (by positivity) (by nlinarith)
    have h3 : Real.exp (348694/1000000 : ℝ) * Real.exp (789*r) ≤
        (142836/100000) * (1 + 2*(789*r)) :=
      mul_le_mul a0_ub h2 (Real.exp_nonneg _) (by norm_num)
    nlinarith [h1, h3]
  have hexpG_lb : (140678/100000 : ℝ) * (1 - 789*r) ≤
      Real.exp (-(Real.exp (-r) * (Ppaper' r - Ppaper r))) := by
    have h1 : Real.exp (348694/1000000 + -(789*r)) ≤
        Real.exp (-(Real.exp (-r) * (Ppaper' r - Ppaper r))) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_add] at h1
    have h2 : 1 - 789*r ≤ Real.exp (-(789*r)) := one_sub_le_exp_neg (789*r)
    have h3 : (140678/100000 : ℝ) * (1 - 789*r) ≤
        Real.exp (348694/1000000 : ℝ) * Real.exp (-(789*r)) :=
      mul_le_mul a0_lb h2 (by nlinarith) (Real.exp_nonneg _)
    linarith
  have hq_ub : Real.exp (-Dpaper r) ≤ 14306/10000 * r := by
    rw [hq_eq]
    have hfr : r/(1+r) ≤ r := by
      rw [div_le_iff₀ h1r]; nlinarith
    have h4 : r/(1+r) * Real.exp (-(Real.exp (-r) * (Ppaper' r - Ppaper r))) ≤
        r * (142836/100000 * (1 + 1578*r)) :=
      mul_le_mul hfr hexpG_ub (Real.exp_nonneg _) hr0.le
    nlinarith [mul_le_mul_of_nonneg_left hl hr0.le]
  have hq_lb : (14057/10000 : ℝ) * r ≤ Real.exp (-Dpaper r) := by
    rw [hq_eq]
    have hfr : r*(1-r) ≤ r/(1+r) := by
      rw [le_div_iff₀ h1r]; nlinarith [mul_pos (mul_pos hr0 hr0) hr0]
    have h4 : (r*(1-r)) * ((140678/100000 : ℝ) * (1 - 789*r)) ≤
        r/(1+r) * Real.exp (-(Real.exp (-r) * (Ppaper' r - Ppaper r))) :=
      mul_le_mul hfr hexpG_lb (by nlinarith) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hl hr0.le,
      mul_pos (mul_pos hr0 hr0) hr0]
  have hq_pos : 0 < Real.exp (-Dpaper r) := Real.exp_pos _
  have hq_half : Real.exp (-Dpaper r) ≤ 1/2 := by nlinarith
  have hm_half : Mpaper r ≤ 1/2 := by nlinarith
  -- v = -log X enclosure (paper (iii))
  have hlogX := log_Xpaper hD hM
  have h1q : (0:ℝ) < 1 - Real.exp (-Dpaper r) := by nlinarith
  have h1m : (0:ℝ) < 1 - Mpaper r := by linarith
  have hA : Real.log (1 - Real.exp (-Dpaper r)) ≤ -(Real.exp (-Dpaper r)) := by
    have := Real.log_le_sub_one_of_pos h1q; linarith
  have hB : Real.log (1 - Mpaper r) ≤ -(Mpaper r) := by
    have := Real.log_le_sub_one_of_pos h1m; linarith
  have hv_lb : (2758/1000 : ℝ) * r ≤ -Real.log (Xpaper r) := by
    have hAneg : Real.log (1 - Real.exp (-Dpaper r)) ≤ 0 := by linarith
    have hd1 : Real.log (1 - Real.exp (-Dpaper r)) / (1 - Mpaper r) ≤
        Real.log (1 - Real.exp (-Dpaper r)) := by
      rw [div_le_iff₀ h1m]
      nlinarith [mul_nonneg (neg_nonneg.mpr hAneg) hM0.le]
    rw [hlogX]
    nlinarith [hq_lb, hM_lb]
  have hv_ub : -Real.log (Xpaper r) ≤ (2785/1000 : ℝ) * r := by
    have hnA := neg_log_one_sub_le hq_pos.le hq_half
    have hnB := neg_log_one_sub_le hM0.le hm_half
    have hinv := inv_one_sub_le hM0.le hm_half
    have hd : -(Real.log (1 - Real.exp (-Dpaper r)) / (1 - Mpaper r)) ≤
        (Real.exp (-Dpaper r) + 2*(Real.exp (-Dpaper r))^2) * (1 + 2*Mpaper r) := by
      have e1 : -(Real.log (1 - Real.exp (-Dpaper r)) / (1 - Mpaper r)) =
          (-Real.log (1 - Real.exp (-Dpaper r))) * (1/(1 - Mpaper r)) := by
        field_simp
      rw [e1]
      have e2 : (-Real.log (1 - Real.exp (-Dpaper r))) * (1/(1 - Mpaper r)) ≤
          (Real.exp (-Dpaper r) + 2*(Real.exp (-Dpaper r))^2) * (1/(1 - Mpaper r)) :=
        mul_le_mul_of_nonneg_right hnA (by positivity)
      have e3 : (Real.exp (-Dpaper r) + 2*(Real.exp (-Dpaper r))^2) * (1/(1 - Mpaper r)) ≤
          (Real.exp (-Dpaper r) + 2*(Real.exp (-Dpaper r))^2) * (1 + 2*Mpaper r) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      linarith
    have c1 : Real.exp (-Dpaper r) + 2*(Real.exp (-Dpaper r))^2 ≤ 14307/10000 * r := by
      nlinarith [mul_le_mul hq_ub hq_ub hq_pos.le (by positivity :
          (0:ℝ) ≤ 14306/10000*r),
        mul_le_mul_of_nonneg_left hl hr0.le]
    have c2 : 1 + 2*Mpaper r ≤ 1 + 3/1000000 := by nlinarith
    have c3 : (Real.exp (-Dpaper r) + 2*(Real.exp (-Dpaper r))^2) * (1 + 2*Mpaper r) ≤
        (14307/10000 * r) * (1 + 3/1000000) :=
      mul_le_mul c1 c2 (by positivity) (by positivity)
    have c4 : Mpaper r + 2*(Mpaper r)^2 ≤ 135253/100000 * r := by
      nlinarith [mul_le_mul hM_ub hM_ub hM0.le (by positivity :
          (0:ℝ) ≤ 135251/100000*r),
        mul_le_mul_of_nonneg_left hl hr0.le]
    rw [hlogX]
    nlinarith [hd, hnB, c3, c4, hr0]
  -- abbreviate v
  set v : ℝ := -Real.log (Xpaper r) with hv_def
  have hlogX_neg : Real.log (Xpaper r) = -v := by rw [hv_def]; ring
  have hv_pos : 0 < v := by
    rw [hv_def]
    have := Real.log_neg hX.1 hX.2
    linarith
  have hvlam : v ≤ 2785/1000 * (1/2^20) := by nlinarith
  have hv3 : v ≤ 3/1000000 := by
    have : (2785/1000 : ℝ) * (1/2^20) ≤ 3/1000000 := by norm_num
    linarith
  -- the tangent witness t₀ = v(1 - 1000 v)
  set t0 : ℝ := v * (1 - 1000*v) with ht0_def
  have h1000v : 1000*v ≤ 3/1000 := by linarith
  have ht0_pos : 0 < t0 := by
    rw [ht0_def]; apply mul_pos hv_pos; linarith
  have ht0_le_v : t0 ≤ v := by rw [ht0_def]; nlinarith
  have ht0_le5 : t0 ≤ 1/100000 := by linarith
  have ht0_le1 : t0 ≤ 1 := by linarith
  have ht0_lb : (275/100 : ℝ) * r ≤ t0 := by
    rw [ht0_def]
    nlinarith [hv_lb, hv_ub, hv_pos, mul_le_mul_of_nonneg_left hvlam hv_pos.le]
  have ht0_mem : t0 ∈ Ioc (0:ℝ) 1 := ⟨ht0_pos, ht0_le1⟩
  -- the witness derivative S̄ = F'(t₀)
  have hS2 : 2 ≤ Dpaper t0 := Dpaper_ge_two ht0_pos ht0_le5
  have hS_ub : Dpaper t0 ≤
      -Real.log r + (-348694/1000000 : ℝ) - 10115/10000 + 2201*r := by
    have h1 := Dpaper_ub ht0_pos ht0_le5
    have h2 : Real.log (275/100 * r) ≤ Real.log t0 :=
      Real.log_le_log (by positivity) ht0_lb
    have h3 : Real.log (275/100 * r) = Real.log (275/100) + Real.log r :=
      Real.log_mul (by norm_num) (ne_of_gt hr0)
    have h4 := log_275_lb
    have h5 : t0 ≤ 2785/1000 * r := le_trans ht0_le_v hv_ub
    linarith
  have hY : Real.exp (-Dpaper t0) ∈ Ioo (0:ℝ) 1 :=
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith)⟩
  -- the tangent defect is at most v (paper (iv))
  have hdef : Fpaper t0 - t0 * Dpaper t0 ≤ v := by
    have h1 := defect_le ht0_pos ht0_le5
    have h2a : (1 - 1000*v)^2 ≤ 1 := by nlinarith
    have h2 : t0 + 934*t0^2 ≤ v := by
      rw [ht0_def]
      nlinarith [sq_nonneg v, mul_nonneg (sq_nonneg v) (sq_nonneg (1 - 1000*v))]
    linarith
  -- log M ≥ log r - r + 0.26 (paper (v))
  have hQl : (1352506/1000000 : ℝ) - 345/100*r ≤ Qpaper r := (Qpaper_bounds hr0.le hr1).1
  have hQpos : (0:ℝ) < Qpaper r := by nlinarith
  have hlogM_eq : Real.log (Mpaper r) = Real.log r + -r + Real.log (Qpaper r) := by
    unfold Mpaper
    rw [Real.log_mul (mul_ne_zero (ne_of_gt hr0) (Real.exp_ne_zero _)) (ne_of_gt hQpos),
      Real.log_mul (ne_of_gt hr0) (Real.exp_ne_zero _), Real.log_exp]
  have hlogQ : (26/100 : ℝ) ≤ Real.log (Qpaper r) := by
    have h1 : 1 - 1/(Qpaper r) ≤ Real.log (Qpaper r) := one_sub_inv_le_log hQpos
    have h2 : (13525/10000 : ℝ) ≤ Qpaper r := by nlinarith
    have h3 : 1/(Qpaper r) ≤ 1/(13525/10000 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) h2
    have h4 : (1:ℝ)/(13525/10000 : ℝ) ≤ 74/100 := by norm_num
    linarith
  -- assemble
  refine ⟨hM, hX, Real.exp (-Dpaper t0), hY, ?_, ?_, ?_⟩
  · -- admissibility 1: F s ≤ v + s S̄ via the tangent line at t₀
    intro s hs
    have htang := hT t0 ht0_mem s hs
    rw [Real.log_exp]
    linarith [htang, hdef]
  · -- admissibility 2: F s ≤ F 1 ≤ 7/5 ≤ 2 ≤ S̄ + s v
    intro s hs
    have h1 := hMono s hs
    have h2 := Fpaper_one_le
    rw [Real.log_exp, hlogX_neg]
    have hsv : 0 ≤ s * v := mul_nonneg hs.1.le hv_pos.le
    linarith
  · -- dense-case slack (paper (v)): everything is linear in
    -- {r, r², r log r, v, r log M, r S̄} after multiplying by r
    simp only [denseCaseExponent]
    rw [Real.log_exp, hlogX_neg]
    have hFlb := Fpaper_lb hr0 hrl
    have hrlogM : r * (Real.log r + -r + 26/100) ≤ r * Real.log (Mpaper r) := by
      apply mul_le_mul_of_nonneg_left _ hr0.le
      rw [hlogM_eq]; linarith
    have hrS : r * Dpaper t0 ≤
        r * (-Real.log r + (-348694/1000000 : ℝ) - 10115/10000 + 2201*r) :=
      mul_le_mul_of_nonneg_left hS_ub hr0.le
    have hr2 : r^2 ≤ (1/2^20) * r := by nlinarith
    nlinarith [hFlb, hv_ub, hrlogM, hrS, hr2, hr0]

end Bootstrap
end RamseyLean

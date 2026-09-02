import RamseyLean.Descent
import RamseyLean.AsymptoticRegion
import RamseyLean.Asymptotics.Uniform
import Mathlib.Tactic

/-!
# The self-consistent bootstrap (shift ladder)

`uniformRamseyExpBound_of_descent` (paper Theorem 14 of Gupta–Ndiaye–Norin–Wei) turns
an *already established* asymptotic region into a new uniform exponential Ramsey bound.
Here we show that the bound `F` being proved may itself define the admissible pair
`(X r, Y r)`: it suffices that `(X r, Y r)` is `F`-admissible in both orientations,

  `F s ≤ -log (X r) - s * log (Y r)`  and  `F s ≤ -log (Y r) - s * log (X r)`   (`0 < s ≤ 1`),

together with the strict slack inequality of the descent theorem.

The proof is a ladder.  For `σ ≥ 0` let `Fσ r = F r + σ * (1 + r)`, `Xσ = X e^{-σ}`,
`Yσ = Y e^{-σ}`.  The pair `(Xσ, Yσ)` is `Fσ`-admissible whenever `(X, Y)` is
`F`-admissible, and the dense-case exponent of `(Xσ, M, Yσ)` is that of `(X, M, Y)` plus
`σ (1 + r) / 2`.  Hence, if `Fσ` is a valid bound, the descent theorem applied to the
function `F_{σ/2}` with the pair `(Xσ, Yσ)` shows that `F_{σ/2}` is valid.  Starting from
`σ₀ = log 4` (Erdős–Szekeres) and halving, every `F_{σ₀ / 2^j}` is valid, and `F` follows.

The relaxed hypothesis `X r ≤ (1 - e^{-D r})^{1/(1-M r)} (1 - M r)` of
`uniformRamseyExpBound_of_descent` is what makes the shift of `X` harmless.
-/

namespace RamseyLean

open Filter Set Topology

/-- The constant function `log 4` is a valid uniform exponential bound
(Erdős–Szekeres with `x = 1/2`). -/
theorem uniformRamseyExpBound_log_four :
    UniformRamseyExpBound (fun _ : ℝ => Real.log 4) := by
  apply uniformRamseyExpBound_of_exact
  intro k ℓ hℓ hℓk
  have hk : 0 < k := hℓ.trans_le hℓk
  have hES := ramseyBound_erdosSzekeres (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hk hℓ
  have h2 : ((1 / 2 : ℝ)⁻¹) ^ (k - 1) * ((1 - (1 / 2 : ℝ))⁻¹) ^ (ℓ - 1) ≤ (4 : ℝ) ^ k := by
    have e1 : ((1 / 2 : ℝ)⁻¹) = 2 := by norm_num
    have e2 : ((1 - (1 / 2 : ℝ))⁻¹) = 2 := by norm_num
    rw [e1, e2, ← pow_add]
    have hpow : (2 : ℝ) ^ (k - 1 + (ℓ - 1)) ≤ (2 : ℝ) ^ (2 * k) := by
      apply pow_le_pow_right₀ (by norm_num)
      omega
    calc (2 : ℝ) ^ (k - 1 + (ℓ - 1)) ≤ (2 : ℝ) ^ (2 * k) := hpow
      _ = (4 : ℝ) ^ k := by rw [pow_mul]; norm_num
  calc (ramseyNumber k ℓ : ℝ) ≤ _ := hES
    _ ≤ (4 : ℝ) ^ k := h2
    _ = Real.exp (Real.log 4 * (k : ℝ)) := by
      rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- The shifted rate function `F_σ(r) = F(r) + σ (1 + r)`. -/
noncomputable def shiftRate (F : ℝ → ℝ) (σ : ℝ) : ℝ → ℝ := fun r => F r + σ * (1 + r)

/-- One rung of the ladder: if `F_σ` is valid then so is `F_{σ/2}`. -/
theorem shiftRate_half_of_shiftRate
    {F D M X Y : ℝ → ℝ}
    (hderiv : ∀ r ∈ Ioc (0 : ℝ) 1, HasDerivAt F (D r) r)
    (hDcont : ContinuousOn D (Ioc (0 : ℝ) 1))
    (hMcont : ContinuousOn M (Ioc (0 : ℝ) 1))
    (hFnonneg : ∀ r ∈ Ioc (0 : ℝ) 1, 0 ≤ F r)
    (hDpos : ∀ r ∈ Ioc (0 : ℝ) 1, 0 < D r)
    (hM : ∀ r ∈ Ioc (0 : ℝ) 1, M r ∈ Ioo (0 : ℝ) 1)
    (hX : ∀ r ∈ Ioc (0 : ℝ) 1, X r ∈ Ioo (0 : ℝ) 1)
    (hY : ∀ r ∈ Ioc (0 : ℝ) 1, Y r ∈ Ioo (0 : ℝ) 1)
    (hXle : ∀ r ∈ Ioc (0 : ℝ) 1,
      X r ≤ (1 - Real.exp (-D r)) ^ (1 / (1 - M r)) * (1 - M r))
    (hadm₁ : ∀ r ∈ Ioc (0 : ℝ) 1, ∀ s ∈ Ioc (0 : ℝ) 1,
      F s ≤ -Real.log (X r) - s * Real.log (Y r))
    (hadm₂ : ∀ r ∈ Ioc (0 : ℝ) 1, ∀ s ∈ Ioc (0 : ℝ) 1,
      F s ≤ -Real.log (Y r) - s * Real.log (X r))
    (hslack : ∀ r ∈ Ioc (0 : ℝ) 1,
      denseCaseExponent (X r) (M r) (Y r) r < F r)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hvalid : UniformRamseyExpBound (shiftRate F σ)) :
    UniformRamseyExpBound (shiftRate F (σ / 2)) := by
  -- the shifted pair
  set e : ℝ := Real.exp (-σ) with he
  have hepos : 0 < e := Real.exp_pos _
  have hele : e ≤ 1 := by
    rw [he]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hloge : Real.log e = -σ := by rw [he, Real.log_exp]
  let Xσ : ℝ → ℝ := fun r => X r * e
  let Yσ : ℝ → ℝ := fun r => Y r * e
  have hXσ : ∀ r ∈ Ioc (0 : ℝ) 1, Xσ r ∈ Ioo (0 : ℝ) 1 := by
    intro r hr
    exact ⟨mul_pos (hX r hr).1 hepos,
      (mul_le_of_le_one_right (hX r hr).1.le hele).trans_lt (hX r hr).2⟩
  have hYσ : ∀ r ∈ Ioc (0 : ℝ) 1, Yσ r ∈ Ioo (0 : ℝ) 1 := by
    intro r hr
    exact ⟨mul_pos (hY r hr).1 hepos,
      (mul_le_of_le_one_right (hY r hr).1.le hele).trans_lt (hY r hr).2⟩
  have hlogXσ : ∀ r ∈ Ioc (0 : ℝ) 1, Real.log (Xσ r) = Real.log (X r) - σ := by
    intro r hr
    simp only [Xσ]
    rw [Real.log_mul (hX r hr).1.ne' hepos.ne', hloge]
    ring
  have hlogYσ : ∀ r ∈ Ioc (0 : ℝ) 1, Real.log (Yσ r) = Real.log (Y r) - σ := by
    intro r hr
    simp only [Yσ]
    rw [Real.log_mul (hY r hr).1.ne' hepos.ne', hloge]
    ring
  -- the shifted pair lies in the asymptotic region, by validity of `F_σ`
  have hregion : ∀ r ∈ Ioc (0 : ℝ) 1, (Xσ r, Yσ r) ∈ asymptoticRegion := by
    intro r hr
    apply mem_asymptoticRegion_of_uniform_bound (hXσ r hr) (hYσ r hr) hvalid
    · intro s hs
      rw [hlogXσ r hr, hlogYσ r hr]
      have := hadm₁ r hr s hs
      simp only [shiftRate]
      nlinarith [hs.1.le]
    · intro s hs
      rw [hlogXσ r hr, hlogYσ r hr]
      have := hadm₂ r hr s hs
      simp only [shiftRate]
      nlinarith [hs.1.le]
  -- apply the descent theorem to `F_{σ/2}` with derivative `D + σ/2`
  apply uniformRamseyExpBound_of_descent
    (F := shiftRate F (σ / 2)) (D := fun r => D r + σ / 2) (M := M) (X := Xσ) (Y := Yσ)
  · intro r hr
    have h1 : HasDerivAt (fun r : ℝ => σ / 2 * (1 + r)) (σ / 2) r := by
      simpa using ((hasDerivAt_id r).const_add 1).const_mul (σ / 2)
    have h2 := (hderiv r hr).add h1
    have hfun : (fun r => F r + σ / 2 * (1 + r)) = shiftRate F (σ / 2) := rfl
    exact hfun ▸ h2
  · exact hDcont.add continuousOn_const
  · exact hMcont
  · intro r hr
    simp only [shiftRate]
    nlinarith [hFnonneg r hr, hr.1.le]
  · intro r hr
    linarith [hDpos r hr]
  · exact hM
  · exact hXσ
  · exact hYσ
  · intro r hr
    -- `X e^{-σ} ≤ X ≤ formula(D) ≤ formula(D + σ/2)`
    have hM' := hM r hr
    have hexp : Real.exp (-(D r + σ / 2)) ≤ Real.exp (-D r) :=
      Real.exp_le_exp.mpr (by linarith)
    have hbase : 1 - Real.exp (-D r) ≤ 1 - Real.exp (-(D r + σ / 2)) := by linarith
    have hbasepos : 0 ≤ 1 - Real.exp (-D r) := by
      have : Real.exp (-D r) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hDpos r hr])
      linarith
    have hexpo : 0 ≤ 1 / (1 - M r) := by
      have : 0 < 1 - M r := by linarith [hM'.2]
      positivity
    have hmono := Real.rpow_le_rpow hbasepos hbase hexpo
    calc Xσ r = X r * e := rfl
      _ ≤ X r := mul_le_of_le_one_right (hX r hr).1.le hele
      _ ≤ (1 - Real.exp (-D r)) ^ (1 / (1 - M r)) * (1 - M r) := hXle r hr
      _ ≤ (1 - Real.exp (-(D r + σ / 2))) ^ (1 / (1 - M r)) * (1 - M r) := by
        apply mul_le_mul_of_nonneg_right hmono
        linarith [hM'.2]
  · exact hregion
  · intro r hr
    have hs := hslack r hr
    have hexp : denseCaseExponent (Xσ r) (M r) (Yσ r) r =
        denseCaseExponent (X r) (M r) (Y r) r + σ * (1 + r) / 2 := by
      simp only [denseCaseExponent]
      rw [hlogXσ r hr, hlogYσ r hr]
      ring
    rw [hexp]
    simp only [shiftRate]
    linarith

/-- Paper Theorem 4.2 (self-consistent bootstrap): the bound being proved may define
its own admissible pair.  All hypotheses are those of `uniformRamseyExpBound_of_descent`
except that region membership is replaced by `F`-admissibility of `(X r, Y r)` in both
orientations. -/
theorem uniformRamseyExpBound_selfConsistent
    {F D M X Y : ℝ → ℝ}
    (hderiv : ∀ r ∈ Ioc (0 : ℝ) 1, HasDerivAt F (D r) r)
    (hDcont : ContinuousOn D (Ioc (0 : ℝ) 1))
    (hMcont : ContinuousOn M (Ioc (0 : ℝ) 1))
    (hFnonneg : ∀ r ∈ Ioc (0 : ℝ) 1, 0 ≤ F r)
    (hDpos : ∀ r ∈ Ioc (0 : ℝ) 1, 0 < D r)
    (hM : ∀ r ∈ Ioc (0 : ℝ) 1, M r ∈ Ioo (0 : ℝ) 1)
    (hX : ∀ r ∈ Ioc (0 : ℝ) 1, X r ∈ Ioo (0 : ℝ) 1)
    (hY : ∀ r ∈ Ioc (0 : ℝ) 1, Y r ∈ Ioo (0 : ℝ) 1)
    (hXle : ∀ r ∈ Ioc (0 : ℝ) 1,
      X r ≤ (1 - Real.exp (-D r)) ^ (1 / (1 - M r)) * (1 - M r))
    (hadm₁ : ∀ r ∈ Ioc (0 : ℝ) 1, ∀ s ∈ Ioc (0 : ℝ) 1,
      F s ≤ -Real.log (X r) - s * Real.log (Y r))
    (hadm₂ : ∀ r ∈ Ioc (0 : ℝ) 1, ∀ s ∈ Ioc (0 : ℝ) 1,
      F s ≤ -Real.log (Y r) - s * Real.log (X r))
    (hslack : ∀ r ∈ Ioc (0 : ℝ) 1,
      denseCaseExponent (X r) (M r) (Y r) r < F r) :
    UniformRamseyExpBound F := by
  -- every rung `F + (log 4 / 2^j)(1 + r)` is valid
  have hrung : ∀ j : ℕ, UniformRamseyExpBound (shiftRate F (Real.log 4 / 2 ^ j)) := by
    intro j
    induction j with
    | zero =>
      simp only [pow_zero, div_one]
      refine uniformRamseyExpBound_log_four.weakenRate ?_
      intro r hr
      simp only [shiftRate]
      have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      nlinarith [hFnonneg r hr, hr.1.le]
    | succ j ih =>
      have hσ : 0 ≤ Real.log 4 / 2 ^ j := by
        have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        positivity
      have := shiftRate_half_of_shiftRate hderiv hDcont hMcont hFnonneg hDpos hM hX hY hXle
        hadm₁ hadm₂ hslack hσ ih
      have heq : Real.log 4 / 2 ^ j / 2 = Real.log 4 / 2 ^ (j + 1) := by
        rw [pow_succ]; ring
      simpa [heq] using this
  -- pass to the limit `j → ∞`
  apply uniformRamseyExpBound_of_eventually
  intro ε hε
  -- choose `j` with `2 * log 4 / 2^j ≤ ε / 2`
  obtain ⟨j, hj⟩ : ∃ j : ℕ, 2 * Real.log 4 / 2 ^ j ≤ ε / 2 := by
    have hlim : Tendsto (fun j : ℕ => 2 * Real.log 4 / (2 : ℝ) ^ j) atTop (𝓝 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
      have h := this.const_mul (2 * Real.log 4)
      simp only [mul_zero] at h
      refine h.congr ?_
      intro j
      rw [one_div, inv_pow, div_eq_mul_inv]
    exact (hlim.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < ε / 2))).exists.imp
      fun j hj => le_of_lt hj
  rcases hrung j with ⟨w⟩
  have herr := w.error_sublinear.eventually_abs_le (by linarith : (0 : ℝ) < ε / 2)
  filter_upwards [herr] with k hk
  intro ℓ hℓ hℓk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hℓ.trans_le hℓk
  have hr1 : (ℓ : ℝ) / (k : ℝ) ≤ 1 := by
    rw [div_le_one hkpos]; exact_mod_cast hℓk
  have hr0 : 0 ≤ (ℓ : ℝ) / (k : ℝ) := by positivity
  refine (w.bound k ℓ hℓ hℓk).trans (Real.exp_le_exp.mpr ?_)
  simp only [shiftRate]
  have hshift : Real.log 4 / 2 ^ j * (1 + (ℓ : ℝ) / (k : ℝ)) ≤ ε / 2 := by
    have h2 : 1 + (ℓ : ℝ) / (k : ℝ) ≤ 2 := by linarith
    have hσ : 0 ≤ Real.log 4 / 2 ^ j := by
      have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      positivity
    calc Real.log 4 / 2 ^ j * (1 + (ℓ : ℝ) / (k : ℝ))
        ≤ Real.log 4 / 2 ^ j * 2 := mul_le_mul_of_nonneg_left h2 hσ
      _ = 2 * Real.log 4 / 2 ^ j := by ring
      _ ≤ ε / 2 := hj
  have habs : w.error k ≤ ε / 2 * (k : ℝ) := (le_abs_self _).trans hk
  nlinarith [hshift, habs, hkpos]

end RamseyLean

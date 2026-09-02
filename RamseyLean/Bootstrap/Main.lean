import RamseyLean.Bootstrap.Analytic
import RamseyLean.Bootstrap.SmallLambda
import RamseyLean.Bootstrap.Cert
import RamseyLean.SelfConsistent
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic

/-!
# The bootstrap main theorem

Glue layer: the two region lemmas (`Bootstrap/SmallLambda.lean` on
`(0, λ₀]` and `Bootstrap/Cert.lean` on `[λ₀, 1]`) are combined into the
hypotheses of the self-consistent shift-ladder theorem
`uniformRamseyExpBound_selfConsistent`, giving

  `main_bootstrap : UniformRamseyExpBound Fpaper`,

followed by the binomial form (`bootstrap_main`, mirroring GNNW's
`RamseyLean.main`) and the diagonal corollary

  `R(k,k) ≤ exp ((2 log 2 - 0.159705 e⁻¹ + ε) k)`  eventually, for every `ε > 0`,

i.e. `R(k,k) ≤ 3.7718^{k + o(k)}`.

The Stirling/binomial-entropy comparison is copied verbatim (as private
lemmas) from `RamseyLean/Main.lean`; importing that module would drag in all
of GNNW's numerical certificate chunks, which are irrelevant here.
-/

set_option autoImplicit false

namespace RamseyLean
namespace Bootstrap

open Set Filter Asymptotics

noncomputable section

/-! ## Region glue -/

/-- Derivative sign facts on all of `(0,1]`, combining the two regions. -/
theorem derivFacts_paper :
    ∀ r ∈ Ioc (0 : ℝ) 1, 0 < Dpaper r ∧ D2paper r < 0 := by
  intro r hr
  rcases le_total r lam0 with h | h
  · exact smallLambda_derivFacts r ⟨hr.1, h⟩
  · exact cert_derivFacts r ⟨h, hr.2⟩

theorem Dpaper_pos : ∀ r ∈ Ioc (0 : ℝ) 1, 0 < Dpaper r :=
  fun r hr => (derivFacts_paper r hr).1

theorem D2paper_neg : ∀ r ∈ Ioc (0 : ℝ) 1, D2paper r < 0 :=
  fun r hr => (derivFacts_paper r hr).2

theorem tangentUB_paper : TangentUB :=
  tangentUB_of_D2neg D2paper_neg

theorem monoUB_paper : MonoUB :=
  monoUB_of_Dpos Dpaper_pos

/-- The pointwise ladder facts on all of `(0,1]`, combining the two regions. -/
theorem ladderFacts_paper :
    ∀ r ∈ Ioc (0 : ℝ) 1, LadderFactsAt r := by
  intro r hr
  rcases le_total r lam0 with h | h
  · exact smallLambda_ladderFacts tangentUB_paper monoUB_paper r ⟨hr.1, h⟩
  · exact cert_ladderFacts tangentUB_paper monoUB_paper r ⟨h, hr.2⟩

open Classical in
/-- A global admissible partner, obtained from the per-`r` existential of
`LadderFactsAt` by choice; junk value `1/2` off `(0,1]` (the ladder theorem
only evaluates `Y` on `(0,1]`). -/
def Ypaper (r : ℝ) : ℝ :=
  if h : r ∈ Ioc (0 : ℝ) 1 then ((ladderFacts_paper r h).2.2).choose else 1 / 2

theorem Ypaper_spec {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1) :
    Ypaper r ∈ Ioo (0 : ℝ) 1 ∧
      (∀ s ∈ Ioc (0 : ℝ) 1,
        Fpaper s ≤ -Real.log (Xpaper r) - s * Real.log (Ypaper r)) ∧
      (∀ s ∈ Ioc (0 : ℝ) 1,
        Fpaper s ≤ -Real.log (Ypaper r) - s * Real.log (Xpaper r)) ∧
      denseCaseExponent (Xpaper r) (Mpaper r) (Ypaper r) r < Fpaper r := by
  simp only [Ypaper, dif_pos hr]
  exact ((ladderFacts_paper r hr).2.2).choose_spec

/-! ## The main theorem -/

/-- The paper's main uniform bound: `Fpaper` is a valid uniform exponential
Ramsey rate, `R(k,ℓ) ≤ exp (Fpaper (ℓ/k) k + o(k))` uniformly in `1 ≤ ℓ ≤ k`. -/
theorem main_bootstrap : UniformRamseyExpBound Fpaper := by
  apply uniformRamseyExpBound_selfConsistent
    (F := Fpaper) (D := Dpaper) (M := Mpaper) (X := Xpaper) (Y := Ypaper)
  · exact fun r hr => hasDerivAt_Fpaper hr.1
  · exact continuousOn_Dpaper
  · exact continuousOn_Mpaper
  · exact Fpaper_nonneg Dpaper_pos
  · exact Dpaper_pos
  · exact fun r hr => (ladderFacts_paper r hr).1
  · exact fun r hr => (ladderFacts_paper r hr).2.1
  · exact fun r hr => (Ypaper_spec hr).1
  · exact fun r hr => le_of_eq rfl
  · exact fun r hr => (Ypaper_spec hr).2.1
  · exact fun r hr => (Ypaper_spec hr).2.2.1
  · exact fun r hr => (Ypaper_spec hr).2.2.2

/-! ## The binomial-entropy comparison (copied from `RamseyLean/Main.lean`) -/

private theorem log_factorial_le_stirling_upper {n : ℕ} (hn : n ≠ 0) :
    Real.log (n.factorial : ℝ) ≤ n * Real.log n - n + Real.log n / 2 + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hmono :
      Real.log (Stirling.stirlingSeq (m + 1)) ≤
        Real.log (Stirling.stirlingSeq 1) := by
    exact Stirling.log_stirlingSeq'_antitone (Nat.zero_le m)
  have hconst :
      Real.log (Stirling.stirlingSeq 1) = 1 - Real.log 2 / 2 := by
    rw [Stirling.stirlingSeq_one,
      Real.log_div (by positivity) (by positivity), Real.log_exp,
      Real.log_sqrt (by positivity)]
  rw [Stirling.log_stirlingSeq_formula, hconst,
    Real.log_div (by positivity) (by positivity), Real.log_exp] at hmono
  rw [Real.log_mul (by norm_num) (by positivity)] at hmono
  nlinarith

private theorem log_choose_add (k ℓ : ℕ) :
    Real.log (Nat.choose (k + ℓ) ℓ : ℝ) =
      Real.log ((k + ℓ).factorial : ℝ) -
        Real.log (k.factorial : ℝ) - Real.log (ℓ.factorial : ℝ) := by
  have hℓsum : ℓ ≤ k + ℓ := by omega
  have hnat :
      Nat.choose (k + ℓ) ℓ * ℓ.factorial * k.factorial =
        (k + ℓ).factorial := by
    simpa using Nat.choose_mul_factorial_mul_factorial hℓsum
  have hcast :
      (Nat.choose (k + ℓ) ℓ : ℝ) * (ℓ.factorial : ℝ) * (k.factorial : ℝ) =
        ((k + ℓ).factorial : ℝ) := by
    exact_mod_cast hnat
  have hchoose0 : (Nat.choose (k + ℓ) ℓ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hℓsum))
  have hℓfac0 : (ℓ.factorial : ℝ) ≠ 0 := by positivity
  have hkfac0 : (k.factorial : ℝ) ≠ 0 := by positivity
  have hlog := congrArg Real.log hcast
  rw [Real.log_mul (mul_ne_zero hchoose0 hℓfac0) hkfac0,
    Real.log_mul hchoose0 hℓfac0] at hlog
  linarith

private theorem entropy_ratio_mul {k ℓ : ℕ} (hk : 0 < k) (hℓ : 0 < ℓ) :
    entropy ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ) =
      ((k + ℓ : ℕ) : ℝ) * Real.log (k + ℓ) -
        (k : ℝ) * Real.log k - (ℓ : ℝ) * Real.log ℓ := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hsumR : (0 : ℝ) < k + ℓ := by positivity
  have hone :
      1 + (ℓ : ℝ) / (k : ℝ) = ((k + ℓ : ℕ) : ℝ) / (k : ℝ) := by
    rw [Nat.cast_add]
    field_simp [hkR.ne']
  rw [entropy, hone]
  push_cast
  rw [Real.log_div hsumR.ne' hkR.ne', Real.log_div hℓR.ne' hkR.ne']
  field_simp [hkR.ne']
  ring

/-- The explicit `O(log k)` loss in the uniform binomial-entropy estimate. -/
private def binomialEntropyError (k : ℕ) : ℝ :=
  Real.log (k : ℝ) / 2 + 2

private theorem sublinearError_binomialEntropyError :
    SublinearError binomialEntropyError := by
  have hlog : SublinearError (fun k : ℕ => Real.log (k : ℝ)) := by
    change (fun k : ℕ => Real.log (k : ℝ)) =o[atTop]
      (fun k : ℕ => (k : ℝ))
    exact Real.isLittleO_log_id_atTop.natCast_atTop
  change (fun k : ℕ => Real.log (k : ℝ) / 2 + 2) =o[atTop]
    ramseyLinearScale
  simpa [binomialEntropyError, div_eq_mul_inv, mul_comm] using
    (hlog.const_mul_left (2 : ℝ)⁻¹).add (sublinearError_const 2)

private theorem entropy_mul_le_log_choose_add_error {k ℓ : ℕ}
    (hℓ : 0 < ℓ) (hℓk : ℓ ≤ k) :
    entropy ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ) ≤
      Real.log (Nat.choose (k + ℓ) ℓ : ℝ) + binomialEntropyError k := by
  have hk : 0 < k := lt_of_lt_of_le hℓ hℓk
  have hsum0 : k + ℓ ≠ 0 := by omega
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  have hℓ0 : ℓ ≠ 0 := Nat.ne_of_gt hℓ
  have hsumLower := Stirling.le_log_factorial_stirling hsum0
  have hkUpper := log_factorial_le_stirling_upper hk0
  have hℓUpper := log_factorial_le_stirling_upper hℓ0
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hℓsumR : (ℓ : ℝ) ≤ (k + ℓ : ℕ) := by
    exact_mod_cast (show ℓ ≤ k + ℓ by omega)
  have hlogℓsum : Real.log (ℓ : ℝ) ≤ Real.log (k + ℓ : ℕ) :=
    Real.log_le_log hℓR hℓsumR
  have hlogTwoPi : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.two_le_pi]
  push_cast at hsumLower hlogℓsum
  rw [log_choose_add, entropy_ratio_mul hk hℓ]
  dsimp [binomialEntropyError]
  push_cast
  linarith

private theorem choose_entropy_lower_bound {k ℓ : ℕ}
    (hℓ : 0 < ℓ) (hℓk : ℓ ≤ k) :
    Real.exp
        (entropy ((ℓ : ℝ) / (k : ℝ)) * (k : ℝ) - binomialEntropyError k) ≤
      (Nat.choose (k + ℓ) ℓ : ℝ) := by
  have hchoosePos : 0 < (Nat.choose (k + ℓ) ℓ : ℝ) := by
    exact_mod_cast Nat.choose_pos (show ℓ ≤ k + ℓ by omega)
  rw [← Real.exp_log hchoosePos]
  apply Real.exp_le_exp.mpr
  linarith [entropy_mul_le_log_choose_add_error hℓ hℓk]

/-! ## Final statements -/

/-- The bootstrap main theorem in the printed shape of GNNW's `main`, with
the binomial coefficient factored out via the Stirling comparison:
`R(k,ℓ) ≤ e^{P(ℓ/k) e^{-ℓ/k} k + o(k)} \binom{k+ℓ}{ℓ}` uniformly in
`1 ≤ ℓ ≤ k`. -/
theorem bootstrap_main :
    ∃ η : ℕ → ℝ,
      SublinearError η ∧
      ∀ k ℓ : ℕ, 0 < ℓ → ℓ ≤ k →
        (ramseyNumber k ℓ : ℝ) ≤
          Real.exp
              (Real.exp (-((ℓ : ℝ) / (k : ℝ))) * Ppaper ((ℓ : ℝ) / (k : ℝ)) *
                (k : ℝ) + η k) *
            (Nat.choose (k + ℓ) ℓ : ℝ) := by
  rcases main_bootstrap with ⟨w⟩
  refine ⟨fun k => w.error k + binomialEntropyError k,
    w.error_sublinear.add sublinearError_binomialEntropyError, ?_⟩
  intro k ℓ hℓ hℓk
  set r : ℝ := (ℓ : ℝ) / (k : ℝ) with hr
  calc
    (ramseyNumber k ℓ : ℝ) ≤
        Real.exp (Fpaper r * (k : ℝ) + w.error k) :=
      w.bound k ℓ hℓ hℓk
    _ = Real.exp
          (Real.exp (-r) * Ppaper r * (k : ℝ) +
            (w.error k + binomialEntropyError k)) *
        Real.exp (entropy r * (k : ℝ) - binomialEntropyError k) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [Fpaper]
      ring
    _ ≤ Real.exp
          (Real.exp (-r) * Ppaper r * (k : ℝ) +
            (w.error k + binomialEntropyError k)) *
        (Nat.choose (k + ℓ) ℓ : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (choose_entropy_lower_bound hℓ hℓk) (Real.exp_pos _).le

/-- The diagonal value of the rate function:
`Fpaper 1 = 2 log 2 - 0.159705 e⁻¹ = log (3.7717…)`. -/
theorem Fpaper_one :
    Fpaper 1 = 2 * Real.log 2 - (159705 / 1000000 : ℝ) * Real.exp (-1) := by
  have hent : entropy 1 = 2 * Real.log 2 := by
    show (1 + 1) * Real.log (1 + 1) - 1 * Real.log 1 = 2 * Real.log 2
    norm_num
  have hP1 : Ppaper 1 = -159705 / 1000000 := by norm_num [Ppaper]
  show entropy 1 + Real.exp (-1) * Ppaper 1 = _
  rw [hent, hP1]
  ring

/-- Diagonal corollary: `R(k,k) ≤ exp ((2 log 2 - 0.159705 e⁻¹ + ε) k)`
for every `ε > 0` and all sufficiently large `k`; numerically
`R(k,k) ≤ 3.7718^k` eventually. -/
theorem bootstrap_diagonal :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k : ℕ in atTop,
        (ramseyNumber k k : ℝ) ≤
          Real.exp
            ((2 * Real.log 2 - (159705 / 1000000 : ℝ) * Real.exp (-1) + ε) *
              (k : ℝ)) := by
  intro ε hε
  filter_upwards [main_bootstrap.eventually ε hε, eventually_gt_atTop 0]
    with k hk hkpos
  have hkR : ((k : ℝ)) ≠ 0 := by
    exact_mod_cast hkpos.ne'
  have h := hk k hkpos le_rfl
  rwa [div_self hkR, Fpaper_one] at h

end

end Bootstrap
end RamseyLean

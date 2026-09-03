import RamseyLean.Bootstrap2.Check
import RamseyLean.Bootstrap2.Spline
import RamseyLean.Bootstrap2.Cover
import RamseyLean.Bootstrap2.Glue
import RamseyLean.SelfConsistent

/-!
# The spline-certificate main theorem (glue layer)

Given a certificate `cells : List Cell` passing the four Boolean passes
(`cells.all checkCell`, `checkChain`, `checkWitnesses`, `checkTail`), the
functions `Fcert/Dcert/Mcert/Xcert/Ycert` satisfy every hypothesis of the
self-consistent shift-ladder theorem `uniformRamseyExpBound_selfConsistent`,
so `Fcert cells` is a valid uniform exponential Ramsey bound; the diagonal
value is the last node's `F`-value, an explicit rational.
-/

set_option autoImplicit false

namespace RamseyLean
namespace Bootstrap2

open Set Filter

/-- `ChainOK` from the Boolean passes. -/
theorem chainOK_of_checks {cells : List Cell}
    (hall : cells.all checkCell = true)
    (hchain : checkChain cells = true) : ChainOK cells := by
  obtain ⟨hne, hhead, hlast, hchn⟩ := checkChain_sound hchain
  refine ⟨hne, ?_, ?_, hchn, ?_⟩
  · cases hh : cells.head? with
    | none => exact absurd (List.head?_eq_none_iff.mp hh) hne
    | some c0 => simp [hhead c0 hh]
  · cases hh : cells.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hh) hne
    | some cN => simp [hlast cN hh]
  · intro c hc
    obtain ⟨-, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ :=
      all_checkCell_int_facts hall c hc
    exact ⟨h2, h3, h4, h6, h7, h8, h9,
      checkCell_M_mono c (List.all_eq_true.mp hall c hc), h5⟩

variable {cells : List Cell}

/-- Positivity of the head node's `F`-value, from (T1). -/
theorem F0_pos (hall : cells.all checkCell = true)
    (htail : checkTail cells = true)
    {c0 : Cell} (hc0 : cells.head? = some c0) : 0 < c0.n0.FR := by
  have hT1 := checkTail_sound htail c0 hc0
  have hfacts := all_checkCell_int_facts hall c0 (List.mem_of_mem_head? hc0)
  obtain ⟨h1, -, h3, h4, -, -, -, -, -, hX0, hXS, -⟩ := hfacts
  have hXr : (0:ℝ) < (c0.X : ℝ) / (SC : ℝ) := by
    apply div_pos (by exact_mod_cast hX0)
    norm_num [SC]
  have hXr1 : (c0.X : ℝ) / (SC : ℝ) < 1 := by
    rw [div_lt_one (by norm_num [SC])]
    exact_mod_cast hXS
  have hlog : Real.log ((c0.X : ℝ) / (SC : ℝ)) < 0 := Real.log_neg hXr hXr1
  have hlam : (0:ℝ) < c0.n0.lamR := by
    rw [Node.lamR]
    apply div_pos (by exact_mod_cast h1)
    norm_num [SC]
  have hd : (0:ℝ) < c0.n0.dR := by
    rw [Node.dR]
    apply div_pos ?_ (by norm_num [SC])
    exact_mod_cast h3.trans_le h4
  nlinarith [mul_pos hlam hd]

/-- All pointwise ladder hypotheses on `(0, 1]`, by tail/cell dispatch. -/
theorem allHyps (hall : cells.all checkCell = true)
    (hchain : checkChain cells = true)
    (hwit : checkWitnesses cells = true)
    (htail : checkTail cells = true) :
    ∀ r ∈ Ioc (0:ℝ) 1,
      LadderHypsAt (Fcert cells) (Dcert cells) (Mcert cells)
        (Xcert cells) (Ycert cells) r := by
  have hOK := chainOK_of_checks hall hchain
  obtain ⟨hne, hhead, hlast, hchn⟩ := checkChain_sound hchain
  obtain ⟨c0, hc0⟩ : ∃ c0, cells.head? = some c0 := by
    cases cells with
    | nil => exact absurd rfl hne
    | cons a l => exact ⟨a, rfl⟩
  have hc0mem : c0 ∈ cells := List.mem_of_mem_head? hc0
  have hlamR0 : c0.n0.lamR = lam0 := head_lamR hOK hc0
  have htan : ∀ c ∈ cells,
      (∀ s ∈ Ioc (0:ℝ) 1, Fcert cells s ≤ c.wa.FR + (s - c.wa.lamR) * c.wa.dR) ∧
      (∀ s ∈ Ioc (0:ℝ) 1, Fcert cells s ≤ c.wb.FR + (s - c.wb.lamR) * c.wb.dR) := by
    intro c hc
    obtain ⟨hwa, hwb⟩ := checkWitnesses_sound hwit c hc
    exact ⟨tangentUB hOK c.wa hwa, tangentUB hOK c.wb hwb⟩
  intro r hr
  rcases le_or_gt r lam0 with hle | hgt
  · -- tail region (0, λ₀]
    have hchk : checkCell c0 = true := List.all_eq_true.mp hall c0 hc0mem
    have := checkCell_sound_tail c0 hchk
      (Fcert cells) (Dcert cells) (Mcert cells) (Xcert cells) (Ycert cells)
      (checkTail_sound htail c0 hc0)
      (fun r' hr' => Fcert_tail_linear hOK hc0 r' (hlamR0 ▸ hr'.2))
      (fun r' hr' => (tailVals hOK hc0 r' (hlamR0 ▸ hr'.2)).1)
      (fun r' hr' => (tailVals hOK hc0 r' (hlamR0 ▸ hr'.2)).2.1)
      (fun r' hr' => (tailVals hOK hc0 r' (hlamR0 ▸ hr'.2)).2.2.1)
      (fun r' hr' => (tailVals hOK hc0 r' (hlamR0 ▸ hr'.2)).2.2.2)
      (htan c0 hc0mem).1 (htan c0 hc0mem).2
    exact this r ⟨hr.1, hlamR0 ▸ hle⟩
  · -- cell region (λ₀, 1]
    obtain ⟨c, hc, hmem⟩ := cover cells hne hchn hhead hlast r ⟨hgt, hr.2⟩
    have hchk : checkCell c = true := List.all_eq_true.mp hall c hc
    have hF0pos := F0_pos hall htail hc0
    have hlamle : lam0 ≤ c.n0.lamR := by
      have hint := lam_ge_head cells c0 hc0 hchn
        (fun d hd => (all_checkCell_int_facts hall d hd).2.1) c hc
      rw [← hlamR0, Node.lamR, Node.lamR]
      have hSC : (0:ℝ) < (SC : ℝ) := by norm_num [SC]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hint) hSC.le
    have hFnn : 0 ≤ Fcert cells c.n0.lamR := by
      have h1 : Fcert cells lam0 = c0.n0.FR := by
        rw [← hlamR0]; exact (nodeVals hOK c0 hc0mem).1
      have := Fmono hOK hlamle
      rw [h1] at this
      exact (hF0pos.le.trans this)
    exact checkCell_sound c hchk
      (Fcert cells) (Dcert cells) (Mcert cells) (Xcert cells) (Ycert cells)
      (nodeVals hOK c hc).1 (nodeVals hOK c hc).2
      (fun r' hr' => Fmono hOK hr'.1.le)
      (Fchord hOK c hc)
      (htan c hc).1 (htan c hc).2
      hFnn
      (fun r' hr' => Dbox hOK c hc r' ⟨hr'.1.le, hr'.2⟩)
      (Mlin hOK c hc)
      (Xval hOK c hc) (Yval hOK c hc)
      r hmem hr.2

/-- The main theorem: a fully checked certificate makes `Fcert cells` a valid
uniform exponential Ramsey bound. -/
theorem main_cert (hall : cells.all checkCell = true)
    (hchain : checkChain cells = true)
    (hwit : checkWitnesses cells = true)
    (htail : checkTail cells = true) :
    UniformRamseyExpBound (Fcert cells) := by
  have hOK := chainOK_of_checks hall hchain
  have hyps := allHyps hall hchain hwit htail
  refine uniformRamseyExpBound_selfConsistent
    (F := Fcert cells) (D := Dcert cells) (M := Mcert cells)
    (X := Xcert cells) (Y := Ycert cells)
    (fun r _ => hderiv hOK r)
    ((dcont hOK).continuousOn)
    ((mcont hOK).continuousOn)
    (fun r hr => (hyps r hr).1)
    (fun r _ => Dpos hOK r)
    (fun r hr => (hyps r hr).2.2.1)
    (fun r hr => (hyps r hr).2.2.2.1)
    (fun r hr => (hyps r hr).2.2.2.2.1)
    (fun r hr => (hyps r hr).2.2.2.2.2.1)
    (fun r hr => (hyps r hr).2.2.2.2.2.2.1)
    (fun r hr => (hyps r hr).2.2.2.2.2.2.2.1)
    (fun r hr => (hyps r hr).2.2.2.2.2.2.2.2)

/-- Diagonal corollary: `R(k,k) ≤ exp ((F_N + ε) k)` eventually, for every
`ε > 0`, where `F_N = (last).n1.FR` is the certificate's terminal value (an
explicit rational). -/
theorem cert_diagonal (hall : cells.all checkCell = true)
    (hchain : checkChain cells = true)
    (hwit : checkWitnesses cells = true)
    (htail : checkTail cells = true)
    {cN : Cell} (hN : cells.getLast? = some cN) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k : ℕ in atTop,
        (ramseyNumber k k : ℝ) ≤ Real.exp ((cN.n1.FR + ε) * (k : ℝ)) := by
  intro ε hε
  have hOK := chainOK_of_checks hall hchain
  have hmain := main_cert hall hchain hwit htail
  filter_upwards [hmain.eventually ε hε, eventually_gt_atTop 0]
    with k hk hkpos
  have hkR : ((k : ℝ)) ≠ 0 := by exact_mod_cast hkpos.ne'
  have h := hk k hkpos le_rfl
  rwa [div_self hkR, F1val hOK hN] at h

end Bootstrap2
end RamseyLean

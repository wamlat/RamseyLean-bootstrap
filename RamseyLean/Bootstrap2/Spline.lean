import RamseyLean.Bootstrap2.Defs

/-!
# Spline certificate (Bootstrap2): analysis layer

Sorry-free real-analysis facts about the data-defined functions of
`Bootstrap2/Defs.lean` (`Dcert`, `Mcert`, `Fcert`, `Xcert`, `Ycert`), under the
data-level chain-validity predicate `ChainOK`:

* `dcont`, `mcont` : global continuity of `Dcert`/`Mcert`;
* `hderiv`         : `HasDerivAt (Fcert cells) (Dcert cells r) r` for all `r` (FTC-1);
* `nodeVals`       : `Fcert` interpolates the nodal `F`-values exactly
  (trapezoid rule + the exact integer chain identity);
* `Dbox`, `Mbox`   : per-cell boxes for `Dcert`/`Mcert`;
* `Xval`, `Yval`, `tailVals` : values of the step functions on cells / the tail;
* `Dpos`, `Danti`  : positivity and global antitonicity of `Dcert`;
* `tangentUB`      : the tangent line at every node dominates `Fcert` (concavity);
* `Fmono`, `F1val` : monotonicity of `Fcert` and its value at `1`.

NOTE: `ChainOK` is stated with `List.IsChain`; in this toolchain `List.Chain'`
is a deprecated alias with `Chain' R = IsChain R` definitionally.
-/

namespace RamseyLean
namespace Bootstrap2

open Set

/-! ### Scale constants -/

private lemma SCR_pos : (0 : ℝ) < (SC : ℝ) := by norm_num [SC]

private lemma SCR_ne : (SC : ℝ) ≠ 0 := ne_of_gt SCR_pos

private lemma FSR_eq : (FS : ℝ) = 2 * (SC : ℝ) ^ 2 := by norm_num [FS, SC]

private lemma keyR_lt {a b : Int} (hab : a < b) :
    (a : ℝ) / (SC : ℝ) < (b : ℝ) / (SC : ℝ) :=
  div_lt_div_of_pos_right (by exact_mod_cast hab) SCR_pos

private lemma keyR_le {a b : Int} (hab : a ≤ b) :
    (a : ℝ) / (SC : ℝ) ≤ (b : ℝ) / (SC : ℝ) := by
  rcases lt_or_eq_of_le hab with h | rfl
  · exact (keyR_lt h).le
  · exact le_rfl

/-! ### The chord (affine piece of the PL interpolation) -/

/-- The affine chord between `(a, v)` and `(b, w)` (abscissas and values at
scale `SC`), written exactly as in the recursive case of `plInterp`. -/
private noncomputable def chord (a v b w : Int) (r : ℝ) : ℝ :=
  (v : ℝ) / (SC : ℝ) +
    (r - (a : ℝ) / (SC : ℝ)) * (((w : ℝ) - (v : ℝ)) / ((b : ℝ) - (a : ℝ)))

private lemma chord_left {a v b w : Int} :
    chord a v b w ((a : ℝ) / (SC : ℝ)) = (v : ℝ) / (SC : ℝ) := by
  simp [chord]

private lemma chord_right {a v b w : Int} (hab : a < b) :
    chord a v b w ((b : ℝ) / (SC : ℝ)) = (w : ℝ) / (SC : ℝ) := by
  have hba : ((b : ℝ)) - (a : ℝ) ≠ 0 := by
    have : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    linarith
  unfold chord
  field_simp
  try ring

private lemma chord_continuous {a v b w : Int} : Continuous (chord a v b w) := by
  unfold chord
  exact continuous_const.add ((continuous_id.sub continuous_const).mul continuous_const)

private lemma chord_mem_Icc {a v b w : Int} (hab : a < b) {r : ℝ}
    (hr : r ∈ Icc ((a : ℝ) / (SC : ℝ)) ((b : ℝ) / (SC : ℝ))) :
    chord a v b w r ∈
      Icc (min ((v : ℝ) / (SC : ℝ)) ((w : ℝ) / (SC : ℝ)))
        (max ((v : ℝ) / (SC : ℝ)) ((w : ℝ) / (SC : ℝ))) := by
  have hba : (0 : ℝ) < (b : ℝ) - (a : ℝ) := by
    have : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    linarith
  have h1 : 0 ≤ r - (a : ℝ) / (SC : ℝ) := by linarith [hr.1]
  have h2 : r - (a : ℝ) / (SC : ℝ) ≤ ((b : ℝ) - (a : ℝ)) / (SC : ℝ) := by
    have := hr.2
    rw [sub_div]
    linarith
  have hkey : ((b : ℝ) - (a : ℝ)) / (SC : ℝ) *
      (((w : ℝ) - (v : ℝ)) / ((b : ℝ) - (a : ℝ))) = ((w : ℝ) - (v : ℝ)) / (SC : ℝ) := by
    field_simp
    try ring
  rcases le_total (v : ℝ) (w : ℝ) with hvw | hvw
  · have hm : 0 ≤ ((w : ℝ) - (v : ℝ)) / ((b : ℝ) - (a : ℝ)) :=
      div_nonneg (by linarith) hba.le
    constructor
    · have := mul_nonneg h1 hm
      have hmin : min ((v : ℝ) / (SC : ℝ)) ((w : ℝ) / (SC : ℝ)) ≤ (v : ℝ) / (SC : ℝ) :=
        min_le_left _ _
      unfold chord
      linarith
    · have hle := mul_le_mul_of_nonneg_right h2 hm
      rw [hkey] at hle
      have hmax : (w : ℝ) / (SC : ℝ) ≤ max ((v : ℝ) / (SC : ℝ)) ((w : ℝ) / (SC : ℝ)) :=
        le_max_right _ _
      unfold chord
      have hsplit : ((w : ℝ) - (v : ℝ)) / (SC : ℝ) =
          (w : ℝ) / (SC : ℝ) - (v : ℝ) / (SC : ℝ) := sub_div _ _ _
      linarith
  · have hm : ((w : ℝ) - (v : ℝ)) / ((b : ℝ) - (a : ℝ)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hba.le
    constructor
    · have hge := mul_le_mul_of_nonpos_right h2 hm
      rw [hkey] at hge
      have hmin : min ((v : ℝ) / (SC : ℝ)) ((w : ℝ) / (SC : ℝ)) ≤ (w : ℝ) / (SC : ℝ) :=
        min_le_right _ _
      unfold chord
      have hsplit : ((w : ℝ) - (v : ℝ)) / (SC : ℝ) =
          (w : ℝ) / (SC : ℝ) - (v : ℝ) / (SC : ℝ) := sub_div _ _ _
      linarith
    · have := mul_nonpos_of_nonneg_of_nonpos h1 hm
      have hmax : (v : ℝ) / (SC : ℝ) ≤ max ((v : ℝ) / (SC : ℝ)) ((w : ℝ) / (SC : ℝ)) :=
        le_max_left _ _
      unfold chord
      linarith

private lemma chord_antitone {a v b w : Int} (hab : a < b) (hwv : w ≤ v) :
    Antitone (chord a v b w) := by
  intro x y hxy
  have hba : (0 : ℝ) < (b : ℝ) - (a : ℝ) := by
    have : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    linarith
  have hm : ((w : ℝ) - (v : ℝ)) / ((b : ℝ) - (a : ℝ)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by
      have : (w : ℝ) ≤ (v : ℝ) := by exact_mod_cast hwv
      linarith) hba.le
  have := mul_le_mul_of_nonpos_right
    (by linarith : x - (a : ℝ) / (SC : ℝ) ≤ y - (a : ℝ) / (SC : ℝ)) hm
  unfold chord
  linarith

/-- Exact integral of a chord over its cell: the trapezoid rule. -/
private lemma integral_chord {a v b w : Int} (hab : a < b) :
    ∫ t in ((a : ℝ) / (SC : ℝ))..((b : ℝ) / (SC : ℝ)), chord a v b w t =
      (((v : ℝ) / (SC : ℝ) + (w : ℝ) / (SC : ℝ)) / 2) *
        ((b : ℝ) / (SC : ℝ) - (a : ℝ) / (SC : ℝ)) := by
  have hba : ((a : ℝ)) < (b : ℝ) := by exact_mod_cast hab
  have hba' : ((b : ℝ)) - (a : ℝ) ≠ 0 := by linarith
  have hG : ∀ t : ℝ, HasDerivAt
      (fun t => ((v : ℝ) / (SC : ℝ) -
          (((w : ℝ) - (v : ℝ)) / ((b : ℝ) - (a : ℝ))) * ((a : ℝ) / (SC : ℝ))) * t +
        (((w : ℝ) - (v : ℝ)) / ((b : ℝ) - (a : ℝ))) / 2 * t ^ 2)
      (chord a v b w t) t := by
    intro t
    have h1 : HasDerivAt
        (fun t : ℝ => ((v : ℝ) / (SC : ℝ) -
          (((w : ℝ) - (v : ℝ)) / ((b : ℝ) - (a : ℝ))) * ((a : ℝ) / (SC : ℝ))) * t)
        ((v : ℝ) / (SC : ℝ) -
          (((w : ℝ) - (v : ℝ)) / ((b : ℝ) - (a : ℝ))) * ((a : ℝ) / (SC : ℝ))) t := by
      simpa using (hasDerivAt_id t).const_mul
        ((v : ℝ) / (SC : ℝ) -
          (((w : ℝ) - (v : ℝ)) / ((b : ℝ) - (a : ℝ))) * ((a : ℝ) / (SC : ℝ)))
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t ^ 1) t := by
      simpa using hasDerivAt_pow 2 t
    have h3 := h1.add (h2.const_mul ((((w : ℝ) - (v : ℝ)) / ((b : ℝ) - (a : ℝ))) / 2))
    have hd : chord a v b w t =
        ((v : ℝ) / (SC : ℝ) -
          (((w : ℝ) - (v : ℝ)) / ((b : ℝ) - (a : ℝ))) * ((a : ℝ) / (SC : ℝ))) +
        (((w : ℝ) - (v : ℝ)) / ((b : ℝ) - (a : ℝ))) / 2 * (2 * t ^ 1) := by
      unfold chord
      ring
    rw [hd]
    exact h3
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hG t)
    (chord_continuous.intervalIntegrable _ _)]
  field_simp
  try ring

/-! ### Generic `IsChain` helpers -/

/-- In a strictly key-sorted list, the head key is below every later key. -/
private lemma key_lt_of_mem {α : Type*} (key : α → Int) :
    ∀ {l : List α} {p x : α},
      (p :: l).IsChain (fun s t => key s < key t) → x ∈ l → key p < key x
  | [], _, _, _, hx => absurd hx (List.not_mem_nil)
  | q :: l, p, x, h, hx => by
    obtain ⟨hpq, htail⟩ := List.isChain_cons_cons.mp h
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hpq
    · exact lt_trans hpq (key_lt_of_mem key htail hx')

/-- In a strictly key-sorted list `l₁ ++ x :: l₂`, all keys of `l₁` are below
the key of `x`. -/
private lemma key_lt_of_append {α : Type*} (key : α → Int) :
    ∀ {l₁ : List α} {x : α} {l₂ : List α},
      (l₁ ++ x :: l₂).IsChain (fun s t => key s < key t) → ∀ y ∈ l₁, key y < key x
  | [], _, _, _, y, hy => absurd hy (List.not_mem_nil)
  | p :: l₁, x, l₂, h, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact key_lt_of_mem key h (List.mem_append_right _ (List.mem_cons_self))
    · exact key_lt_of_append key (l₁ := l₁) (List.IsChain.tail h) y hy'

/-- A chain on an append restricts to the right part. -/
private lemma isChain_append_right {α : Type*} {R : α → α → Prop} :
    ∀ {l₁ l₂ : List α}, (l₁ ++ l₂).IsChain R → l₂.IsChain R
  | [], _, h => h
  | _ :: l₁, _, h => isChain_append_right (l₁ := l₁) (List.IsChain.tail h)

/-! ### `plInterp`: equations and basic lemmas -/

private lemma plInterp_nil (r : ℝ) : plInterp [] r = 0 := rfl

private lemma plInterp_single (a v : Int) (r : ℝ) :
    plInterp [(a, v)] r = (v : ℝ) / (SC : ℝ) := rfl

private lemma plInterp_cons₂ (a v b w : Int) (rest : List (Int × Int)) (r : ℝ) :
    plInterp ((a, v) :: (b, w) :: rest) r =
      if r ≤ (b : ℝ) / (SC : ℝ) then
        if r ≤ (a : ℝ) / (SC : ℝ) then (v : ℝ) / (SC : ℝ) else chord a v b w r
      else plInterp ((b, w) :: rest) r := rfl

/-- Left clamp: at or below the first breakpoint the value is the first value. -/
private lemma plInterp_head_val {a v : Int} {tl : List (Int × Int)}
    (htl : ∀ y ∈ tl.head?, a < y.1) {r : ℝ} (hr : r ≤ (a : ℝ) / (SC : ℝ)) :
    plInterp ((a, v) :: tl) r = (v : ℝ) / (SC : ℝ) := by
  match tl with
  | [] => rfl
  | (b, w) :: rest =>
    have hab : a < b := htl (b, w) rfl
    rw [plInterp_cons₂, if_pos (le_trans hr (keyR_lt hab).le), if_pos hr]

/-- Value at a breakpoint, decomposition form. -/
private lemma plInterp_at_key :
    ∀ (l₁ : List (Int × Int)) {a v : Int} (l₂ : List (Int × Int)),
      (∀ x ∈ l₁, x.1 < a) → (∀ y ∈ l₂.head?, a < y.1) →
      plInterp (l₁ ++ (a, v) :: l₂) ((a : ℝ) / (SC : ℝ)) = (v : ℝ) / (SC : ℝ)
  | [], a, v, l₂, _, h₂ => plInterp_head_val h₂ le_rfl
  | [(p, q)], a, v, l₂, h₁, _ => by
    have hpa : p < a := h₁ (p, q) (List.mem_singleton_self _)
    rw [List.singleton_append, plInterp_cons₂, if_pos le_rfl,
      if_neg (not_le.mpr (keyR_lt hpa)), chord_right hpa]
  | (p, q) :: (p₂, q₂) :: l₁, a, v, l₂, h₁, h₂ => by
    have hp₂ : p₂ < a := h₁ (p₂, q₂) (by simp)
    rw [List.cons_append, List.cons_append, plInterp_cons₂,
      if_neg (not_le.mpr (keyR_lt hp₂))]
    rw [← List.cons_append]
    exact plInterp_at_key ((p₂, q₂) :: l₁) l₂
      (fun x hx => h₁ x (List.mem_cons_of_mem _ hx)) h₂

/-- On the interior-plus-right-end of a cell, `plInterp` is the cell's chord. -/
private lemma plInterp_eq_chord :
    ∀ (l₁ : List (Int × Int)) {a v b w : Int} (l₂ : List (Int × Int)) {r : ℝ},
      (∀ x ∈ l₁, x.1 < a) → a < b →
      (a : ℝ) / (SC : ℝ) < r → r ≤ (b : ℝ) / (SC : ℝ) →
      plInterp (l₁ ++ (a, v) :: (b, w) :: l₂) r = chord a v b w r
  | [], a, v, b, w, l₂, r, _, hab, h1, h2 => by
    rw [List.nil_append, plInterp_cons₂, if_pos h2, if_neg (not_le.mpr h1)]
  | [(p, q)], a, v, b, w, l₂, r, _, hab, h1, h2 => by
    rw [List.singleton_append, plInterp_cons₂, if_neg (not_le.mpr h1)]
    exact plInterp_eq_chord [] l₂ (by simp) hab h1 h2
  | (p, q) :: (p₂, q₂) :: l₁, a, v, b, w, l₂, r, h₁, hab, h1, h2 => by
    have hp₂ : p₂ < a := h₁ (p₂, q₂) (by simp)
    rw [List.cons_append, List.cons_append, plInterp_cons₂,
      if_neg (not_le.mpr (lt_trans (keyR_lt hp₂) h1))]
    rw [← List.cons_append]
    exact plInterp_eq_chord ((p₂, q₂) :: l₁) l₂
      (fun x hx => h₁ x (List.mem_cons_of_mem _ hx)) hab h1 h2

/-- On the whole closed cell, `plInterp` agrees with the cell's chord. -/
private lemma plInterp_eqOn_chord (l₁ : List (Int × Int)) {a v b w : Int}
    (l₂ : List (Int × Int)) (h₁ : ∀ x ∈ l₁, x.1 < a) (hab : a < b) :
    EqOn (plInterp (l₁ ++ (a, v) :: (b, w) :: l₂)) (chord a v b w)
      (Icc ((a : ℝ) / (SC : ℝ)) ((b : ℝ) / (SC : ℝ))) := by
  intro r hr
  rcases eq_or_lt_of_le hr.1 with heq | hlt
  · rw [← heq]
    rw [plInterp_at_key l₁ ((b, w) :: l₂) h₁
      (fun y hy => by
        obtain rfl : (b, w) = y := by simpa using hy
        exact hab),
      chord_left]
  · exact plInterp_eq_chord l₁ l₂ h₁ hab hlt hr.2

/-- Value at a breakpoint, membership form. -/
private lemma plInterp_at_mem :
    ∀ (l : List (Int × Int)),
      l.IsChain (fun p q => p.1 < q.1) → ∀ {x : Int × Int}, x ∈ l →
      plInterp l ((x.1 : ℝ) / (SC : ℝ)) = (x.2 : ℝ) / (SC : ℝ)
  | [], _, _, hx => absurd hx (List.not_mem_nil)
  | [(p, q)], _, x, hx => by
    obtain rfl : x = (p, q) := by simpa using hx
    rfl
  | (p, q) :: (p₂, q₂) :: tl, h, x, hx => by
    obtain ⟨hpp₂, htail⟩ := List.isChain_cons_cons.mp h
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact plInterp_head_val (List.isChain_cons.mp h).1 le_rfl
    · rcases List.mem_cons.mp hx' with rfl | hx''
      · rw [plInterp_cons₂, if_pos le_rfl, if_neg (not_le.mpr (keyR_lt hpp₂)),
          chord_right hpp₂]
      · have hlt : p₂ < x.1 := key_lt_of_mem Prod.fst htail hx''
        rw [plInterp_cons₂, if_neg (not_le.mpr (keyR_lt hlt))]
        exact plInterp_at_mem ((p₂, q₂) :: tl) htail hx'

/-- Global continuity of the clamped PL interpolation of a sorted list. -/
private lemma plInterp_continuous :
    ∀ (l : List (Int × Int)), l.IsChain (fun p q => p.1 < q.1) →
      Continuous (plInterp l)
  | [], _ => by
    have h : plInterp [] = fun _ : ℝ => (0 : ℝ) := rfl
    rw [h]; exact continuous_const
  | [(a, v)], _ => by
    have h : plInterp [(a, v)] = fun _ : ℝ => (v : ℝ) / (SC : ℝ) := rfl
    rw [h]; exact continuous_const
  | (a, v) :: (b, w) :: rest, h => by
    obtain ⟨hab, htail⟩ := List.isChain_cons_cons.mp h
    have ih := plInterp_continuous ((b, w) :: rest) htail
    have hfun : plInterp ((a, v) :: (b, w) :: rest) = fun r =>
        if r ≤ (b : ℝ) / (SC : ℝ) then
          (if r ≤ (a : ℝ) / (SC : ℝ) then (v : ℝ) / (SC : ℝ) else chord a v b w r)
        else plInterp ((b, w) :: rest) r := rfl
    rw [hfun]
    refine Continuous.if_le ?_ ih continuous_id continuous_const ?_
    · refine Continuous.if_le continuous_const chord_continuous
        continuous_id continuous_const ?_
      intro x hx
      rw [hx, chord_left]
    · intro x hx
      rw [hx, if_neg (not_le.mpr (keyR_lt hab)), chord_right hab,
        plInterp_head_val (List.isChain_cons.mp htail).1 le_rfl]

/-- Positivity of the clamped PL interpolation of positive nodal values. -/
private lemma plInterp_pos :
    ∀ (l : List (Int × Int)), l ≠ [] → l.IsChain (fun p q => p.1 < q.1) →
      (∀ x ∈ l, 0 < x.2) → ∀ r : ℝ, 0 < plInterp l r
  | [], hne, _, _, _ => absurd rfl hne
  | [(a, v)], _, _, hpos, r =>
    div_pos (by exact_mod_cast hpos (a, v) (List.mem_singleton_self _)) SCR_pos
  | (a, v) :: (b, w) :: rest, _, h, hpos, r => by
    obtain ⟨hab, htail⟩ := List.isChain_cons_cons.mp h
    rw [plInterp_cons₂]
    split_ifs with h1 h2
    · exact div_pos (by exact_mod_cast hpos (a, v) (by simp)) SCR_pos
    · have hr : r ∈ Icc ((a : ℝ) / (SC : ℝ)) ((b : ℝ) / (SC : ℝ)) :=
        ⟨(not_le.mp h2).le, h1⟩
      have hbox := chord_mem_Icc (v := v) (w := w) hab hr
      have hv : (0 : ℝ) < (v : ℝ) / (SC : ℝ) :=
        div_pos (by exact_mod_cast hpos (a, v) (by simp)) SCR_pos
      have hw : (0 : ℝ) < (w : ℝ) / (SC : ℝ) :=
        div_pos (by exact_mod_cast hpos (b, w) (by simp)) SCR_pos
      exact lt_of_lt_of_le (lt_min hv hw) hbox.1
    · exact plInterp_pos ((b, w) :: rest) (by simp) htail
        (fun x hx => hpos x (List.mem_cons_of_mem _ hx)) r

/-- The left-clamped chord piece is antitone (two-point form). -/
private lemma clamped_chord_anti {a v b w : Int} (hab : a < b) (hwv : w ≤ v)
    {x y : ℝ} (hxy : x ≤ y) :
    (if y ≤ (a : ℝ) / (SC : ℝ) then (v : ℝ) / (SC : ℝ) else chord a v b w y) ≤
      (if x ≤ (a : ℝ) / (SC : ℝ) then (v : ℝ) / (SC : ℝ) else chord a v b w x) := by
  by_cases hy : y ≤ (a : ℝ) / (SC : ℝ)
  · rw [if_pos hy, if_pos (le_trans hxy hy)]
  · rw [if_neg hy]
    by_cases hx : x ≤ (a : ℝ) / (SC : ℝ)
    · rw [if_pos hx]
      calc chord a v b w y ≤ chord a v b w ((a : ℝ) / (SC : ℝ)) :=
            chord_antitone hab hwv (not_le.mp hy).le
        _ = (v : ℝ) / (SC : ℝ) := chord_left
    · rw [if_neg hx]
      exact chord_antitone hab hwv hxy

/-- Global antitonicity of the clamped PL interpolation of a sorted list with
non-increasing values. -/
private lemma plInterp_antitone :
    ∀ (l : List (Int × Int)), l.IsChain (fun p q => p.1 < q.1) →
      l.IsChain (fun p q => q.2 ≤ p.2) → Antitone (plInterp l)
  | [], _, _ => fun _ _ _ => le_rfl
  | [(_, _)], _, _ => fun _ _ _ => le_rfl
  | (a, v) :: (b, w) :: rest, hlt, hval => by
    obtain ⟨hab, hlt'⟩ := List.isChain_cons_cons.mp hlt
    obtain ⟨hwv, hval'⟩ := List.isChain_cons_cons.mp hval
    have ih := plInterp_antitone ((b, w) :: rest) hlt' hval'
    have htail_b : plInterp ((b, w) :: rest) ((b : ℝ) / (SC : ℝ)) = (w : ℝ) / (SC : ℝ) :=
      plInterp_head_val (List.isChain_cons.mp hlt').1 le_rfl
    have hG_b : (if (b : ℝ) / (SC : ℝ) ≤ (a : ℝ) / (SC : ℝ) then (v : ℝ) / (SC : ℝ)
        else chord a v b w ((b : ℝ) / (SC : ℝ))) = (w : ℝ) / (SC : ℝ) := by
      rw [if_neg (not_le.mpr (keyR_lt hab)), chord_right hab]
    intro x y hxy
    rw [plInterp_cons₂, plInterp_cons₂]
    by_cases hy : y ≤ (b : ℝ) / (SC : ℝ)
    · rw [if_pos hy, if_pos (le_trans hxy hy)]
      exact clamped_chord_anti hab hwv hxy
    · rw [if_neg hy]
      by_cases hx : x ≤ (b : ℝ) / (SC : ℝ)
      · rw [if_pos hx]
        have h1 : plInterp ((b, w) :: rest) y ≤ (w : ℝ) / (SC : ℝ) := by
          rw [← htail_b]
          exact ih (not_le.mp hy).le
        have h2 : (w : ℝ) / (SC : ℝ) ≤
            (if x ≤ (a : ℝ) / (SC : ℝ) then (v : ℝ) / (SC : ℝ) else chord a v b w x) := by
          rw [← hG_b]
          exact clamped_chord_anti hab hwv hx
        exact le_trans h1 h2
      · rw [if_neg hx]
        exact ih hxy

/-! ### `stepInterp`: equations and the cell-value lemma -/

private lemma stepInterp_cons₂ (a v b w : Int) (rest : List (Int × Int)) (r : ℝ) :
    stepInterp ((a, v) :: (b, w) :: rest) r =
      if r ≤ (b : ℝ) / (SC : ℝ) then (v : ℝ) / (SC : ℝ)
      else stepInterp ((b, w) :: rest) r := rfl

/-! ### `ChainOK` and structural facts about `nodes` -/

/-- Data-level validity of a certificate chain: nonempty, spans `[λ₀, 1]`
(scaled: `[L0, SC]`), consecutive cells share their boundary node, and per
cell the abscissas strictly increase, the derivative values are positive and
non-increasing, the `M`-values lie strictly between `0` and `SC`, and the
`F`-values satisfy the exact integer trapezoid chain identity.

(`List.IsChain` is definitionally `List.Chain'` in this toolchain.) -/
def ChainOK (cells : List Cell) : Prop :=
  cells ≠ [] ∧
  cells.head?.map (·.n0.lam) = some L0 ∧
  cells.getLast?.map (·.n1.lam) = some SC ∧
  cells.IsChain (fun c c' => c.n1 = c'.n0) ∧
  ∀ c ∈ cells, c.n0.lam < c.n1.lam ∧ 0 < c.n1.d ∧ c.n1.d ≤ c.n0.d ∧
    0 < c.n0.M ∧ c.n0.M < SC ∧ 0 < c.n1.M ∧ c.n1.M < SC ∧ c.n0.M ≤ c.n1.M ∧
    c.n1.F = c.n0.F + (c.n0.d + c.n1.d) * (c.n1.lam - c.n0.lam)

namespace ChainOK

variable {cells : List Cell}

lemma ne_nil (h : ChainOK cells) : cells ≠ [] := h.1

lemma head_lam (h : ChainOK cells) : cells.head?.map (·.n0.lam) = some L0 := h.2.1

lemma last_lam (h : ChainOK cells) : cells.getLast?.map (·.n1.lam) = some SC := h.2.2.1

lemma link (h : ChainOK cells) : cells.IsChain (fun c c' => c.n1 = c'.n0) := h.2.2.2.1

lemma cellFacts (h : ChainOK cells) :
    ∀ c ∈ cells, c.n0.lam < c.n1.lam ∧ 0 < c.n1.d ∧ c.n1.d ≤ c.n0.d ∧
      0 < c.n0.M ∧ c.n0.M < SC ∧ 0 < c.n1.M ∧ c.n1.M < SC ∧ c.n0.M ≤ c.n1.M ∧
      c.n1.F = c.n0.F + (c.n0.d + c.n1.d) * (c.n1.lam - c.n0.lam) := h.2.2.2.2

lemma lam_lt (h : ChainOK cells) {c : Cell} (hc : c ∈ cells) :
    c.n0.lam < c.n1.lam := (h.cellFacts c hc).1

end ChainOK

/-- The node list of a chain, built from a per-cell relation. -/
private lemma nodes_chain (R : Node → Node → Prop) :
    ∀ (cells : List Cell), cells.IsChain (fun c c' => c.n1 = c'.n0) →
      (∀ c ∈ cells, R c.n0 c.n1) → (nodes cells).IsChain R
  | [], _, _ => .nil
  | [c], _, hR =>
    List.isChain_cons_cons.mpr ⟨hR c (List.mem_singleton_self _), .singleton _⟩
  | c₀ :: c₁ :: rest, hlink, hR => by
    obtain ⟨h01, hlink'⟩ := List.isChain_cons_cons.mp hlink
    have ih := nodes_chain R (c₁ :: rest) hlink'
      (fun c hc => hR c (List.mem_cons_of_mem _ hc))
    have heq : nodes (c₀ :: c₁ :: rest) = c₀.n0 :: nodes (c₁ :: rest) := by
      simp [nodes, h01]
    rw [heq]
    refine List.isChain_cons.mpr ⟨?_, ih⟩
    intro y hy
    obtain rfl : c₁.n0 = y := by
      have h2 : nodes (c₁ :: rest) = c₁.n0 :: (c₁ :: rest).map (·.n1) := rfl
      rw [h2] at hy
      simpa using hy
    rw [← h01]
    exact hR c₀ (List.mem_cons_self)

/-- The node abscissas of a valid chain are strictly increasing. -/
private lemma nodes_chain_lam (h : ChainOK cells) :
    (nodes cells).IsChain (fun n n' => n.lam < n'.lam) :=
  nodes_chain _ cells h.link fun c hc => (h.cellFacts c hc).1

/-- The node derivative values of a valid chain are non-increasing. -/
private lemma nodes_chain_d (h : ChainOK cells) :
    (nodes cells).IsChain (fun n n' => n'.d ≤ n.d) :=
  nodes_chain _ cells h.link fun c hc => (h.cellFacts c hc).2.2.1

/-- All node derivative values of a valid chain are positive. -/
private lemma nodes_d_pos (h : ChainOK cells) : ∀ n ∈ nodes cells, 0 < n.d := by
  intro n hn
  obtain ⟨c₀, rest, rfl⟩ := List.exists_cons_of_ne_nil h.ne_nil
  have heq : nodes (c₀ :: rest) = c₀.n0 :: (c₀ :: rest).map (·.n1) := rfl
  rw [heq] at hn
  rcases List.mem_cons.mp hn with rfl | hn'
  · have hfacts := h.cellFacts c₀ (List.mem_cons_self)
    exact lt_of_lt_of_le hfacts.2.1 hfacts.2.2.1
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn'
    exact (h.cellFacts c hc).2.1

/-- Every cell's node pair is adjacent in the node list. -/
private lemma nodes_decomp :
    ∀ {cells : List Cell}, cells.IsChain (fun c c' => c.n1 = c'.n0) →
      ∀ {c : Cell}, c ∈ cells →
      ∃ pre post, nodes cells = pre ++ c.n0 :: c.n1 :: post
  | [], _, c, hc => absurd hc (List.not_mem_nil)
  | c₀ :: rest, hlink, c, hc => by
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact ⟨[], rest.map (·.n1), by simp [nodes]⟩
    · match rest, hc' with
      | c₁ :: rest', hc' =>
        obtain ⟨h01, hlink'⟩ := List.isChain_cons_cons.mp hlink
        obtain ⟨pre, post, hpp⟩ := nodes_decomp hlink' hc'
        refine ⟨c₀.n0 :: pre, post, ?_⟩
        have heq : nodes (c₀ :: c₁ :: rest') = c₀.n0 :: nodes (c₁ :: rest') := by
          simp [nodes, h01]
        rw [heq, hpp, List.cons_append]

/-- The `n0`-abscissas of a valid chain are strictly increasing. -/
private lemma cells_chain_n0 :
    ∀ (cells : List Cell), cells.IsChain (fun c c' => c.n1 = c'.n0) →
      (∀ c ∈ cells, c.n0.lam < c.n1.lam) →
      cells.IsChain (fun c c' => c.n0.lam < c'.n0.lam)
  | [], _, _ => .nil
  | [c], _, _ => .singleton c
  | c₀ :: c₁ :: rest, hlink, hlt => by
    obtain ⟨h01, hlink'⟩ := List.isChain_cons_cons.mp hlink
    refine List.isChain_cons_cons.mpr ⟨?_, cells_chain_n0 (c₁ :: rest) hlink'
      (fun c hc => hlt c (List.mem_cons_of_mem _ hc))⟩
    rw [← h01]
    exact hlt c₀ (List.mem_cons_self)

/-- Chain propagation of a nodal predicate along the cells. -/
private lemma chain_propagate {Q : Node → Prop} :
    ∀ (cells : List Cell), cells.IsChain (fun c c' => c.n1 = c'.n0) →
      (∀ c ∈ cells, Q c.n0 → Q c.n1) →
      (∀ c₀, cells.head? = some c₀ → Q c₀.n0) →
      ∀ c ∈ cells, Q c.n0 ∧ Q c.n1
  | [], _, _, _, c, hc => absurd hc (List.not_mem_nil)
  | c₀ :: rest, hlink, hstep, hhead, c, hc => by
    have hQ0 : Q c₀.n0 := hhead c₀ rfl
    have hQ1 : Q c₀.n1 := hstep c₀ (List.mem_cons_self) hQ0
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact ⟨hQ0, hQ1⟩
    · match rest, hc' with
      | c₁ :: rest', hc' =>
        obtain ⟨h01, hlink'⟩ := List.isChain_cons_cons.mp hlink
        exact chain_propagate (c₁ :: rest') hlink'
          (fun c hc => hstep c (List.mem_cons_of_mem _ hc))
          (fun c₁' hc₁' => by
            obtain rfl : c₁ = c₁' := by simpa using hc₁'
            rw [← h01]; exact hQ1)
          c hc'

/-! ### Continuity of `Dcert` and `Mcert` -/

variable {cells : List Cell}

/-- `Dcert` is continuous on all of `ℝ`. -/
theorem dcont (h : ChainOK cells) : Continuous (Dcert cells) :=
  plInterp_continuous _ ((List.isChain_map _).mpr (nodes_chain_lam h))

/-- `Mcert` is continuous on all of `ℝ`. -/
theorem mcont (h : ChainOK cells) : Continuous (Mcert cells) :=
  plInterp_continuous _ ((List.isChain_map _).mpr (nodes_chain_lam h))

/-! ### FTC: derivative of `Fcert` -/

/-- `Fcert` is differentiable everywhere with derivative `Dcert` (FTC-1). -/
theorem hderiv (h : ChainOK cells) :
    ∀ r : ℝ, HasDerivAt (Fcert cells) (Dcert cells r) r := by
  intro r
  have hD : Continuous (Dcert cells) := dcont h
  have h1 : HasDerivAt (fun u => ∫ t in lam0..u, Dcert cells t) (Dcert cells r) r :=
    (hD.integral_hasStrictDerivAt lam0 r).hasDerivAt
  obtain ⟨c₀, rest, rfl⟩ := List.exists_cons_of_ne_nil h.ne_nil
  exact h1.const_add c₀.n0.FR

/-- Difference of `Fcert` values as an interval integral of `Dcert`. -/
private lemma Fcert_sub (hD : Continuous (Dcert cells)) (x y : ℝ) :
    Fcert cells y - Fcert cells x = ∫ t in x..y, Dcert cells t := by
  simp only [Fcert]
  rw [add_sub_add_left_eq_sub]
  exact intervalIntegral.integral_interval_sub_left
    (hD.intervalIntegrable _ _) (hD.intervalIntegrable _ _)

/-! ### Cell decomposition of the PL interpolants -/

/-- On a cell of a valid chain, the nodal PL interpolant agrees with that
cell's chord (for any nodal value map `f`). -/
private lemma plInterp_nodes_eqOn (f : Node → Int) (h : ChainOK cells)
    {c : Cell} (hc : c ∈ cells) :
    EqOn (plInterp ((nodes cells).map fun n => (n.lam, f n)))
      (chord c.n0.lam (f c.n0) c.n1.lam (f c.n1))
      (Icc c.n0.lamR c.n1.lamR) := by
  obtain ⟨pre, post, hdec⟩ := nodes_decomp h.link hc
  have hlt : c.n0.lam < c.n1.lam := h.lam_lt hc
  have hchainM : (((nodes cells).map fun n => (n.lam, f n))).IsChain
      (fun p q => p.1 < q.1) :=
    (List.isChain_map _).mpr (nodes_chain_lam h)
  have hM : ((nodes cells).map fun n => (n.lam, f n)) =
      (pre.map fun n => (n.lam, f n)) ++
        (c.n0.lam, f c.n0) :: (c.n1.lam, f c.n1) ::
          (post.map fun n => (n.lam, f n)) := by
    rw [hdec]; simp
  rw [hM] at hchainM
  have hpre : ∀ x ∈ (pre.map fun n => (n.lam, f n)), x.1 < c.n0.lam :=
    fun x hx => key_lt_of_append Prod.fst hchainM x hx
  intro r hr
  rw [hM]
  exact plInterp_eqOn_chord _ _ hpre hlt hr

/-! ### Per-cell boxes -/

/-- `Dcert` stays in the cell's derivative box. -/
theorem Dbox (h : ChainOK cells) :
    ∀ c ∈ cells, ∀ r ∈ Icc c.n0.lamR c.n1.lamR,
      Dcert cells r ∈ Icc c.n1.dR c.n0.dR := by
  intro c hc r hr
  have hfacts := h.cellFacts c hc
  have heq : Dcert cells r = chord c.n0.lam c.n0.d c.n1.lam c.n1.d r :=
    plInterp_nodes_eqOn Node.d h hc hr
  rw [heq]
  have hbox := chord_mem_Icc (v := c.n0.d) (w := c.n1.d) hfacts.1 hr
  rwa [min_eq_right (keyR_le hfacts.2.2.1), max_eq_left (keyR_le hfacts.2.2.1)] at hbox

/-- `Mcert` stays in the cell's `M`-box. -/
theorem Mbox (h : ChainOK cells) :
    ∀ c ∈ cells, ∀ r ∈ Icc c.n0.lamR c.n1.lamR,
      Mcert cells r ∈ Icc (min c.n0.MR c.n1.MR) (max c.n0.MR c.n1.MR) := by
  intro c hc r hr
  have heq : Mcert cells r = chord c.n0.lam c.n0.M c.n1.lam c.n1.M r :=
    plInterp_nodes_eqOn Node.M h hc hr
  rw [heq]
  exact chord_mem_Icc (v := c.n0.M) (w := c.n1.M) (h.lam_lt hc) hr

/-! ### Node values of `Fcert` (trapezoid rule + integer chain identity) -/

/-- Per-cell increment of `Fcert`: the trapezoid integral equals the exact
`F`-difference of the endpoints. -/
private lemma Fcert_step (h : ChainOK cells) {c : Cell} (hc : c ∈ cells) :
    Fcert cells c.n1.lamR = Fcert cells c.n0.lamR + (c.n1.FR - c.n0.FR) := by
  have hfacts := h.cellFacts c hc
  have hlt : c.n0.lam < c.n1.lam := hfacts.1
  have hF : c.n1.F = c.n0.F + (c.n0.d + c.n1.d) * (c.n1.lam - c.n0.lam) :=
    hfacts.2.2.2.2.2.2.2.2
  have hD := dcont h
  have hle : c.n0.lamR ≤ c.n1.lamR := (keyR_lt hlt).le
  have hcong : (∫ t in c.n0.lamR..c.n1.lamR, Dcert cells t) =
      ∫ t in c.n0.lamR..c.n1.lamR, chord c.n0.lam c.n0.d c.n1.lam c.n1.d t := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hle]
    exact plInterp_nodes_eqOn Node.d h hc
  have hval : (∫ t in c.n0.lamR..c.n1.lamR, chord c.n0.lam c.n0.d c.n1.lam c.n1.d t) =
      ((c.n0.dR + c.n1.dR) / 2) * (c.n1.lamR - c.n0.lamR) :=
    integral_chord (v := c.n0.d) (w := c.n1.d) hlt
  have hsub := Fcert_sub hD c.n0.lamR c.n1.lamR
  have hFc : (c.n1.F : ℝ) =
      (c.n0.F : ℝ) + ((c.n0.d : ℝ) + (c.n1.d : ℝ)) * ((c.n1.lam : ℝ) - (c.n0.lam : ℝ)) := by
    exact_mod_cast hF
  have e2 : (c.n1.F : ℝ) - (c.n0.F : ℝ) =
      ((c.n0.d : ℝ) + (c.n1.d : ℝ)) * ((c.n1.lam : ℝ) - (c.n0.lam : ℝ)) := by
    rw [hFc]; ring
  have hkey : c.n1.FR - c.n0.FR = ((c.n0.dR + c.n1.dR) / 2) * (c.n1.lamR - c.n0.lamR) := by
    simp only [Node.FR, Node.dR, Node.lamR]
    rw [div_sub_div_same, e2, FSR_eq]
    field_simp
    try ring
  have hfin : Fcert cells c.n1.lamR - Fcert cells c.n0.lamR = c.n1.FR - c.n0.FR := by
    rw [hsub, hcong, hval, ← hkey]
  linarith

/-- `Fcert` interpolates the nodal `F`-values exactly. -/
theorem nodeVals (h : ChainOK cells) :
    ∀ c ∈ cells, Fcert cells c.n0.lamR = c.n0.FR ∧ Fcert cells c.n1.lamR = c.n1.FR := by
  have hstep : ∀ c ∈ cells,
      Fcert cells c.n0.lamR = c.n0.FR → Fcert cells c.n1.lamR = c.n1.FR := by
    intro c hc h0
    have := Fcert_step h hc
    rw [this, h0]
    ring
  have hhead : ∀ c₀, cells.head? = some c₀ → Fcert cells c₀.n0.lamR = c₀.n0.FR := by
    intro c₀ hc₀
    obtain ⟨c₀', rest, rfl⟩ := List.exists_cons_of_ne_nil h.ne_nil
    obtain rfl : c₀ = c₀' := by symm; simpa using hc₀
    have hlam : c₀.n0.lam = L0 := by simpa using h.head_lam
    have hlamR : c₀.n0.lamR = lam0 := by
      simp only [Node.lamR, hlam]
      rfl
    show c₀.n0.FR + (∫ t in lam0..c₀.n0.lamR, Dcert (c₀ :: rest) t) = c₀.n0.FR
    rw [hlamR, intervalIntegral.integral_same, add_zero]
  exact chain_propagate (Q := fun n => Fcert cells n.lamR = n.FR) cells h.link hstep hhead

/-- `Fcert` interpolates every node of the certificate. -/
private lemma Fcert_node (h : ChainOK cells) {n : Node} (hn : n ∈ nodes cells) :
    Fcert cells n.lamR = n.FR := by
  obtain ⟨c₀, rest, rfl⟩ := List.exists_cons_of_ne_nil h.ne_nil
  have heq : nodes (c₀ :: rest) = c₀.n0 :: (c₀ :: rest).map (·.n1) := rfl
  rw [heq] at hn
  rcases List.mem_cons.mp hn with rfl | hn'
  · exact (nodeVals h c₀ (List.mem_cons_self)).1
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn'
    exact (nodeVals h c hc).2

/-- `Dcert` takes the nodal derivative value at every node. -/
private lemma Dcert_node (h : ChainOK cells) {n : Node} (hn : n ∈ nodes cells) :
    Dcert cells n.lamR = n.dR :=
  plInterp_at_mem _ ((List.isChain_map _).mpr (nodes_chain_lam h))
    (List.mem_map_of_mem hn)

/-! ### Step-function values -/

/-- Value of a cell-indexed step function on the half-open cell. -/
private lemma stepInterp_cell (g : Cell → Int) :
    ∀ (cells : List Cell), cells.IsChain (fun c c' => c.n1 = c'.n0) →
      cells.IsChain (fun c c' => c.n0.lam < c'.n0.lam) →
      ∀ c ∈ cells, ∀ r : ℝ, c.n0.lamR < r → r ≤ c.n1.lamR →
      stepInterp (cells.map fun c => (c.n0.lam, g c)) r = (g c : ℝ) / (SC : ℝ)
  | [], _, _, c, hc, _, _, _ => absurd hc (List.not_mem_nil)
  | [c₀], _, _, c, hc, r, h1, h2 => by
    obtain rfl : c = c₀ := by simpa using hc
    rfl
  | c₀ :: c₁ :: rest, hlink, hsort, c, hc, r, h1, h2 => by
    obtain ⟨hl01, hlink'⟩ := List.isChain_cons_cons.mp hlink
    obtain ⟨hs01, hsort'⟩ := List.isChain_cons_cons.mp hsort
    rcases List.mem_cons.mp hc with rfl | hc'
    · have hr : r ≤ (c₁.n0.lam : ℝ) / (SC : ℝ) := by
        rw [← hl01]
        exact h2
      rw [List.map_cons, List.map_cons, stepInterp_cons₂, if_pos hr]
    · have hge : c₁.n0.lam ≤ c.n0.lam := by
        rcases List.mem_cons.mp hc' with rfl | hc''
        · exact le_refl _
        · exact (key_lt_of_mem (fun c : Cell => c.n0.lam) hsort' hc'').le
      have hgt : (c₁.n0.lam : ℝ) / (SC : ℝ) < r := lt_of_le_of_lt (keyR_le hge) h1
      rw [List.map_cons, List.map_cons, stepInterp_cons₂, if_neg (not_le.mpr hgt)]
      exact stepInterp_cell g (c₁ :: rest) hlink' hsort' c hc' r h1 h2

/-- `Xcert` equals the cell constant on the half-open cell. -/
theorem Xval (h : ChainOK cells) :
    ∀ c ∈ cells, ∀ r ∈ Ioc c.n0.lamR c.n1.lamR,
      Xcert cells r = (c.X : ℝ) / (SC : ℝ) := by
  intro c hc r hr
  exact stepInterp_cell Cell.X cells h.link
    (cells_chain_n0 cells h.link fun c hc => h.lam_lt hc) c hc r hr.1 hr.2

/-- `Ycert` equals the cell constant on the half-open cell. -/
theorem Yval (h : ChainOK cells) :
    ∀ c ∈ cells, ∀ r ∈ Ioc c.n0.lamR c.n1.lamR,
      Ycert cells r = (c.Y : ℝ) / (SC : ℝ) := by
  intro c hc r hr
  exact stepInterp_cell Cell.Y cells h.link
    (cells_chain_n0 cells h.link fun c hc => h.lam_lt hc) c hc r hr.1 hr.2

/-- On the tail `(-∞, λ₀]` all four data functions take the head cell's
`n0`-values. -/
theorem tailVals (h : ChainOK cells) {c₀ : Cell} (hc₀ : cells.head? = some c₀) :
    ∀ r ≤ lam0,
      Dcert cells r = c₀.n0.dR ∧ Mcert cells r = c₀.n0.MR ∧
      Xcert cells r = (c₀.X : ℝ) / (SC : ℝ) ∧ Ycert cells r = (c₀.Y : ℝ) / (SC : ℝ) := by
  obtain ⟨c₀', rest, rfl⟩ := List.exists_cons_of_ne_nil h.ne_nil
  obtain rfl : c₀ = c₀' := by symm; simpa using hc₀
  intro r hr
  have hlam : c₀.n0.lam = L0 := by simpa using h.head_lam
  have hr' : r ≤ (c₀.n0.lam : ℝ) / (SC : ℝ) := by
    rw [hlam]
    exact hr
  have hlt0 : c₀.n0.lam < c₀.n1.lam := h.lam_lt (List.mem_cons_self)
  have hnodes : nodes (c₀ :: rest) = c₀.n0 :: c₀.n1 :: rest.map (·.n1) := by
    simp [nodes]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show plInterp ((nodes (c₀ :: rest)).map fun n => (n.lam, n.d)) r = c₀.n0.dR
    rw [hnodes, List.map_cons, List.map_cons]
    exact plInterp_head_val
      (fun y hy => by
        obtain rfl : (c₀.n1.lam, c₀.n1.d) = y := by simpa using hy
        exact hlt0) hr'
  · show plInterp ((nodes (c₀ :: rest)).map fun n => (n.lam, n.M)) r = c₀.n0.MR
    rw [hnodes, List.map_cons, List.map_cons]
    exact plInterp_head_val
      (fun y hy => by
        obtain rfl : (c₀.n1.lam, c₀.n1.M) = y := by simpa using hy
        exact hlt0) hr'
  · show stepInterp ((c₀ :: rest).map fun c => (c.n0.lam, c.X)) r = (c₀.X : ℝ) / (SC : ℝ)
    cases rest with
    | nil => rfl
    | cons c₁ rest' =>
      have h01 : c₀.n1 = c₁.n0 := (List.isChain_cons_cons.mp h.link).1
      have hr₁ : r ≤ (c₁.n0.lam : ℝ) / (SC : ℝ) := by
        rw [← h01]
        exact le_trans hr' (keyR_lt hlt0).le
      rw [List.map_cons, List.map_cons, stepInterp_cons₂, if_pos hr₁]
  · show stepInterp ((c₀ :: rest).map fun c => (c.n0.lam, c.Y)) r = (c₀.Y : ℝ) / (SC : ℝ)
    cases rest with
    | nil => rfl
    | cons c₁ rest' =>
      have h01 : c₀.n1 = c₁.n0 := (List.isChain_cons_cons.mp h.link).1
      have hr₁ : r ≤ (c₁.n0.lam : ℝ) / (SC : ℝ) := by
        rw [← h01]
        exact le_trans hr' (keyR_lt hlt0).le
      rw [List.map_cons, List.map_cons, stepInterp_cons₂, if_pos hr₁]

/-! ### Positivity, antitonicity, monotonicity -/

/-- `Dcert` is positive everywhere. -/
theorem Dpos (h : ChainOK cells) : ∀ r : ℝ, 0 < Dcert cells r := by
  intro r
  refine plInterp_pos _ ?_ ((List.isChain_map _).mpr (nodes_chain_lam h)) ?_ r
  · obtain ⟨c₀, rest, rfl⟩ := List.exists_cons_of_ne_nil h.ne_nil
    simp [nodes]
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
    exact nodes_d_pos h n hn

/-- `Dcert` is non-increasing on all of `ℝ` (concavity of `Fcert`). -/
theorem Danti (h : ChainOK cells) : Antitone (Dcert cells) :=
  plInterp_antitone _ ((List.isChain_map _).mpr (nodes_chain_lam h))
    ((List.isChain_map _).mpr (nodes_chain_d h))

/-- `Fcert` is monotone on all of `ℝ`. -/
theorem Fmono (h : ChainOK cells) : Monotone (Fcert cells) := by
  intro x y hxy
  have hD := dcont h
  have hsub := Fcert_sub hD x y
  have hnn : 0 ≤ ∫ t in x..y, Dcert cells t :=
    intervalIntegral.integral_nonneg hxy fun t _ => (Dpos h t).le
  linarith

/-! ### Tangent bound and the value at 1 -/

/-- The tangent line at every node dominates `Fcert` (concavity via integral
comparison). -/
theorem tangentUB (h : ChainOK cells) : SplineTangentUB cells := by
  intro n hn s _
  have hD := dcont h
  have hFu : Fcert cells n.lamR = n.FR := Fcert_node h hn
  have hDu : Dcert cells n.lamR = n.dR := Dcert_node h hn
  have hanti := Danti h
  rcases le_total n.lamR s with hus | hsu
  · have hmono : (∫ t in n.lamR..s, Dcert cells t) ≤ ∫ t in n.lamR..s, n.dR := by
      refine intervalIntegral.integral_mono_on hus (hD.intervalIntegrable _ _)
        intervalIntegrable_const fun t ht => ?_
      rw [← hDu]
      exact hanti ht.1
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hsub := Fcert_sub hD n.lamR s
    rw [hFu] at hsub
    linarith
  · have hmono : (∫ t in s..n.lamR, (n.dR : ℝ)) ≤ ∫ t in s..n.lamR, Dcert cells t := by
      refine intervalIntegral.integral_mono_on hsu intervalIntegrable_const
        (hD.intervalIntegrable _ _) fun t ht => ?_
      rw [← hDu]
      exact hanti ht.2
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hsub := Fcert_sub hD s n.lamR
    rw [hFu] at hsub
    have hring : (n.lamR - s) * n.dR = -((s - n.lamR) * n.dR) := by ring
    linarith

/-- A chord evaluated at a convex combination of its endpoints is the convex
combination of its values. -/
private lemma chord_at_comb {a v b w : Int} (hab : a < b) (t : ℝ) :
    chord a v b w ((1 - t) * ((a : ℝ) / (SC : ℝ)) + t * ((b : ℝ) / (SC : ℝ))) =
      (1 - t) * ((v : ℝ) / (SC : ℝ)) + t * ((w : ℝ) / (SC : ℝ)) := by
  have hba : ((b : ℝ)) - (a : ℝ) ≠ 0 := by
    have : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    linarith
  unfold chord
  field_simp
  ring

/-- Convex combinations of a cell's endpoints stay in the cell. -/
private lemma comb_mem_Icc {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 - t) * a + t * b ∈ Icc a b := by
  constructor
  · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hab)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hab)]

/-- `Fcert` lies above the chord of each cell (concavity): the convex
combination of nodal values is dominated by the value at the convex
combination. -/
theorem Fchord (h : ChainOK cells) :
    ∀ c ∈ cells, ∀ t ∈ Icc (0 : ℝ) 1,
      (1 - t) * c.n0.FR + t * c.n1.FR ≤
        Fcert cells ((1 - t) * c.n0.lamR + t * c.n1.lamR) := by
  intro c hc t ht
  have hD := dcont h
  have hanti := Danti h
  have hab : c.n0.lamR ≤ c.n1.lamR := (keyR_lt (h.lam_lt hc)).le
  obtain ⟨har, hrb⟩ := comb_mem_Icc hab ht
  have hvals := nodeVals h c hc
  -- lower bound for the left integral, upper bound for the right integral
  have h1 : (((1 - t) * c.n0.lamR + t * c.n1.lamR) - c.n0.lamR) *
      Dcert cells ((1 - t) * c.n0.lamR + t * c.n1.lamR) ≤
      ∫ u in c.n0.lamR..((1 - t) * c.n0.lamR + t * c.n1.lamR), Dcert cells u := by
    have hmono : (∫ u in c.n0.lamR..((1 - t) * c.n0.lamR + t * c.n1.lamR),
        Dcert cells ((1 - t) * c.n0.lamR + t * c.n1.lamR)) ≤
        ∫ u in c.n0.lamR..((1 - t) * c.n0.lamR + t * c.n1.lamR), Dcert cells u := by
      refine intervalIntegral.integral_mono_on har intervalIntegrable_const
        (hD.intervalIntegrable _ _) fun u hu => ?_
      exact hanti hu.2
    rwa [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have h2 : (∫ u in ((1 - t) * c.n0.lamR + t * c.n1.lamR)..c.n1.lamR, Dcert cells u) ≤
      (c.n1.lamR - ((1 - t) * c.n0.lamR + t * c.n1.lamR)) *
        Dcert cells ((1 - t) * c.n0.lamR + t * c.n1.lamR) := by
    have hmono : (∫ u in ((1 - t) * c.n0.lamR + t * c.n1.lamR)..c.n1.lamR,
        Dcert cells u) ≤
        ∫ u in ((1 - t) * c.n0.lamR + t * c.n1.lamR)..c.n1.lamR,
          Dcert cells ((1 - t) * c.n0.lamR + t * c.n1.lamR) := by
      refine intervalIntegral.integral_mono_on hrb (hD.intervalIntegrable _ _)
        intervalIntegrable_const fun u hu => ?_
      exact hanti hu.1
    rwa [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hIa := Fcert_sub hD c.n0.lamR ((1 - t) * c.n0.lamR + t * c.n1.lamR)
  have hIb := Fcert_sub hD ((1 - t) * c.n0.lamR + t * c.n1.lamR) c.n1.lamR
  rw [hvals.1] at hIa
  rw [hvals.2] at hIb
  -- weighted combination
  have e1 := mul_le_mul_of_nonneg_left h1 (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t)
  have e2 := mul_le_mul_of_nonneg_left h2 ht.1
  have hzero : (1 - t) * ((((1 - t) * c.n0.lamR + t * c.n1.lamR) - c.n0.lamR) *
        Dcert cells ((1 - t) * c.n0.lamR + t * c.n1.lamR)) -
      t * ((c.n1.lamR - ((1 - t) * c.n0.lamR + t * c.n1.lamR)) *
        Dcert cells ((1 - t) * c.n0.lamR + t * c.n1.lamR)) = 0 := by
    ring
  rw [← hIa] at e1
  rw [← hIb] at e2
  nlinarith [e1, e2, hzero]

/-- `Mcert` is exactly the chord on each cell: at a convex combination of the
cell's endpoints it takes the convex combination of the nodal `M`-values. -/
theorem Mlin (h : ChainOK cells) :
    ∀ c ∈ cells, ∀ t ∈ Icc (0 : ℝ) 1,
      Mcert cells ((1 - t) * c.n0.lamR + t * c.n1.lamR) =
        (1 - t) * c.n0.MR + t * c.n1.MR := by
  intro c hc t ht
  have hab : c.n0.lamR ≤ c.n1.lamR := (keyR_lt (h.lam_lt hc)).le
  have hr : (1 - t) * c.n0.lamR + t * c.n1.lamR ∈ Icc c.n0.lamR c.n1.lamR :=
    comb_mem_Icc hab ht
  have heq : Mcert cells ((1 - t) * c.n0.lamR + t * c.n1.lamR) =
      chord c.n0.lam c.n0.M c.n1.lam c.n1.M ((1 - t) * c.n0.lamR + t * c.n1.lamR) :=
    plInterp_nodes_eqOn Node.M h hc hr
  rw [heq]
  show chord c.n0.lam c.n0.M c.n1.lam c.n1.M
      ((1 - t) * c.n0.lamR + t * c.n1.lamR) = (1 - t) * c.n0.MR + t * c.n1.MR
  simp only [Node.lamR, Node.MR]
  exact chord_at_comb (h.lam_lt hc) t

/-- The value of `Fcert` at `1` is the last node's `F`-value. -/
theorem F1val (h : ChainOK cells) {cN : Cell} (hN : cells.getLast? = some cN) :
    Fcert cells 1 = cN.n1.FR := by
  have hmem : cN ∈ cells := List.mem_of_getLast? hN
  have hlam : cN.n1.lam = SC := by
    have hl := h.last_lam
    rw [hN] at hl
    simpa using hl
  have h1 : cN.n1.lamR = 1 := by
    simp only [Node.lamR, hlam]
    exact div_self SCR_ne
  rw [← h1]
  exact (nodeVals h cN hmem).2

end Bootstrap2
end RamseyLean

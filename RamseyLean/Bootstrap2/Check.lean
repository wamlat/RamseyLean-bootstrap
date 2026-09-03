import RamseyLean.Bootstrap2.Defs
import RamseyLean.Bootstrap.CertCheck
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Bootstrap2: kernel-checkable certificate cell checker

Bool-valued checker for the spline certificate of `SPEC.md` (§3, §5) together
with its soundness theorems.  Interval arithmetic is the scaled-`Int` backend
`RamseyLean.Analysis.FixedPointInterval` plus the `logPos`/`expNegBig`
reductions of `RamseyLean.Bootstrap.CertCheck`.

Per cell, `checkCell` verifies (all `&&`-ed, kernel-decidable):
* chain-local integer conditions (§2): `0 < n0.lam < n1.lam`, `0 < n1.d ≤ n0.d`,
  the exact `F`-chain identity, `0 < M < SC` at both nodes, `0 < X,Y < SC`,
  witness sanity;
* safety predicates for every interval evaluation;
* the interval checks (P)(XLE)(A1)(A2)(B1)(B2)(MMONO)(PSI0)(PSI1); the
  ψ-slack is verified in two-endpoint form: node values of ψ at both cell
  endpoints, each reduced by the `t(1-t) ≤ 1/4` quadratic dip of the
  `r·log M` chord.

`checkCell_sound` turns a passing cell into `LadderHypsAt` at every `r` in the
cell, abstractly over real functions `F D M X Y` satisfying the interface
provided by the analysis layer (`Spline.lean`).

Global passes: `checkChain` (tiling of `[λ₀, 1]`), `checkWitnesses`
(two-pointer merge validating that every tangent witness is a certificate
node), `checkTail` (T1).  The generated data files state their kernel facts
about `checkCellFast`, a `let`-sharing twin with `checkCellFast = checkCell`
by `rfl`.

The Python generator mirrors `checkCellFast` bit-exactly; see `SPEC.md`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace RamseyLean
namespace Bootstrap2

open Set FixedPointInterval FixedPointInterval.Interval
open Bootstrap.CertCheck (logPos logPosSafe expNegBig logPos_contains
  expNegBig_contains value_pos value_nonneg value_nonpos value_le_value
  value_lt_value value_neg' value_lt_one value_le_one value_scale contains_one)

/-! ### Scale bridges (`SC`/`FS` of `Bootstrap2.Defs` vs `scale` of the
interval library) -/

theorem SC_eq_scale : SC = scale := by decide

theorem contains_one_SC : (point SC).Contains 1 := by
  rw [SC_eq_scale]; exact contains_one

theorem value_div_SC (z : ℤ) : (z : ℝ) / (SC : ℝ) = value z := by
  unfold value
  rw [SC_eq_scale]

theorem Node.lamR_eq (n : Node) : n.lamR = value n.lam := by
  unfold Node.lamR value
  rw [SC_eq_scale]

theorem Node.dR_eq (n : Node) : n.dR = value n.d := by
  unfold Node.dR value
  rw [SC_eq_scale]

theorem Node.MR_eq (n : Node) : n.MR = value n.M := by
  unfold Node.MR value
  rw [SC_eq_scale]

theorem value_min' (a b : ℤ) : value (min a b) = min (value a) (value b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (value_le_value h)]
  · rw [min_eq_right h, min_eq_right (value_le_value h)]

/-! ### `fpt`: downscaling an `F`-value (scale `FS`) into an `SC`-interval -/

/-- Directed-rounding enclosure of `f / FS` at interval scale `SC`
(SPEC §1; `/` is `Int.ediv` = floor division for the positive divisor,
i.e. Python `//`). -/
def fpt (f : Int) : Interval := ⟨f / (2 * SC), -((-f) / (2 * SC))⟩

theorem two_SC_pos : (0 : ℤ) < 2 * SC := by decide

theorem cast_two_SC_mul_scale : ((2 * SC : ℤ) : ℝ) * (scale : ℝ) = (FS : ℝ) := by
  norm_num [SC, FS, scale]

/-- Soundness of `fpt`: it encloses `f / FS` as a real number. -/
theorem fpt_contains (f : Int) : (fpt f).Contains ((f : ℝ) / (FS : ℝ)) := by
  constructor
  · show value (f / (2 * SC)) ≤ (f : ℝ) / (FS : ℝ)
    have h := cast_ediv_le_div (a := f) two_SC_pos
    have h2 : value (f / (2 * SC)) ≤ ((f : ℝ) / ((2 * SC : ℤ) : ℝ)) / (scale : ℝ) := by
      unfold value
      exact div_le_div_of_nonneg_right h scale_pos_real.le
    calc value (f / (2 * SC)) ≤ ((f : ℝ) / ((2 * SC : ℤ) : ℝ)) / (scale : ℝ) := h2
      _ = (f : ℝ) / (FS : ℝ) := by rw [div_div, cast_two_SC_mul_scale]
  · show (f : ℝ) / (FS : ℝ) ≤ value (-((-f) / (2 * SC)))
    have h := div_le_cast_ceil (a := f) two_SC_pos
    have h2 : ((f : ℝ) / ((2 * SC : ℤ) : ℝ)) / (scale : ℝ) ≤
        value (-((-f) / (2 * SC))) := by
      unfold value
      exact div_le_div_of_nonneg_right h scale_pos_real.le
    calc (f : ℝ) / (FS : ℝ) = ((f : ℝ) / ((2 * SC : ℤ) : ℝ)) / (scale : ℝ) := by
          rw [div_div, cast_two_SC_mul_scale]
      _ ≤ value (-((-f) / (2 * SC))) := h2

theorem fpt_contains_FR (n : Node) : (fpt n.F).Contains n.FR := fpt_contains n.F

/-! ### Named per-cell interval expressions (SPEC §3)

The generator mirrors these bit-exactly (through `checkCellFast`). -/

/-- `Mlo = min(n0.M, n1.M)` (no monotonicity of `M` is assumed). -/
def MloI (c : Cell) : Int := min c.n0.M c.n1.M

/-- `Mhi = max(n0.M, n1.M)`. -/
def MhiI (c : Cell) : Int := max c.n0.M c.n1.M

/-- Box interval for `D` over the cell (concavity: `n1.d ≤ n0.d`). -/
def DIc (c : Cell) : Interval := ⟨c.n1.d, c.n0.d⟩

/-- Box interval for `M` over the cell. -/
def MIc (c : Cell) : Interval := ⟨MloI c, MhiI c⟩

/-- Enclosure of `log (X/SC)`. -/
def lXc (c : Cell) : Interval := logPos (point c.X)

/-- Enclosure of `log (Y/SC)`. -/
def lYc (c : Cell) : Interval := logPos (point c.Y)

/-- Enclosure of `log (n0.M/SC)` (= `log (Mlo/SC)` given (MMONO)). -/
def lM0c (c : Cell) : Interval := logPos (point c.n0.M)

/-- Enclosure of `log (n1.M/SC)`. -/
def lM1c (c : Cell) : Interval := logPos (point c.n1.M)

/-- Enclosure of `1 - M` over the box. -/
def oneMinusMc (c : Cell) : Interval := add (point SC) (neg (MIc c))

/-- Enclosure of `1 - e^{-D}` over the box. -/
def pIc (c : Cell) : Interval := add (point SC) (neg (expNegBig (DIc c)))

/-- Enclosure of `log [(1-e^{-D})^{1/(1-M)} (1-M)]` over the box. -/
def rhsLogc (c : Cell) : Interval :=
  add (mul (log 13 (pIc c)) (inv (oneMinusMc c))) (log 13 (oneMinusMc c))

/-- Enclosure of `S̄a = F(u_a) - u_a d(u_a)` (witness `wa`). -/
def SaI (c : Cell) : Interval :=
  add (fpt c.wa.F) (neg (mul (point c.wa.lam) (point c.wa.d)))

/-- Enclosure of `S̄b` (witness `wb`). -/
def SbI (c : Cell) : Interval :=
  add (fpt c.wb.F) (neg (mul (point c.wb.lam) (point c.wb.d)))

/-- Endpoint value of `ψ(r) = F r + (log X + r log M + r log Y)/2` at the
left node `r = n0.lamR` (where `F` and `M` take the node values exactly). -/
def psiLo0I (c : Cell) : Interval :=
  add (fpt c.n0.F)
    (divNat (add (add (lXc c) (mul (point c.n0.lam) (lM0c c)))
      (mul (point c.n0.lam) (lYc c))) 2)

/-- Endpoint value of `ψ` at the right node `r = n1.lamR`. -/
def psiLo1I (c : Cell) : Interval :=
  add (fpt c.n1.F)
    (divNat (add (add (lXc c) (mul (point c.n1.lam) (lM1c c)))
      (mul (point c.n1.lam) (lYc c))) 2)

/-- The quadratic dip `(log M₁ − log M₀)(λ₁ − λ₀)/8` of the `r·(log M)` chord:
inside the cell, `ψ(r)` exceeds the linear interpolant of its endpoint values
minus `t(1−t)(λ₁−λ₀)(log M₁ − log M₀)/2 ≥ −dip` since `t(1−t) ≤ 1/4`. -/
def dipI (c : Cell) : Interval :=
  divNat (mul (add (lM1c c) (neg (lM0c c)))
    (add (point c.n1.lam) (neg (point c.n0.lam)))) 8

/-! ### The per-cell Boolean check (SPEC §2 chain-local + §3) -/

/-- The full per-cell check (reference version; the data files use the
evaluation twin `checkCellFast`).  Flat `&&`-chain, in SPEC order:
integer chain-local conditions, safety predicates, then
(XLE)(A1)(A2)(B1)(B2)(MMONO)(PSI0)(PSI1). -/
def checkCell (c : Cell) : Bool :=
  -- chain-local integer conditions (§2)
  decide (0 < c.n0.lam) && decide (c.n0.lam < c.n1.lam) &&
  decide (0 < c.n1.d) && decide (c.n1.d ≤ c.n0.d) &&
  decide (c.n1.F = c.n0.F + (c.n0.d + c.n1.d) * (c.n1.lam - c.n0.lam)) &&
  decide (0 < c.n0.M) && decide (c.n0.M < SC) &&
  decide (0 < c.n1.M) && decide (c.n1.M < SC) &&
  -- (P) cell constants
  decide (0 < c.X) && decide (c.X < SC) && decide (0 < c.Y) && decide (c.Y < SC) &&
  -- witness sanity
  decide (0 < c.wa.lam) && decide (c.wa.lam ≤ SC) && decide (0 < c.wa.d) &&
  decide (0 < c.wb.lam) && decide (c.wb.lam ≤ SC) && decide (0 < c.wb.d) &&
  -- safety predicates
  logPosSafe (point c.X) && logPosSafe (point c.Y) &&
  logPosSafe (point c.n0.M) && logPosSafe (point c.n1.M) &&
  expSafe 16 (divNat (neg (DIc c)) 16) &&
  logSafe 13 (pIc c) && logSafe 13 (oneMinusMc c) &&
  positive (pIc c) && positive (oneMinusMc c) &&
  -- (XLE)
  decide ((lXc c).hi ≤ (rhsLogc c).lo) &&
  -- (A1)
  decide ((add (SaI c) (lXc c)).hi ≤ 0) &&
  -- (A2)
  decide ((add (add (SaI c) (point c.wa.d)) (add (lXc c) (lYc c))).hi ≤ 0) &&
  -- (B1)
  decide ((add (SbI c) (lYc c)).hi ≤ 0) &&
  -- (B2)
  decide ((add (add (SbI c) (point c.wb.d)) (add (lYc c) (lXc c))).hi ≤ 0) &&
  -- (MMONO)
  decide (c.n0.M ≤ c.n1.M) &&
  -- (PSI0)
  decide (0 < (add (psiLo0I c) (neg (dipI c))).lo) &&
  -- (PSI1)
  decide (0 < (add (psiLo1I c) (neg (dipI c))).lo)

/-- The integer chain-local facts of a passing cell, as `Prop`s. -/
theorem checkCell_int_facts (c : Cell) (h : checkCell c = true) :
    0 < c.n0.lam ∧ c.n0.lam < c.n1.lam ∧
    0 < c.n1.d ∧ c.n1.d ≤ c.n0.d ∧
    c.n1.F = c.n0.F + (c.n0.d + c.n1.d) * (c.n1.lam - c.n0.lam) ∧
    0 < c.n0.M ∧ c.n0.M < SC ∧ 0 < c.n1.M ∧ c.n1.M < SC ∧
    0 < c.X ∧ c.X < SC ∧ 0 < c.Y ∧ c.Y < SC ∧
    0 < c.wa.lam ∧ c.wa.lam ≤ SC ∧ 0 < c.wa.d ∧
    0 < c.wb.lam ∧ c.wb.lam ≤ SC ∧ 0 < c.wb.d := by
  simp only [checkCell, Bool.and_eq_true, decide_eq_true_eq, positive,
    and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    h16, h17, h18, h19, -⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    h16, h17, h18, h19⟩

/-- (MMONO): `M` is non-decreasing across the cell's nodes. -/
theorem checkCell_M_mono (c : Cell) (h : checkCell c = true) :
    c.n0.M ≤ c.n1.M := by
  simp only [checkCell, Bool.and_eq_true, decide_eq_true_eq, positive,
    and_assoc] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMM, -, -⟩ := h
  exact hMM

/-! ### Per-cell soundness -/

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
/-- Soundness of `checkCell`: a passing cell yields the pointwise ladder
hypotheses at every `r` in the (half-open) cell, for any real functions
`F D M X Y` satisfying the analysis-layer interface: `F` matches the node
values at both endpoints (`hFn0`/`hFn1`, kept for the glue layer), is
non-decreasing on the cell and lies above its chord (concavity), the tangent
lines at the two witnesses dominate `F` on `(0,1]`, `D` stays in the cell
box, `M` is the linear interpolant of the node values, and `X`/`Y` are the
cell constants. -/
theorem checkCell_sound (c : Cell) (hchk : checkCell c = true)
    (F D M X Y : ℝ → ℝ)
    (hFn0 : F c.n0.lamR = c.n0.FR)
    (hFn1 : F c.n1.lamR = c.n1.FR)
    (hFge : ∀ r ∈ Set.Ioc c.n0.lamR c.n1.lamR, F c.n0.lamR ≤ F r)
    (hFchord : ∀ t ∈ Set.Icc (0:ℝ) 1,
      (1 - t) * c.n0.FR + t * c.n1.FR ≤
        F ((1 - t) * c.n0.lamR + t * c.n1.lamR))
    (htanA : ∀ s ∈ Set.Ioc (0:ℝ) 1, F s ≤ c.wa.FR + (s - c.wa.lamR) * c.wa.dR)
    (htanB : ∀ s ∈ Set.Ioc (0:ℝ) 1, F s ≤ c.wb.FR + (s - c.wb.lamR) * c.wb.dR)
    (hFnn : 0 ≤ F c.n0.lamR)
    (hD : ∀ r ∈ Set.Ioc c.n0.lamR c.n1.lamR, D r ∈ Set.Icc c.n1.dR c.n0.dR)
    (hMlin : ∀ t ∈ Set.Icc (0:ℝ) 1,
      M ((1 - t) * c.n0.lamR + t * c.n1.lamR) = (1 - t) * c.n0.MR + t * c.n1.MR)
    (hX : ∀ r ∈ Set.Ioc c.n0.lamR c.n1.lamR, X r = (c.X : ℝ) / (SC : ℝ))
    (hY : ∀ r ∈ Set.Ioc c.n0.lamR c.n1.lamR, Y r = (c.Y : ℝ) / (SC : ℝ)) :
    ∀ r ∈ Set.Ioc c.n0.lamR c.n1.lamR, r ≤ 1 → LadderHypsAt F D M X Y r := by
  clear hFn0 hFn1  -- endpoint equalities are part of the glue interface only
  simp only [checkCell, Bool.and_eq_true, decide_eq_true_eq, positive,
    and_assoc] at hchk
  obtain ⟨hlam0, hlam01, hd1, _hd10, _hFchain, hM00, _hM0SC, hM10, hM1SC,
    hX0, hXSC, hY0, hYSC, _hwal0, _hwalSC, _hwad0, _hwbl0, _hwblSC, _hwbd0,
    hsafeX, hsafeY, hsafeM0, hsafeM1, hsafeE, hsafeP, hsafe1M, _hpIpos, h1Mpos,
    hXLE, hA1, hA2, hB1, hB2, hMM, hPSI0, hPSI1⟩ := hchk
  rw [SC_eq_scale] at hXSC hYSC hM1SC
  -- real-valued facts about the cell constants
  have hXv : (0:ℝ) < value c.X := value_pos hX0
  have hXv1 : value c.X < 1 := value_lt_one hXSC
  have hYv : (0:ℝ) < value c.Y := value_pos hY0
  have hYv1 : value c.Y < 1 := value_lt_one hYSC
  have hM0R : (0:ℝ) < value c.n0.M := value_pos hM00
  have hM1R : (0:ℝ) < value c.n1.M := value_pos hM10
  have hM1R1 : value c.n1.M < 1 := value_lt_one hM1SC
  have hM01 : value c.n0.M ≤ value c.n1.M := value_le_value hMM
  have hL01 : Real.log (value c.n0.M) ≤ Real.log (value c.n1.M) :=
    Real.log_le_log hM0R hM01
  set x := Real.log (value c.X) with hxdef
  set y := Real.log (value c.Y) with hydef
  have hxneg : x < 0 := Real.log_neg hXv hXv1
  have hyneg : y < 0 := Real.log_neg hYv hYv1
  -- log enclosures for the cell constants
  have hlX : (lXc c).Contains x := logPos_contains (contains_point c.X) hXv hsafeX
  have hlY : (lYc c).Contains y := logPos_contains (contains_point c.Y) hYv hsafeY
  have hlM0 : (lM0c c).Contains (Real.log (value c.n0.M)) :=
    logPos_contains (contains_point c.n0.M) hM0R hsafeM0
  have hlM1 : (lM1c c).Contains (Real.log (value c.n1.M)) :=
    logPos_contains (contains_point c.n1.M) hM1R hsafeM1
  -- witness S̄ enclosures and the (A)/(B) real inequalities
  have hSa : (SaI c).Contains (c.wa.FR - c.wa.lamR * c.wa.dR) := by
    have h := (fpt_contains_FR c.wa).add
      (((contains_point c.wa.lam).mul (contains_point c.wa.d)).neg)
    simpa [SaI, sub_eq_add_neg, Node.lamR_eq, Node.dR_eq] using h
  have hSb : (SbI c).Contains (c.wb.FR - c.wb.lamR * c.wb.dR) := by
    have h := (fpt_contains_FR c.wb).add
      (((contains_point c.wb.lam).mul (contains_point c.wb.d)).neg)
    simpa [SbI, sub_eq_add_neg, Node.lamR_eq, Node.dR_eq] using h
  have hSaD : (add (SaI c) (point c.wa.d)).Contains
      (c.wa.FR - c.wa.lamR * c.wa.dR + c.wa.dR) := by
    have h := hSa.add (contains_point c.wa.d)
    rwa [← Node.dR_eq] at h
  have hSbD : (add (SbI c) (point c.wb.d)).Contains
      (c.wb.FR - c.wb.lamR * c.wb.dR + c.wb.dR) := by
    have h := hSb.add (contains_point c.wb.d)
    rwa [← Node.dR_eq] at h
  have hA1R : c.wa.FR - c.wa.lamR * c.wa.dR + x ≤ 0 := by
    have h := (hSa.add hlX).2
    have h0 := value_nonpos hA1
    linarith
  have hA2R : c.wa.FR - c.wa.lamR * c.wa.dR + c.wa.dR + (x + y) ≤ 0 := by
    have h := (hSaD.add (hlX.add hlY)).2
    have h0 := value_nonpos hA2
    linarith
  have hB1R : c.wb.FR - c.wb.lamR * c.wb.dR + y ≤ 0 := by
    have h := (hSb.add hlY).2
    have h0 := value_nonpos hB1
    linarith
  have hB2R : c.wb.FR - c.wb.lamR * c.wb.dR + c.wb.dR + (y + x) ≤ 0 := by
    have h := (hSbD.add (hlY.add hlX)).2
    have h0 := value_nonpos hB2
    linarith
  -- endpoint ψ bounds (PSI0)/(PSI1), with the dip subtracted
  have hL0pt : (point c.n0.lam).Contains c.n0.lamR := by
    rw [Node.lamR_eq]; exact contains_point c.n0.lam
  have hL1pt : (point c.n1.lam).Contains c.n1.lamR := by
    rw [Node.lamR_eq]; exact contains_point c.n1.lam
  have hab : c.n0.lamR < c.n1.lamR := by
    rw [Node.lamR_eq, Node.lamR_eq]; exact value_lt_value hlam01
  have hba : (0:ℝ) < c.n1.lamR - c.n0.lamR := by linarith
  have hpsi0C := (fpt_contains_FR c.n0).add
    (((hlX.add (hL0pt.mul hlM0)).add (hL0pt.mul hlY)).divNat (k := 2)
      (by norm_num))
  have hpsi1C := (fpt_contains_FR c.n1).add
    (((hlX.add (hL1pt.mul hlM1)).add (hL1pt.mul hlY)).divNat (k := 2)
      (by norm_num))
  have hdipC := ((hlM1.add hlM0.neg).mul (hL1pt.add hL0pt.neg)).divNat
    (k := 8) (by norm_num)
  have hPsi0R : (0:ℝ) < c.n0.FR
      + (x + c.n0.lamR * Real.log (value c.n0.M) + c.n0.lamR * y) / 2
      - (Real.log (value c.n1.M) - Real.log (value c.n0.M))
        * (c.n1.lamR - c.n0.lamR) / 8 := by
    have h := (value_pos hPSI0).trans_le (hpsi0C.add hdipC.neg).1
    push_cast at h
    linarith [h]
  have hPsi1R : (0:ℝ) < c.n1.FR
      + (x + c.n1.lamR * Real.log (value c.n1.M) + c.n1.lamR * y) / 2
      - (Real.log (value c.n1.M) - Real.log (value c.n0.M))
        * (c.n1.lamR - c.n0.lamR) / 8 := by
    have h := (value_pos hPSI1).trans_le (hpsi1C.add hdipC.neg).1
    push_cast at h
    linarith [h]
  -- now fix r in the cell
  intro r hr _hr1
  have hn0lamv : (0:ℝ) < c.n0.lamR := by
    rw [Node.lamR_eq]; exact value_pos hlam0
  have hr0 : (0:ℝ) < r := hn0lamv.trans hr.1
  have hDr := hD r hr
  have hXr : X r = value c.X := (hX r hr).trans (value_div_SC c.X)
  have hYr : Y r = value c.Y := (hY r hr).trans (value_div_SC c.Y)
  have hlogXr : Real.log (X r) = x := by rw [hXr]
  have hlogYr : Real.log (Y r) = y := by rw [hYr]
  -- chord parametrization of the cell
  set t : ℝ := (r - c.n0.lamR) / (c.n1.lamR - c.n0.lamR) with htdef
  have hbane : c.n1.lamR - c.n0.lamR ≠ 0 := ne_of_gt hba
  have ht0 : 0 < t := div_pos (by linarith [hr.1]) hba
  have ht1 : t ≤ 1 := (div_le_one hba).mpr (by linarith [hr.2])
  have hrt : (1 - t) * c.n0.lamR + t * c.n1.lamR = r := by
    have h : t * (c.n1.lamR - c.n0.lamR) = r - c.n0.lamR := by
      rw [htdef]
      exact div_mul_cancel₀ _ hbane
    linarith
  have hMr_eq : M r = (1 - t) * value c.n0.M + t * value c.n1.M := by
    have h := hMlin t ⟨ht0.le, ht1⟩
    rw [hrt] at h
    rw [h, Node.MR_eq, Node.MR_eq]
  -- box containments
  have hDIc : (DIc c).Contains (D r) := by
    constructor
    · show value c.n1.d ≤ D r
      rw [← Node.dR_eq]; exact hDr.1
    · show D r ≤ value c.n0.d
      rw [← Node.dR_eq]; exact hDr.2
  have hd1v : (0:ℝ) < c.n1.dR := by rw [Node.dR_eq]; exact value_pos hd1
  have hDpos : 0 < D r := hd1v.trans_le hDr.1
  have hMr_lo : value c.n0.M ≤ M r := by
    rw [hMr_eq]
    linarith [mul_nonneg ht0.le (sub_nonneg.mpr hM01)]
  have hMr_hi : M r ≤ value c.n1.M := by
    rw [hMr_eq]
    linarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - t) (sub_nonneg.mpr hM01)]
  have hMIc : (MIc c).Contains (M r) := by
    constructor
    · show value (min c.n0.M c.n1.M) ≤ M r
      exact le_trans (value_le_value (min_le_left _ _)) hMr_lo
    · show M r ≤ value (max c.n0.M c.n1.M)
      exact le_trans hMr_hi (value_le_value (le_max_right _ _))
  have hMpos : 0 < M r := hM0R.trans_le hMr_lo
  have hMlt1 : M r < 1 := lt_of_le_of_lt hMr_hi hM1R1
  have h1Mr : (0:ℝ) < 1 - M r := by linarith
  -- (XLE): enclosure of the RHS logarithm over the box
  have hexpD : (expNegBig (DIc c)).Contains (Real.exp (-(D r))) :=
    expNegBig_contains hDIc hsafeE
  have hpI : (pIc c).Contains (1 - Real.exp (-(D r))) := by
    have h := contains_one_SC.add hexpD.neg
    simpa [pIc, sub_eq_add_neg] using h
  have hp0 : (0:ℝ) < 1 - Real.exp (-(D r)) := by
    have h1 : Real.exp (-(D r)) < 1 := by
      calc Real.exp (-(D r)) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
        _ = 1 := Real.exp_zero
    linarith
  have hlogp : (log 13 (pIc c)).Contains (Real.log (1 - Real.exp (-(D r)))) :=
    Sound.contains_log_of_safe hpI hsafeP
  have h1MC : (oneMinusMc c).Contains (1 - M r) := by
    have h := contains_one_SC.add hMIc.neg
    simpa [oneMinusMc, sub_eq_add_neg] using h
  have hlog1M : (log 13 (oneMinusMc c)).Contains (Real.log (1 - M r)) :=
    Sound.contains_log_of_safe h1MC hsafe1M
  have hinv1M : (inv (oneMinusMc c)).Contains (1 - M r)⁻¹ := h1MC.inv h1Mpos
  have hrhs : (rhsLogc c).Contains
      (Real.log (1 - Real.exp (-(D r))) * (1 - M r)⁻¹ + Real.log (1 - M r)) :=
    (hlogp.mul hinv1M).add hlog1M
  have hXle : X r ≤ (1 - Real.exp (-(D r))) ^ (1 / (1 - M r)) * (1 - M r) := by
    have hrpow : (0:ℝ) < (1 - Real.exp (-(D r))) ^ (1 / (1 - M r)) :=
      Real.rpow_pos_of_pos hp0 _
    have hRHSpos : (0:ℝ) <
        (1 - Real.exp (-(D r))) ^ (1 / (1 - M r)) * (1 - M r) :=
      mul_pos hrpow h1Mr
    have hlogRHS : Real.log
        ((1 - Real.exp (-(D r))) ^ (1 / (1 - M r)) * (1 - M r)) =
        Real.log (1 - Real.exp (-(D r))) * (1 - M r)⁻¹ + Real.log (1 - M r) := by
      rw [Real.log_mul (ne_of_gt hrpow) (ne_of_gt h1Mr),
        Real.log_rpow hp0, one_div]
      ring
    have hchain : x ≤ Real.log
        ((1 - Real.exp (-(D r))) ^ (1 / (1 - M r)) * (1 - M r)) := by
      rw [hlogRHS]
      exact hlX.2.trans ((value_le_value hXLE).trans hrhs.1)
    calc X r = value c.X := hXr
      _ = Real.exp x := (Real.exp_log hXv).symm
      _ ≤ Real.exp (Real.log
            ((1 - Real.exp (-(D r))) ^ (1 / (1 - M r)) * (1 - M r))) :=
          Real.exp_le_exp.mpr hchain
      _ = (1 - Real.exp (-(D r))) ^ (1 / (1 - M r)) * (1 - M r) :=
          Real.exp_log hRHSpos
  -- admissibility (both orientations), from the tangent bounds and (A)/(B)
  have hadm1 : ∀ s ∈ Ioc (0:ℝ) 1,
      F s ≤ -Real.log (X r) - s * Real.log (Y r) := by
    intro s hs
    have hs0 : (0:ℝ) ≤ s := hs.1.le
    have hs1 : s ≤ 1 := hs.2
    have e1 : (1 - s) * (c.wa.FR - c.wa.lamR * c.wa.dR) ≤ (1 - s) * (-x) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e2 : s * (c.wa.FR - c.wa.lamR * c.wa.dR + c.wa.dR) ≤ s * (-x - y) :=
      mul_le_mul_of_nonneg_left (by linarith) hs0
    have hlin : c.wa.FR + (s - c.wa.lamR) * c.wa.dR ≤ -x - s * y := by
      have hsum := add_le_add e1 e2
      calc c.wa.FR + (s - c.wa.lamR) * c.wa.dR
          = (1 - s) * (c.wa.FR - c.wa.lamR * c.wa.dR)
            + s * (c.wa.FR - c.wa.lamR * c.wa.dR + c.wa.dR) := by ring
        _ ≤ (1 - s) * (-x) + s * (-x - y) := hsum
        _ = -x - s * y := by ring
    rw [hlogXr, hlogYr]
    exact (htanA s hs).trans hlin
  have hadm2 : ∀ s ∈ Ioc (0:ℝ) 1,
      F s ≤ -Real.log (Y r) - s * Real.log (X r) := by
    intro s hs
    have hs0 : (0:ℝ) ≤ s := hs.1.le
    have hs1 : s ≤ 1 := hs.2
    have e1 : (1 - s) * (c.wb.FR - c.wb.lamR * c.wb.dR) ≤ (1 - s) * (-y) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e2 : s * (c.wb.FR - c.wb.lamR * c.wb.dR + c.wb.dR) ≤ s * (-y - x) :=
      mul_le_mul_of_nonneg_left (by linarith) hs0
    have hlin : c.wb.FR + (s - c.wb.lamR) * c.wb.dR ≤ -y - s * x := by
      have hsum := add_le_add e1 e2
      calc c.wb.FR + (s - c.wb.lamR) * c.wb.dR
          = (1 - s) * (c.wb.FR - c.wb.lamR * c.wb.dR)
            + s * (c.wb.FR - c.wb.lamR * c.wb.dR + c.wb.dR) := by ring
        _ ≤ (1 - s) * (-y) + s * (-y - x) := hsum
        _ = -y - s * x := by ring
    rw [hlogXr, hlogYr]
    exact (htanB s hs).trans hlin
  -- (PSI0)+(PSI1): the slack inequality via the chord/dip argument
  have hFr_ge : (1 - t) * c.n0.FR + t * c.n1.FR ≤ F r := by
    have h := hFchord t ⟨ht0.le, ht1⟩
    rwa [hrt] at h
  have hlogMr_ge : (1 - t) * Real.log (value c.n0.M)
      + t * Real.log (value c.n1.M) ≤ Real.log (M r) := by
    have h := strictConcaveOn_log_Ioi.concaveOn.2
      (Set.mem_Ioi.mpr hM0R) (Set.mem_Ioi.mpr hM1R)
      (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
    simp only [smul_eq_mul] at h
    rw [hMr_eq]
    exact h
  have hrM : r * ((1 - t) * Real.log (value c.n0.M)
      + t * Real.log (value c.n1.M)) ≤ r * Real.log (M r) :=
    mul_le_mul_of_nonneg_left hlogMr_ge hr0.le
  have hid : r * ((1 - t) * Real.log (value c.n0.M)
      + t * Real.log (value c.n1.M))
      = (1 - t) * (c.n0.lamR * Real.log (value c.n0.M))
        + t * (c.n1.lamR * Real.log (value c.n1.M))
        - t * (1 - t) * ((c.n1.lamR - c.n0.lamR)
          * (Real.log (value c.n1.M) - Real.log (value c.n0.M))) := by
    rw [← hrt]; ring
  have hidy : r * y = (1 - t) * (c.n0.lamR * y) + t * (c.n1.lamR * y) := by
    rw [← hrt]; ring
  have hquarter : t * (1 - t) ≤ 1 / 4 := by linarith [sq_nonneg (t - 1/2)]
  have hdipnn : (0:ℝ) ≤ (c.n1.lamR - c.n0.lamR)
      * (Real.log (value c.n1.M) - Real.log (value c.n0.M)) :=
    mul_nonneg hba.le (by linarith)
  have hdipbound : t * (1 - t) * ((c.n1.lamR - c.n0.lamR)
      * (Real.log (value c.n1.M) - Real.log (value c.n0.M)))
      ≤ (1 / 4) * ((c.n1.lamR - c.n0.lamR)
        * (Real.log (value c.n1.M) - Real.log (value c.n0.M))) :=
    mul_le_mul_of_nonneg_right hquarter hdipnn
  have hc0 : (0:ℝ) ≤ (1 - t) * (c.n0.FR
      + (x + c.n0.lamR * Real.log (value c.n0.M) + c.n0.lamR * y) / 2
      - (Real.log (value c.n1.M) - Real.log (value c.n0.M))
        * (c.n1.lamR - c.n0.lamR) / 8) :=
    mul_nonneg (by linarith) hPsi0R.le
  have hc1 : (0:ℝ) < t * (c.n1.FR
      + (x + c.n1.lamR * Real.log (value c.n1.M) + c.n1.lamR * y) / 2
      - (Real.log (value c.n1.M) - Real.log (value c.n0.M))
        * (c.n1.lamR - c.n0.lamR) / 8) :=
    mul_pos ht0 hPsi1R
  have hpsir : (0:ℝ) < F r + (x + r * Real.log (M r) + r * y) / 2 := by
    linarith [hFr_ge, hrM, hid, hidy, hdipbound, hc0, hc1]
  have hslack : denseCaseExponent (X r) (M r) (Y r) r < F r := by
    simp only [denseCaseExponent]
    rw [hlogXr, hlogYr]
    linarith
  -- assemble
  unfold LadderHypsAt
  refine ⟨hFnn.trans (hFge r hr), hDpos, ⟨hMpos, hMlt1⟩, ?_, ?_, hXle,
    hadm1, hadm2, hslack⟩
  · rw [hXr]; exact ⟨hXv, hXv1⟩
  · rw [hYr]; exact ⟨hYv, hYv1⟩

/-! ### The evaluation twin -/

/-- Evaluation twin of `checkCell` with `let`-sharing of the common
sub-expressions (the kernel caches reductions of shared sub-terms, so
`decide +kernel` on `checkCellFast` avoids recomputing `lX`, `rhsLog`, …).
Definitionally equal to `checkCell` (`checkCellFast_eq`); the generated data
files state their kernel facts about `checkCellFast`. -/
def checkCellFast (c : Cell) : Bool :=
  let Mlo := min c.n0.M c.n1.M
  let Mhi := max c.n0.M c.n1.M
  let DI : Interval := ⟨c.n1.d, c.n0.d⟩
  let MI : Interval := ⟨Mlo, Mhi⟩
  let lX := logPos (point c.X)
  let lY := logPos (point c.Y)
  let lM0 := logPos (point c.n0.M)
  let lM1 := logPos (point c.n1.M)
  let oneM := add (point SC) (neg MI)
  let pI := add (point SC) (neg (expNegBig DI))
  let rhsLog := add (mul (log 13 pI) (inv oneM)) (log 13 oneM)
  let Sa := add (fpt c.wa.F) (neg (mul (point c.wa.lam) (point c.wa.d)))
  let Sb := add (fpt c.wb.F) (neg (mul (point c.wb.lam) (point c.wb.d)))
  let psiLo0 := add (fpt c.n0.F)
    (divNat (add (add lX (mul (point c.n0.lam) lM0))
      (mul (point c.n0.lam) lY)) 2)
  let psiLo1 := add (fpt c.n1.F)
    (divNat (add (add lX (mul (point c.n1.lam) lM1))
      (mul (point c.n1.lam) lY)) 2)
  let dip := divNat (mul (add lM1 (neg lM0))
    (add (point c.n1.lam) (neg (point c.n0.lam)))) 8
  decide (0 < c.n0.lam) && decide (c.n0.lam < c.n1.lam) &&
  decide (0 < c.n1.d) && decide (c.n1.d ≤ c.n0.d) &&
  decide (c.n1.F = c.n0.F + (c.n0.d + c.n1.d) * (c.n1.lam - c.n0.lam)) &&
  decide (0 < c.n0.M) && decide (c.n0.M < SC) &&
  decide (0 < c.n1.M) && decide (c.n1.M < SC) &&
  decide (0 < c.X) && decide (c.X < SC) && decide (0 < c.Y) && decide (c.Y < SC) &&
  decide (0 < c.wa.lam) && decide (c.wa.lam ≤ SC) && decide (0 < c.wa.d) &&
  decide (0 < c.wb.lam) && decide (c.wb.lam ≤ SC) && decide (0 < c.wb.d) &&
  logPosSafe (point c.X) && logPosSafe (point c.Y) &&
  logPosSafe (point c.n0.M) && logPosSafe (point c.n1.M) &&
  expSafe 16 (divNat (neg DI) 16) &&
  logSafe 13 pI && logSafe 13 oneM &&
  positive pI && positive oneM &&
  decide (lX.hi ≤ rhsLog.lo) &&
  decide ((add Sa lX).hi ≤ 0) &&
  decide ((add (add Sa (point c.wa.d)) (add lX lY)).hi ≤ 0) &&
  decide ((add Sb lY).hi ≤ 0) &&
  decide ((add (add Sb (point c.wb.d)) (add lY lX)).hi ≤ 0) &&
  decide (c.n0.M ≤ c.n1.M) &&
  decide (0 < (add psiLo0 (neg dip)).lo) &&
  decide (0 < (add psiLo1 (neg dip)).lo)

theorem checkCellFast_eq : checkCellFast = checkCell := rfl

/-! ### Global pass: chain structure (SPEC §5) -/

/-- Structural walk: consecutive cells share their full boundary `Node`
(`c.n1 = c'.n0`), and the final cell ends at `SC` (i.e. `λ = 1`). -/
def chainStep : List Cell → Bool
  | [] => true
  | [c] => decide (c.n1.lam = SC)
  | c :: c' :: rest => decide (c.n1 = c'.n0) && chainStep (c' :: rest)

/-- Full chain check: non-empty, starts at `L0` (= `λ₀ · SC`), walks
`chainStep`. -/
def checkChain : List Cell → Bool
  | [] => false
  | c :: rest => decide (c.n0.lam = L0) && chainStep (c :: rest)

theorem chainStep_last {cells : List Cell} (h : chainStep cells = true) :
    ∀ cN, cells.getLast? = some cN → cN.n1.lam = SC := by
  induction cells with
  | nil => intro cN hcN; simp at hcN
  | cons c rest ih =>
    cases rest with
    | nil =>
      intro cN hcN
      simp only [List.getLast?_singleton, Option.some.injEq] at hcN
      simp only [chainStep, decide_eq_true_eq] at h
      rw [← hcN]
      exact h
    | cons c' rest' =>
      simp only [chainStep, Bool.and_eq_true, decide_eq_true_eq] at h
      intro cN hcN
      rw [List.getLast?_cons_cons] at hcN
      exact ih h.2 cN hcN

theorem chainStep_isChain {cells : List Cell} (h : chainStep cells = true) :
    List.IsChain (fun a b => a.n1 = b.n0) cells := by
  induction cells with
  | nil => exact .nil
  | cons c rest ih =>
    cases rest with
    | nil => exact .singleton c
    | cons c' rest' =>
      simp only [chainStep, Bool.and_eq_true, decide_eq_true_eq] at h
      exact .cons_cons h.1 (ih h.2)

/-- Soundness of the chain walk: the cell list is non-empty, starts at `L0`,
ends at `SC`, and consecutive cells share their boundary node
(`List.IsChain` = `List.Chain'`). -/
theorem checkChain_sound {cells : List Cell} (h : checkChain cells = true) :
    cells ≠ [] ∧
    (∀ c0, cells.head? = some c0 → c0.n0.lam = L0) ∧
    (∀ cN, cells.getLast? = some cN → cN.n1.lam = SC) ∧
    List.IsChain (fun a b => a.n1 = b.n0) cells := by
  match cells with
  | [] => simp [checkChain] at h
  | c :: rest =>
    simp only [checkChain, Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨by simp, ?_, chainStep_last h.2, chainStep_isChain h.2⟩
    intro c0 hc0
    simp only [List.head?_cons, Option.some.injEq] at hc0
    rw [← hc0]
    exact h.1

/-- The integer chain-local facts of every cell in a fully checked list. -/
theorem all_checkCell_int_facts {cells : List Cell}
    (h : cells.all checkCell = true) :
    ∀ c ∈ cells,
      0 < c.n0.lam ∧ c.n0.lam < c.n1.lam ∧
      0 < c.n1.d ∧ c.n1.d ≤ c.n0.d ∧
      c.n1.F = c.n0.F + (c.n0.d + c.n1.d) * (c.n1.lam - c.n0.lam) ∧
      0 < c.n0.M ∧ c.n0.M < SC ∧ 0 < c.n1.M ∧ c.n1.M < SC ∧
      0 < c.X ∧ c.X < SC ∧ 0 < c.Y ∧ c.Y < SC ∧
      0 < c.wa.lam ∧ c.wa.lam ≤ SC ∧ 0 < c.wa.d ∧
      0 < c.wb.lam ∧ c.wb.lam ≤ SC ∧ 0 < c.wb.d :=
  fun c hc => checkCell_int_facts c (List.all_eq_true.mp h c hc)

/-! ### Global pass: witness merge (SPEC §5) -/

/-- Advance past nodes strictly left of the witness (ascending pointer). -/
def advanceAsc (w : Node) : List Node → List Node
  | [] => []
  | n :: ns => if n.lam < w.lam then advanceAsc w ns else n :: ns

/-- Advance past nodes strictly right of the witness (descending pointer,
used against the reversed node list). -/
def advanceDesc (w : Node) : List Node → List Node
  | [] => []
  | n :: ns => if w.lam < n.lam then advanceDesc w ns else n :: ns

theorem advanceAsc_subset (w : Node) :
    ∀ ns, ∀ x ∈ advanceAsc w ns, x ∈ ns := by
  intro ns
  induction ns with
  | nil => intro x hx; simp [advanceAsc] at hx
  | cons n ns ih =>
    intro x hx
    simp only [advanceAsc] at hx
    split at hx
    · exact List.mem_cons_of_mem n (ih x hx)
    · exact hx

theorem advanceDesc_subset (w : Node) :
    ∀ ns, ∀ x ∈ advanceDesc w ns, x ∈ ns := by
  intro ns
  induction ns with
  | nil => intro x hx; simp [advanceDesc] at hx
  | cons n ns ih =>
    intro x hx
    simp only [advanceDesc] at hx
    split at hx
    · exact List.mem_cons_of_mem n (ih x hx)
    · exact hx

/-- Two-pointer merge (ascending): every witness in `ws` must literally equal
the node reached after advancing past smaller abscissae.  Passing implies
every `w ∈ ws` is a member of `ns` (and, for a strictly increasing node list,
that `ws` is non-decreasing). -/
def mergeAsc : List Node → List Node → Bool
  | _, [] => true
  | ns, w :: ws =>
    match advanceAsc w ns with
    | [] => false
    | n :: ns' => decide (n = w) && mergeAsc (n :: ns') ws

/-- Two-pointer merge against a descending node list. -/
def mergeDesc : List Node → List Node → Bool
  | _, [] => true
  | ns, w :: ws =>
    match advanceDesc w ns with
    | [] => false
    | n :: ns' => decide (n = w) && mergeDesc (n :: ns') ws

theorem mergeAsc_mem : ∀ (ws ns : List Node), mergeAsc ns ws = true →
    ∀ w ∈ ws, w ∈ ns := by
  intro ws
  induction ws with
  | nil => intro ns _ w hw; simp at hw
  | cons w0 ws ih =>
    intro ns h w hw
    cases hadv : advanceAsc w0 ns with
    | nil => simp [mergeAsc, hadv] at h
    | cons n ns' =>
      simp only [mergeAsc, hadv, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨heq, hrec⟩ := h
      subst heq
      have hsub : ∀ z ∈ (n :: ns'), z ∈ ns := by
        intro z hz
        exact advanceAsc_subset n ns z (by rw [hadv]; exact hz)
      rcases List.mem_cons.mp hw with rfl | hwtail
      · exact hsub w (List.mem_cons_self ..)
      · exact hsub w (ih (n :: ns') hrec w hwtail)

theorem mergeDesc_mem : ∀ (ws ns : List Node), mergeDesc ns ws = true →
    ∀ w ∈ ws, w ∈ ns := by
  intro ws
  induction ws with
  | nil => intro ns _ w hw; simp at hw
  | cons w0 ws ih =>
    intro ns h w hw
    cases hadv : advanceDesc w0 ns with
    | nil => simp [mergeDesc, hadv] at h
    | cons n ns' =>
      simp only [mergeDesc, hadv, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨heq, hrec⟩ := h
      subst heq
      have hsub : ∀ z ∈ (n :: ns'), z ∈ ns := by
        intro z hz
        exact advanceDesc_subset n ns z (by rw [hadv]; exact hz)
      rcases List.mem_cons.mp hw with rfl | hwtail
      · exact hsub w (List.mem_cons_self ..)
      · exact hsub w (ih (n :: ns') hrec w hwtail)

/-- Witness merge pass: `wa` witnesses two-pointered against the node list
(ascending), `wb` witnesses against the reversed node list (descending). -/
def checkWitnesses (cells : List Cell) : Bool :=
  mergeAsc (nodes cells) (cells.map (·.wa)) &&
  mergeDesc ((nodes cells).reverse) (cells.map (·.wb))

/-- Soundness of the merge pass: every tangent witness of every cell is a
node of the certificate. -/
theorem checkWitnesses_sound {cells : List Cell}
    (h : checkWitnesses cells = true) :
    ∀ c ∈ cells, c.wa ∈ nodes cells ∧ c.wb ∈ nodes cells := by
  simp only [checkWitnesses, Bool.and_eq_true] at h
  intro c hc
  refine ⟨mergeAsc_mem _ _ h.1 c.wa (List.mem_map_of_mem hc), ?_⟩
  have hb := mergeDesc_mem _ _ h.2 c.wb (List.mem_map_of_mem hc)
  exact List.mem_reverse.mp hb

/-! ### Global pass: tail check (T1, SPEC §5) -/

/-- Tail check (T1), on the head cell `c0`:
`0 < F₀ - λ₀ d₀ + log(X₀/SC)/2` (interval lower bound), giving `ψ > 0` and
`F > 0` on the linear tail `(0, λ₀]`. -/
def checkTail : List Cell → Bool
  | [] => false
  | c0 :: _ =>
    decide (0 < c0.X) && logPosSafe (point c0.X) &&
    decide (0 <
      (add (add (fpt c0.n0.F) (neg (mul (point c0.n0.lam) (point c0.n0.d))))
        (divNat (logPos (point c0.X)) 2)).lo)

/-- Soundness of (T1). -/
theorem checkTail_sound {cells : List Cell} (h : checkTail cells = true) :
    ∀ c0, cells.head? = some c0 →
      0 < c0.n0.FR - c0.n0.lamR * c0.n0.dR +
        Real.log ((c0.X : ℝ) / (SC : ℝ)) / 2 := by
  match cells with
  | [] => simp [checkTail] at h
  | c :: rest =>
    intro c0 hc0
    simp only [List.head?_cons, Option.some.injEq] at hc0
    subst hc0
    simp only [checkTail, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hX0, hsafe⟩, hT⟩ := h
    have hXv : (0:ℝ) < value c.X := value_pos hX0
    have hlX : (logPos (point c.X)).Contains (Real.log (value c.X)) :=
      logPos_contains (contains_point c.X) hXv hsafe
    have hC := ((fpt_contains_FR c.n0).add
      (((contains_point c.n0.lam).mul (contains_point c.n0.d)).neg)).add
      (hlX.divNat (k := 2) (by norm_num))
    have h0 := (value_pos hT).trans_le hC.1
    rw [value_div_SC, Node.lamR_eq, Node.dR_eq]
    push_cast at h0
    linarith

/-! ### Per-cell soundness, tail variant

On the tail `(0, λ₀]` the certificate functions are clamped to the head
cell's left-node values (`D ≡ n0.dR`, `M ≡ n0.MR`, `X/Y ≡` cell-0 constants)
and `F` is linear with slope `n0.dR` through `(n0.lamR, n0.FR)`.  The head
cell's checks plus (T1) then give `LadderHypsAt` on the whole tail: the
admissibility and (XLE) arguments are `r`-free (the point `(n0.dR, n0.MR)`
lies in the cell box), and `ψ` is linear in `r` on the tail with positive
values at both endpoints — `hT1` at `r → 0⁺` and (PSI0) at `r = n0.lamR`
(the `ψ` endpoint value at the left node, valid since `dip ≥ 0`). -/

set_option maxHeartbeats 2000000 in
theorem checkCell_sound_tail (c : Cell) (hchk : checkCell c = true)
    (F D M X Y : ℝ → ℝ)
    (hT1 : 0 < c.n0.FR - c.n0.lamR * c.n0.dR +
      Real.log ((c.X : ℝ) / (SC : ℝ)) / 2)
    (hFlin : ∀ r ∈ Set.Ioc (0:ℝ) c.n0.lamR,
      F r = c.n0.FR + (r - c.n0.lamR) * c.n0.dR)
    (hDv : ∀ r ∈ Set.Ioc (0:ℝ) c.n0.lamR, D r = c.n0.dR)
    (hMv : ∀ r ∈ Set.Ioc (0:ℝ) c.n0.lamR, M r = c.n0.MR)
    (hXv : ∀ r ∈ Set.Ioc (0:ℝ) c.n0.lamR, X r = (c.X : ℝ) / (SC : ℝ))
    (hYv : ∀ r ∈ Set.Ioc (0:ℝ) c.n0.lamR, Y r = (c.Y : ℝ) / (SC : ℝ))
    (htanA : ∀ s ∈ Set.Ioc (0:ℝ) 1, F s ≤ c.wa.FR + (s - c.wa.lamR) * c.wa.dR)
    (htanB : ∀ s ∈ Set.Ioc (0:ℝ) 1, F s ≤ c.wb.FR + (s - c.wb.lamR) * c.wb.dR) :
    ∀ r ∈ Set.Ioc (0:ℝ) c.n0.lamR, LadderHypsAt F D M X Y r := by
  simp only [checkCell, Bool.and_eq_true, decide_eq_true_eq, positive,
    and_assoc] at hchk
  obtain ⟨hlam0, hlam01, hd1, hd10, _hFchain, hM00, hM0SC, hM10, _hM1SC,
    hX0, hXSC, hY0, hYSC, _hwal0, _hwalSC, _hwad0, _hwbl0, _hwblSC, _hwbd0,
    hsafeX, hsafeY, hsafeM0, hsafeM1, hsafeE, hsafeP, hsafe1M, _hpIpos, h1Mpos,
    hXLE, hA1, hA2, hB1, hB2, hMM, hPSI0, _hPSI1⟩ := hchk
  rw [value_div_SC] at hT1
  rw [SC_eq_scale] at hXSC hYSC hM0SC
  -- real-valued facts about the cell constants
  have hX0R : (0:ℝ) < value c.X := value_pos hX0
  have hX1R : value c.X < 1 := value_lt_one hXSC
  have hY0R : (0:ℝ) < value c.Y := value_pos hY0
  have hY1R : value c.Y < 1 := value_lt_one hYSC
  have hM0R : (0:ℝ) < value c.n0.M := value_pos hM00
  have hM0R1 : value c.n0.M < 1 := value_lt_one hM0SC
  have hM1R : (0:ℝ) < value c.n1.M := value_pos hM10
  set x := Real.log (value c.X) with hxdef
  set y := Real.log (value c.Y) with hydef
  have hxneg : x < 0 := Real.log_neg hX0R hX1R
  have hyneg : y < 0 := Real.log_neg hY0R hY1R
  -- log enclosures for the cell constants
  have hlX : (lXc c).Contains x := logPos_contains (contains_point c.X) hX0R hsafeX
  have hlY : (lYc c).Contains y := logPos_contains (contains_point c.Y) hY0R hsafeY
  have hlM0 : (lM0c c).Contains (Real.log (value c.n0.M)) :=
    logPos_contains (contains_point c.n0.M) hM0R hsafeM0
  have hlM1 : (lM1c c).Contains (Real.log (value c.n1.M)) :=
    logPos_contains (contains_point c.n1.M) hM1R hsafeM1
  -- witness S̄ enclosures and the (A)/(B) real inequalities (r-free)
  have hSa : (SaI c).Contains (c.wa.FR - c.wa.lamR * c.wa.dR) := by
    have h := (fpt_contains_FR c.wa).add
      (((contains_point c.wa.lam).mul (contains_point c.wa.d)).neg)
    simpa [SaI, sub_eq_add_neg, Node.lamR_eq, Node.dR_eq] using h
  have hSb : (SbI c).Contains (c.wb.FR - c.wb.lamR * c.wb.dR) := by
    have h := (fpt_contains_FR c.wb).add
      (((contains_point c.wb.lam).mul (contains_point c.wb.d)).neg)
    simpa [SbI, sub_eq_add_neg, Node.lamR_eq, Node.dR_eq] using h
  have hSaD : (add (SaI c) (point c.wa.d)).Contains
      (c.wa.FR - c.wa.lamR * c.wa.dR + c.wa.dR) := by
    have h := hSa.add (contains_point c.wa.d)
    rwa [← Node.dR_eq] at h
  have hSbD : (add (SbI c) (point c.wb.d)).Contains
      (c.wb.FR - c.wb.lamR * c.wb.dR + c.wb.dR) := by
    have h := hSb.add (contains_point c.wb.d)
    rwa [← Node.dR_eq] at h
  have hA1R : c.wa.FR - c.wa.lamR * c.wa.dR + x ≤ 0 := by
    have h := (hSa.add hlX).2
    have h0 := value_nonpos hA1
    linarith
  have hA2R : c.wa.FR - c.wa.lamR * c.wa.dR + c.wa.dR + (x + y) ≤ 0 := by
    have h := (hSaD.add (hlX.add hlY)).2
    have h0 := value_nonpos hA2
    linarith
  have hB1R : c.wb.FR - c.wb.lamR * c.wb.dR + y ≤ 0 := by
    have h := (hSb.add hlY).2
    have h0 := value_nonpos hB1
    linarith
  have hB2R : c.wb.FR - c.wb.lamR * c.wb.dR + c.wb.dR + (y + x) ≤ 0 := by
    have h := (hSbD.add (hlY.add hlX)).2
    have h0 := value_nonpos hB2
    linarith
  -- (PSI0) gives the ψ endpoint bound at r = n0.lamR directly (dip ≥ 0)
  have hL0pt : (point c.n0.lam).Contains c.n0.lamR := by
    rw [Node.lamR_eq]; exact contains_point c.n0.lam
  have hL1pt : (point c.n1.lam).Contains c.n1.lamR := by
    rw [Node.lamR_eq]; exact contains_point c.n1.lam
  have hab : c.n0.lamR < c.n1.lamR := by
    rw [Node.lamR_eq, Node.lamR_eq]; exact value_lt_value hlam01
  have hL01 : Real.log (value c.n0.M) ≤ Real.log (value c.n1.M) :=
    Real.log_le_log hM0R (value_le_value hMM)
  have hpsi0C := (fpt_contains_FR c.n0).add
    (((hlX.add (hL0pt.mul hlM0)).add (hL0pt.mul hlY)).divNat (k := 2)
      (by norm_num))
  have hdipC := ((hlM1.add hlM0.neg).mul (hL1pt.add hL0pt.neg)).divNat
    (k := 8) (by norm_num)
  have hdipnn : (0:ℝ) ≤ (Real.log (value c.n1.M) - Real.log (value c.n0.M))
      * (c.n1.lamR - c.n0.lamR) :=
    mul_nonneg (by linarith) (by linarith)
  have hn0lamv : (0:ℝ) < c.n0.lamR := by
    rw [Node.lamR_eq]; exact value_pos hlam0
  have hAL : (0:ℝ) < c.n0.FR +
      (x + c.n0.lamR * Real.log (value c.n0.M) + c.n0.lamR * y) / 2 := by
    have h := (value_pos hPSI0).trans_le (hpsi0C.add hdipC.neg).1
    push_cast at h
    linarith [h, hdipnn]
  -- now fix r in the tail
  intro r hr
  have hr0 : (0:ℝ) < r := hr.1
  have hrle : r ≤ c.n0.lamR := hr.2
  have hXr : X r = value c.X := (hXv r hr).trans (value_div_SC c.X)
  have hYr : Y r = value c.Y := (hYv r hr).trans (value_div_SC c.Y)
  have hMr' : M r = value c.n0.M := (hMv r hr).trans (Node.MR_eq c.n0)
  have hDr' : D r = value c.n0.d := (hDv r hr).trans (Node.dR_eq c.n0)
  have hFr : F r = c.n0.FR + (r - c.n0.lamR) * c.n0.dR := hFlin r hr
  have hlogXr : Real.log (X r) = x := by rw [hXr]
  have hlogYr : Real.log (Y r) = y := by rw [hYr]
  have hlogMr : Real.log (M r) = Real.log (value c.n0.M) := by rw [hMr']
  -- the clamped point lies in the cell boxes
  have hDIc : (DIc c).Contains (D r) := by
    rw [hDr']
    exact ⟨value_le_value hd10, le_rfl⟩
  have hMIc : (MIc c).Contains (M r) := by
    rw [hMr']
    exact ⟨value_le_value (min_le_left _ _), value_le_value (le_max_left _ _)⟩
  have hDpos : 0 < D r := by
    rw [hDr']; exact value_pos (lt_of_lt_of_le hd1 hd10)
  have hMpos : 0 < M r := by rw [hMr']; exact hM0R
  have hMlt1 : M r < 1 := by rw [hMr']; exact hM0R1
  have h1Mr : (0:ℝ) < 1 - M r := by linarith
  -- (XLE) at the clamped point (verbatim box argument)
  have hexpD : (expNegBig (DIc c)).Contains (Real.exp (-(D r))) :=
    expNegBig_contains hDIc hsafeE
  have hpI : (pIc c).Contains (1 - Real.exp (-(D r))) := by
    have h := contains_one_SC.add hexpD.neg
    simpa [pIc, sub_eq_add_neg] using h
  have hp0 : (0:ℝ) < 1 - Real.exp (-(D r)) := by
    have h1 : Real.exp (-(D r)) < 1 := by
      calc Real.exp (-(D r)) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
        _ = 1 := Real.exp_zero
    linarith
  have hlogp : (log 13 (pIc c)).Contains (Real.log (1 - Real.exp (-(D r)))) :=
    Sound.contains_log_of_safe hpI hsafeP
  have h1MC : (oneMinusMc c).Contains (1 - M r) := by
    have h := contains_one_SC.add hMIc.neg
    simpa [oneMinusMc, sub_eq_add_neg] using h
  have hlog1M : (log 13 (oneMinusMc c)).Contains (Real.log (1 - M r)) :=
    Sound.contains_log_of_safe h1MC hsafe1M
  have hinv1M : (inv (oneMinusMc c)).Contains (1 - M r)⁻¹ := h1MC.inv h1Mpos
  have hrhs : (rhsLogc c).Contains
      (Real.log (1 - Real.exp (-(D r))) * (1 - M r)⁻¹ + Real.log (1 - M r)) :=
    (hlogp.mul hinv1M).add hlog1M
  have hXle : X r ≤ (1 - Real.exp (-(D r))) ^ (1 / (1 - M r)) * (1 - M r) := by
    have hrpow : (0:ℝ) < (1 - Real.exp (-(D r))) ^ (1 / (1 - M r)) :=
      Real.rpow_pos_of_pos hp0 _
    have hRHSpos : (0:ℝ) <
        (1 - Real.exp (-(D r))) ^ (1 / (1 - M r)) * (1 - M r) :=
      mul_pos hrpow h1Mr
    have hlogRHS : Real.log
        ((1 - Real.exp (-(D r))) ^ (1 / (1 - M r)) * (1 - M r)) =
        Real.log (1 - Real.exp (-(D r))) * (1 - M r)⁻¹ + Real.log (1 - M r) := by
      rw [Real.log_mul (ne_of_gt hrpow) (ne_of_gt h1Mr),
        Real.log_rpow hp0, one_div]
      ring
    have hchain : x ≤ Real.log
        ((1 - Real.exp (-(D r))) ^ (1 / (1 - M r)) * (1 - M r)) := by
      rw [hlogRHS]
      exact hlX.2.trans ((value_le_value hXLE).trans hrhs.1)
    calc X r = value c.X := hXr
      _ = Real.exp x := (Real.exp_log hX0R).symm
      _ ≤ Real.exp (Real.log
            ((1 - Real.exp (-(D r))) ^ (1 / (1 - M r)) * (1 - M r))) :=
          Real.exp_le_exp.mpr hchain
      _ = (1 - Real.exp (-(D r))) ^ (1 / (1 - M r)) * (1 - M r) :=
          Real.exp_log hRHSpos
  -- admissibility (verbatim: r enters only through X r / Y r)
  have hadm1 : ∀ s ∈ Ioc (0:ℝ) 1,
      F s ≤ -Real.log (X r) - s * Real.log (Y r) := by
    intro s hs
    have hs0 : (0:ℝ) ≤ s := hs.1.le
    have hs1 : s ≤ 1 := hs.2
    have e1 : (1 - s) * (c.wa.FR - c.wa.lamR * c.wa.dR) ≤ (1 - s) * (-x) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e2 : s * (c.wa.FR - c.wa.lamR * c.wa.dR + c.wa.dR) ≤ s * (-x - y) :=
      mul_le_mul_of_nonneg_left (by linarith) hs0
    have hlin : c.wa.FR + (s - c.wa.lamR) * c.wa.dR ≤ -x - s * y := by
      have hsum := add_le_add e1 e2
      calc c.wa.FR + (s - c.wa.lamR) * c.wa.dR
          = (1 - s) * (c.wa.FR - c.wa.lamR * c.wa.dR)
            + s * (c.wa.FR - c.wa.lamR * c.wa.dR + c.wa.dR) := by ring
        _ ≤ (1 - s) * (-x) + s * (-x - y) := hsum
        _ = -x - s * y := by ring
    rw [hlogXr, hlogYr]
    exact (htanA s hs).trans hlin
  have hadm2 : ∀ s ∈ Ioc (0:ℝ) 1,
      F s ≤ -Real.log (Y r) - s * Real.log (X r) := by
    intro s hs
    have hs0 : (0:ℝ) ≤ s := hs.1.le
    have hs1 : s ≤ 1 := hs.2
    have e1 : (1 - s) * (c.wb.FR - c.wb.lamR * c.wb.dR) ≤ (1 - s) * (-y) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e2 : s * (c.wb.FR - c.wb.lamR * c.wb.dR + c.wb.dR) ≤ s * (-y - x) :=
      mul_le_mul_of_nonneg_left (by linarith) hs0
    have hlin : c.wb.FR + (s - c.wb.lamR) * c.wb.dR ≤ -y - s * x := by
      have hsum := add_le_add e1 e2
      calc c.wb.FR + (s - c.wb.lamR) * c.wb.dR
          = (1 - s) * (c.wb.FR - c.wb.lamR * c.wb.dR)
            + s * (c.wb.FR - c.wb.lamR * c.wb.dR + c.wb.dR) := by ring
        _ ≤ (1 - s) * (-y) + s * (-y - x) := hsum
        _ = -y - s * x := by ring
    rw [hlogXr, hlogYr]
    exact (htanB s hs).trans hlin
  -- 0 ≤ F r: F(0⁺) = F₀ - λ₀ d₀ > -x/2 > 0 by (T1), and slope d₀ > 0
  have hd0R : (0:ℝ) ≤ c.n0.dR := by
    rw [Node.dR_eq]; exact (value_pos (lt_of_lt_of_le hd1 hd10)).le
  have hFnnr : 0 ≤ F r := by
    rw [hFr]
    have h1 : 0 ≤ r * c.n0.dR := mul_nonneg hr0.le hd0R
    nlinarith [hT1, hxneg]
  -- hslack: ψ is linear in r on the tail, positive at both endpoints
  have hslack : denseCaseExponent (X r) (M r) (Y r) r < F r := by
    simp only [denseCaseExponent]
    rw [hlogXr, hlogYr, hlogMr, hFr]
    have key : c.n0.lamR *
        (c.n0.FR + (r - c.n0.lamR) * c.n0.dR +
          (x + r * Real.log (value c.n0.M) + r * y) / 2)
        = (c.n0.lamR - r) * (c.n0.FR - c.n0.lamR * c.n0.dR + x / 2)
          + r * (c.n0.FR +
            (x + c.n0.lamR * Real.log (value c.n0.M) + c.n0.lamR * y) / 2) := by
      ring
    have hprod : 0 < c.n0.lamR *
        (c.n0.FR + (r - c.n0.lamR) * c.n0.dR +
          (x + r * Real.log (value c.n0.M) + r * y) / 2) := by
      rw [key]
      have t1 : 0 ≤ (c.n0.lamR - r) *
          (c.n0.FR - c.n0.lamR * c.n0.dR + x / 2) :=
        mul_nonneg (by linarith) hT1.le
      have t2 : 0 < r * (c.n0.FR +
          (x + c.n0.lamR * Real.log (value c.n0.M) + c.n0.lamR * y) / 2) :=
        mul_pos hr0 hAL
      linarith
    rcases mul_pos_iff.mp hprod with ⟨-, h⟩ | ⟨hneg, -⟩
    · linarith
    · linarith
  -- assemble
  unfold LadderHypsAt
  refine ⟨hFnnr, hDpos, ⟨hMpos, hMlt1⟩, ?_, ?_, hXle, hadm1, hadm2, hslack⟩
  · rw [hXr]; exact ⟨hX0R, hX1R⟩
  · rw [hYr]; exact ⟨hY0R, hY1R⟩

end Bootstrap2
end RamseyLean

import RamseyLean.Bootstrap.Reduction
import RamseyLean.Analysis.FixedPointInterval

/-!
# Kernel-checkable certificate cell checker for the bootstrap region `[λ₀, 1]`

Per cell `[lo/s, hi/s]` (`s = 10^12`) with witness `w/s` and a case tag, the
Bool-valued `checkCell` establishes (via `checkCell_sound`):

  1. `0 < Dpaper r` and `D2paper r < 0` on the cell,
  2. `LadderFactsAt r` on the cell (given `TangentUB` and the kink inequality
     `F u ≤ (1+u) F' u`, cf. `Bootstrap.kink_ineq`).

All integer-interval operations are those of
`RamseyLean.Analysis.FixedPointInterval`, plus three extensions proved sound
here: exact-coefficient polynomial enclosures in mean-value form (`mv`), a
scaling reduction for `log` of small arguments (`logPos`), and a
range reduction for `exp` of large negative arguments (`expNegBig`).

The Python data generator mirrors this file bit-exactly; the shared spec is
`RamseyLean/Bootstrap/CELLSPEC.md`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace RamseyLean
namespace Bootstrap
namespace CertCheck

open Set FixedPointInterval FixedPointInterval.Interval

/-! ### Cell data -/

/-- One certificate cell: the interval `[lo/s, hi/s]` with witness `u₀ = w/s`
(`s = 10^12`), and the case tag `kase`:
* `kase = 0` — paper witness `t₀ = 1/u₀ > 1`, `S̄ = F(u₀) - u₀·D(u₀)`;
* `kase = 1` — paper witness `t₀ = u₀ ≤ 1`, `S̄ = D(u₀)`;
* `kase = 2` — kink witness `t₀ = 1`, `S̄ = F(1) + xU` (`w` unused). -/
structure CellData where
  lo : Int
  hi : Int
  w : Int
  kase : Nat
deriving Repr, DecidableEq

/-! ### Exact coefficients (scale `10^12`; index = power)

`cP` = coefficients of `Ppaper`; `cA` = `Ppaper' - Ppaper`;
`cB` = `Ppaper'' - 2 Ppaper' + Ppaper`; `cQ` = `Qpaper`;
`dP, dA, dB, dQ` are the corresponding derivative coefficient lists. -/

def cP : List Int := [0, -348694000000, -451951000000, 6611582000000,
  -24021517000000, 43622007000000, -43154000000000, 22319017000000,
  -4736149000000]
def dP : List Int := [-348694000000, -903902000000, 19834746000000,
  -96086068000000, 218110035000000, -258924000000000, 156233119000000,
  -37889192000000]
def cA : List Int := [-348694000000, -555208000000, 20286697000000,
  -102697650000000, 242131552000000, -302546007000000, 199387119000000,
  -60208209000000, 4736149000000]
def dA : List Int := [-555208000000, 40573394000000, -308092950000000,
  968526208000000, -1512730035000000, 1196322714000000, -421457463000000,
  37889192000000]
def cB : List Int := [-206514000000, 41128602000000, -328379647000000,
  1071223858000000, -1754861587000000, 1498868721000000, -620844582000000,
  98097401000000, -4736149000000]
def dB : List Int := [41128602000000, -656759294000000, 3213671574000000,
  -7019446348000000, 7494343605000000, -3725067492000000, 686681807000000,
  -37889192000000]
def cQ : List Int := [1352506000000, -1355324000000, 1579442000000,
  -511711000000]
def dQ : List Int := [-1355324000000, 3158884000000, -1535133000000]

/-! ### Interval polynomial evaluation (Horner + mean-value form) -/

/-- Interval Horner evaluation of the polynomial with (scaled-integer)
coefficient list `cs`. -/
def horner (cs : List Int) (I : Interval) : Interval :=
  cs.foldr (fun c acc => add (mul acc I) (point c)) (point 0)

/-- Mean-value-form enclosure: `p(m) + p'(L)·(L - m)` with `m` the integer
midpoint.  On a point interval the second factor is exactly `⟨0,0⟩`. -/
def mv (cs dcs : List Int) (L : Interval) : Interval :=
  let m := (L.lo + L.hi) / 2
  add (horner cs (point m)) (mul (horner dcs L) (add L (neg (point m))))

/-! ### `log`/`exp` argument reductions -/

/-- Fixed enclosure of `log 2`. -/
def log2I : Interval := log 13 (point (2 * scale))

def logShiftAux : Nat → Int → Nat
  | 0, _ => 0
  | n + 1, h => if scale ≤ h then 0 else logShiftAux n (2 * h) + 1

/-- Least `k ≥ 0` with `scale ≤ h·2^k` (fuel 64 suffices for all `h ≥ 1`). -/
def logShift (h : Int) : Nat := logShiftAux 64 h

/-- `log` of a positive interval via `log q = log (q·2^k) - k·log 2`
(the scaling `mulNat` by `2^k` is exact). -/
def logPos (I : Interval) : Interval :=
  let k := logShift I.hi
  add (log 13 (mulNat I (2 ^ k))) (neg (mulNat log2I k))

def logPosSafe (I : Interval) : Bool :=
  let k := logShift I.hi
  logSafe 13 (mulNat I (2 ^ k))

/-- `exp` of a negative quantity of magnitude up to `16` via
`exp d = (exp (d/16))^16`. -/
def expNegBig (I : Interval) : Interval :=
  pow (exp 16 (divNat (neg I) 16)) 16

/-! ### Real-valued polynomial semantics and soundness of `horner`/`mv` -/

/-- Real value of the scaled-integer coefficient list: `polyVal cs r = Σ (cᵢ/s)·rⁱ`. -/
noncomputable def polyVal : List Int → ℝ → ℝ
  | [], _ => 0
  | c :: cs, r => value c + r * polyVal cs r

/-- The derivative of `polyVal cs` (as a recursively defined real function). -/
noncomputable def polyDer : List Int → ℝ → ℝ
  | [], _ => 0
  | _ :: cs, r => polyVal cs r + r * polyDer cs r

@[simp] theorem value_zero : value 0 = 0 := by simp [value]

theorem hasDerivAt_polyVal (cs : List Int) (x : ℝ) :
    HasDerivAt (fun r => polyVal cs r) (polyDer cs x) x := by
  induction cs with
  | nil => simpa [polyVal, polyDer] using hasDerivAt_const x (0 : ℝ)
  | cons c cs ih =>
      have h := ((hasDerivAt_id x).mul ih).const_add (value c)
      simp only [polyVal, polyDer, id_eq, one_mul] at h ⊢
      exact h

theorem horner_contains {I : Interval} {x : ℝ} (hx : I.Contains x) :
    ∀ cs : List Int, (horner cs I).Contains (polyVal cs x)
  | [] => by simpa [horner, polyVal] using contains_point 0
  | c :: cs => by
      have h := ((horner_contains hx cs).mul hx).add (contains_point c)
      have hval : polyVal (c :: cs) x = polyVal cs x * x + value c := by
        simp [polyVal]; ring
      rw [hval]
      simpa [horner] using h

theorem value_le_value {a b : Int} (h : a ≤ b) : value a ≤ value b :=
  div_le_div_of_nonneg_right (by exact_mod_cast h) scale_pos_real.le

theorem value_lt_value {a b : Int} (h : a < b) : value a < value b :=
  div_lt_div_of_pos_right (by exact_mod_cast h) scale_pos_real

theorem value_pos {z : Int} (h : 0 < z) : 0 < value z := by
  simpa using value_lt_value h

theorem value_nonneg {z : Int} (h : 0 ≤ z) : 0 ≤ value z := by
  simpa using value_le_value h

theorem value_neg' {z : Int} (h : z < 0) : value z < 0 := by
  simpa using value_lt_value h

theorem value_nonpos {z : Int} (h : z ≤ 0) : value z ≤ 0 := by
  simpa using value_le_value h

theorem value_scale : value scale = 1 := by
  simp [value]
  norm_num [scale]

theorem contains_one : (point scale).Contains (1 : ℝ) := by
  simpa [value_scale] using contains_point scale

/-- Soundness of the mean-value form: if `dcs` evaluates to the derivative of
`cs`'s polynomial, then `mv cs dcs L` encloses `polyVal cs` over `L`. -/
theorem mv_contains {L : Interval} {r : ℝ} (hr : L.Contains r)
    {cs dcs : List Int} (hd : ∀ x : ℝ, polyVal dcs x = polyDer cs x) :
    (mv cs dcs L).Contains (polyVal cs r) := by
  set m : Int := (L.lo + L.hi) / 2 with hm
  have hlohi : L.lo ≤ L.hi := by
    by_contra hcon
    exact absurd (hr.1.trans hr.2) (not_le.2 (value_lt_value (not_le.1 hcon)))
  have hmlo : L.lo ≤ m := by rw [hm]; omega
  have hmhi : m ≤ L.hi := by rw [hm]; omega
  have hvm : L.Contains (value m) := ⟨value_le_value hmlo, value_le_value hmhi⟩
  have hcont : ∀ a b : ℝ, ContinuousOn (fun x => polyVal cs x) (Icc a b) :=
    fun a b => Continuous.continuousOn (continuous_iff_continuousAt.2
      fun x => (hasDerivAt_polyVal cs x).continuousAt)
  obtain ⟨ξ, hξ, heq⟩ : ∃ ξ, L.Contains ξ ∧
      polyVal cs r = polyVal cs (value m) + polyDer cs ξ * (r - value m) := by
    rcases lt_trichotomy r (value m) with hlt | heqr | hgt
    · obtain ⟨ξ, hξmem, hs⟩ := exists_hasDerivAt_eq_slope (fun x => polyVal cs x)
        (fun x => polyDer cs x) hlt (hcont _ _)
        (fun x _ => hasDerivAt_polyVal cs x)
      refine ⟨ξ, ⟨hr.1.trans hξmem.1.le, hξmem.2.le.trans hvm.2⟩, ?_⟩
      have hne : value m - r ≠ 0 := sub_ne_zero.2 (ne_of_gt hlt)
      rw [eq_div_iff hne] at hs
      linear_combination hs
    · exact ⟨r, hr, by rw [heqr]; ring⟩
    · obtain ⟨ξ, hξmem, hs⟩ := exists_hasDerivAt_eq_slope (fun x => polyVal cs x)
        (fun x => polyDer cs x) hgt (hcont _ _)
        (fun x _ => hasDerivAt_polyVal cs x)
      refine ⟨ξ, ⟨hvm.1.trans hξmem.1.le, hξmem.2.le.trans hr.2⟩, ?_⟩
      have hne : r - value m ≠ 0 := sub_ne_zero.2 (ne_of_gt hgt)
      rw [eq_div_iff hne] at hs
      linear_combination -hs
  have h1 := horner_contains (contains_point m) cs
  have h2 : (horner dcs L).Contains (polyDer cs ξ) := by
    rw [← hd ξ]; exact horner_contains hξ dcs
  have h3 : (add L (neg (point m))).Contains (r - value m) := by
    simpa [sub_eq_add_neg] using hr.add (contains_point m).neg
  have h := h1.add (h2.mul h3)
  have hmv : mv cs dcs L =
      add (horner cs (point m)) (mul (horner dcs L) (add L (neg (point m)))) := by
    rw [hm]
    rfl
  rw [hmv, heq]
  exact h

/-! ### Soundness of the argument reductions -/

set_option maxHeartbeats 1000000 in
theorem log2I_safe : logSafe 13 (point (2 * scale)) = true := by decide +kernel

theorem contains_two : (point (2 * scale)).Contains (2 : ℝ) := by
  have h := contains_point (2 * scale)
  have : value (2 * scale) = 2 := by
    unfold value scale
    norm_num
  rwa [this] at h

theorem log2I_contains : log2I.Contains (Real.log 2) :=
  Sound.contains_log_of_safe contains_two log2I_safe

theorem logPos_contains {I : Interval} {q : ℝ} (hq : I.Contains q) (hq0 : 0 < q)
    (hsafe : logPosSafe I = true) : (logPos I).Contains (Real.log q) := by
  set k := logShift I.hi with hk
  have hsafe' : logSafe 13 (mulNat I (2 ^ k)) = true := by
    rw [hk]; exact hsafe
  have hunfold : logPos I = add (log 13 (mulNat I (2 ^ k))) (neg (mulNat log2I k)) := by
    rw [hk]; rfl
  have hq2 : (mulNat I (2 ^ k)).Contains (q * ((2 ^ k : ℕ) : ℝ)) := hq.mulNat
  have hlog := Sound.contains_log_of_safe hq2 hsafe'
  have hlog2k := log2I_contains.mulNat (k := k)
  have h := hlog.add hlog2k.neg
  have hsplit : Real.log (q * ((2 ^ k : ℕ) : ℝ)) + -(Real.log 2 * (k : ℝ)) =
      Real.log q := by
    have h2k : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
    rw [h2k, Real.log_mul hq0.ne' (by positivity), Real.log_pow]
    ring
  rw [hunfold]
  rwa [hsplit] at h

theorem expNegBig_contains {I : Interval} {d : ℝ} (hd : I.Contains d)
    (hsafe : expSafe 16 (divNat (neg I) 16) = true) :
    (expNegBig I).Contains (Real.exp (-d)) := by
  have h1 : (divNat (neg I) 16).Contains (-d / 16) := hd.neg.divNat (by norm_num)
  have h2 := Sound.contains_exp_of_safe h1 hsafe
  have h3 := h2.pow 16
  have hid : Real.exp (-d / 16) ^ 16 = Real.exp (-d) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rwa [hid] at h3

/-! ### Coefficient identities -/

theorem polyVal_cP (r : ℝ) : polyVal cP r = Ppaper r := by
  simp only [cP, polyVal, value, scale, Ppaper]
  push_cast
  ring

theorem polyVal_dP (x : ℝ) : polyVal dP x = polyDer cP x := by
  simp only [cP, dP, polyVal, polyDer, value, scale]
  push_cast
  ring

theorem polyVal_cA (r : ℝ) : polyVal cA r = Ppaper' r - Ppaper r := by
  simp only [cA, polyVal, value, scale, Ppaper, Ppaper']
  push_cast
  ring

theorem polyVal_dA (x : ℝ) : polyVal dA x = polyDer cA x := by
  simp only [cA, dA, polyVal, polyDer, value, scale]
  push_cast
  ring

theorem polyVal_cB (r : ℝ) : polyVal cB r = Ppaper'' r - 2 * Ppaper' r + Ppaper r := by
  simp only [cB, polyVal, value, scale, Ppaper, Ppaper', Ppaper'']
  push_cast
  ring

theorem polyVal_dB (x : ℝ) : polyVal dB x = polyDer cB x := by
  simp only [cB, dB, polyVal, polyDer, value, scale]
  push_cast
  ring

theorem polyVal_cQ (r : ℝ) : polyVal cQ r = Qpaper r := by
  simp only [cQ, polyVal, value, scale, Qpaper]
  push_cast
  ring

theorem polyVal_dQ (x : ℝ) : polyVal dQ x = polyDer cQ x := by
  simp only [cQ, dQ, polyVal, polyDer, value, scale]
  push_cast
  ring

/-! ### Named sub-expressions of the per-cell computation

Each is a function of the cell interval `R` (or the witness point interval).
The generator mirrors these bit-exactly (`CELLSPEC.md` §Checker outline). -/

def onePlusI (R : Interval) : Interval := add (point scale) R

def entI (R : Interval) : Interval :=
  add (mul (onePlusI R) (log 13 (onePlusI R))) (neg (mul R (logPos R)))

def expNegRI (R : Interval) : Interval := exp 16 (neg R)

def FI (R : Interval) : Interval := add (entI R) (mul (expNegRI R) (mv cP dP R))

def DI (R : Interval) : Interval :=
  add (add (log 13 (onePlusI R)) (neg (logPos R))) (mul (expNegRI R) (mv cA dA R))

def D2I (R : Interval) : Interval :=
  add (neg (inv (mul R (onePlusI R)))) (mul (expNegRI R) (mv cB dB R))

def MI (R : Interval) : Interval := mul (mul R (expNegRI R)) (mv cQ dQ R)

def oneMinusMI (R : Interval) : Interval := add (point scale) (neg (MI R))

def pIf (R : Interval) : Interval := add (point scale) (neg (expNegBig (DI R)))

def xIf (R : Interval) : Interval :=
  add (log 13 (oneMinusMI R)) (mul (log 13 (pIf R)) (inv (oneMinusMI R)))

def SbarIf (W : Interval) : Interval := add (FI W) (neg (mul W (DI W)))

/-- Fixed enclosure of `Fpaper 1` (= `FI (point scale)`, cf. `F1I_eq`). -/
def F1I : Interval := ⟨1327542174938, 1327542175013⟩

/-- Fixed enclosure of `Dpaper 1` (= `DI (point scale)`, cf. `D1I_eq`). -/
def D1I : Interval := ⟨761480418862, 761480418902⟩

/-- The per-case enclosure of `S̄` (so `log Y = -S̄`). -/
def SIf (c : CellData) (R : Interval) : Interval :=
  if c.kase = 2 then add F1I (point (xIf R).hi)
  else if c.kase = 0 then SbarIf (point c.w)
  else DI (point c.w)

/-- Enclosure of `ψ(r) = F r + (log X r + r·log M r - r·S̄)/2` over the cell. -/
def psiIf (c : CellData) (R : Interval) : Interval :=
  add (FI R) (divNat (add (xIf R) (add (mul R (logPos (MI R))) (neg (mul R (SIf c R))))) 2)

/-! ### The Boolean checks -/

/-- Safety for the `F`/`D` evaluation chain over `R ⊆ (0,1]`. -/
def baseSafe (R : Interval) : Bool :=
  decide (0 < R.lo) && decide (R.lo ≤ R.hi) && decide (R.hi ≤ scale) &&
  logSafe 13 (onePlusI R) && logPosSafe R && expSafe 16 (neg R)

/-- Safety for the whole per-cell chain (`D2`, `M`, `log M`, `log X`). -/
def cellSafe (R : Interval) : Bool :=
  baseSafe R &&
  positive (mul R (onePlusI R)) &&
  logPosSafe (MI R) &&
  logSafe 13 (oneMinusMI R) &&
  logSafe 13 (pIf R) &&
  expSafe 16 (divNat (neg (DI R)) 16) &&
  positive (pIf R) &&
  positive (oneMinusMI R)

/-- The case-independent inequalities: `inf D > 0`, `sup D2 < 0`,
`M ∈ (0,1)`, `sup log X < 0`. -/
def mainChecks (R : Interval) : Bool :=
  positive (DI R) && decide ((D2I R).hi < 0) &&
  positive (MI R) && decide ((MI R).hi < scale) &&
  decide ((xIf R).hi < 0)

/-- The per-case inequalities (see `CELLSPEC.md`). -/
def caseChecks (c : CellData) (R : Interval) : Bool :=
  if c.kase = 2 then
    decide (0 < F1I.lo + (xIf R).hi) &&
    decide (F1I.hi + (xIf R).hi ≤ D1I.lo) &&
    decide (0 ≤ (xIf R).hi + D1I.lo)
  else
    baseSafe (point c.w) &&
    (if c.kase = 0 then
      decide ((DI (point c.w)).hi + (xIf R).hi ≤ 0) && positive (SbarIf (point c.w))
    else
      decide ((SbarIf (point c.w)).hi + (xIf R).hi ≤ 0) && positive (DI (point c.w)))

/-- The full per-cell check (reference version; see `checkCellFast` for the
evaluation twin used in the generated data files). -/
def checkCell (c : CellData) : Bool :=
  let R : Interval := ⟨c.lo, c.hi⟩
  cellSafe R && mainChecks R && caseChecks c R && positive (psiIf c R)

/-! ### Enclosure soundness -/

theorem value_lt_one {z : Int} (h : z < scale) : value z < 1 := by
  simpa [value_scale] using value_lt_value h

theorem value_le_one {z : Int} (h : z ≤ scale) : value z ≤ 1 := by
  simpa [value_scale] using value_le_value h

theorem baseSafe_elim {R : Interval} (hs : baseSafe R = true) :
    0 < R.lo ∧ R.hi ≤ scale ∧
    logSafe 13 (onePlusI R) = true ∧ logPosSafe R = true ∧
    expSafe 16 (neg R) = true := by
  simp only [baseSafe, Bool.and_eq_true, decide_eq_true_eq] at hs
  tauto

theorem cellSafe_elim {R : Interval} (hs : cellSafe R = true) :
    baseSafe R = true ∧ 0 < (mul R (onePlusI R)).lo ∧
    logPosSafe (MI R) = true ∧ logSafe 13 (oneMinusMI R) = true ∧
    logSafe 13 (pIf R) = true ∧ expSafe 16 (divNat (neg (DI R)) 16) = true ∧
    0 < (pIf R).lo ∧ 0 < (oneMinusMI R).lo := by
  simp only [cellSafe, positive, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hs
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- `F` and `D` enclosures from the base safety checks (used both on the cell
interval and on the witness point interval). -/
theorem FD_contains {R : Interval} {r : ℝ} (hR : R.Contains r)
    (hs : baseSafe R = true) :
    (FI R).Contains (Fpaper r) ∧ (DI R).Contains (Dpaper r) ∧
      r ∈ Ioc (0 : ℝ) 1 := by
  obtain ⟨hlo, hhis, hsafe1, hsafe2, hsafe3⟩ := baseSafe_elim hs
  have hr0 : 0 < r := (value_pos hlo).trans_le hR.1
  have hr1 : r ≤ 1 := hR.2.trans (value_le_one hhis)
  have hOne : (onePlusI R).Contains (1 + r) := contains_one.add hR
  have hlog1p := Sound.contains_log_of_safe hOne hsafe1
  have hlogr := logPos_contains hR hr0 hsafe2
  have hexp : (expNegRI R).Contains (Real.exp (-r)) :=
    Sound.contains_exp_of_safe hR.neg hsafe3
  have hent : (entI R).Contains (entropy r) := by
    have h := (hOne.mul hlog1p).add (hR.mul hlogr).neg
    simpa [entI, entropy, sub_eq_add_neg] using h
  have hP : (mv cP dP R).Contains (Ppaper r) := by
    have h := mv_contains hR polyVal_dP
    rwa [polyVal_cP] at h
  have hA : (mv cA dA R).Contains (Ppaper' r - Ppaper r) := by
    have h := mv_contains hR polyVal_dA
    rwa [polyVal_cA] at h
  refine ⟨?_, ?_, hr0, hr1⟩
  · have h := hent.add (hexp.mul hP)
    simpa [FI, Fpaper] using h
  · have h := (hlog1p.add hlogr.neg).add (hexp.mul hA)
    simpa [DI, Dpaper, sub_eq_add_neg] using h

/-- All cell-level enclosures from `cellSafe`. -/
theorem cell_contains {R : Interval} {r : ℝ} (hR : R.Contains r)
    (hs : cellSafe R = true) :
    (FI R).Contains (Fpaper r) ∧ (DI R).Contains (Dpaper r) ∧
    (D2I R).Contains (D2paper r) ∧ (MI R).Contains (Mpaper r) ∧
      r ∈ Ioc (0 : ℝ) 1 := by
  obtain ⟨hbase, hrr1, _, _, _, _, _, _⟩ := cellSafe_elim hs
  obtain ⟨hF, hD, hr01⟩ := FD_contains hR hbase
  obtain ⟨hlo, hhis, hsafe1, hsafe2, hsafe3⟩ := baseSafe_elim hbase
  have hr0 : 0 < r := hr01.1
  have hOne : (onePlusI R).Contains (1 + r) := contains_one.add hR
  have hexp : (expNegRI R).Contains (Real.exp (-r)) :=
    Sound.contains_exp_of_safe hR.neg hsafe3
  have hB : (mv cB dB R).Contains (Ppaper'' r - 2 * Ppaper' r + Ppaper r) := by
    have h := mv_contains hR polyVal_dB
    rwa [polyVal_cB] at h
  have hQ : (mv cQ dQ R).Contains (Qpaper r) := by
    have h := mv_contains hR polyVal_dQ
    rwa [polyVal_cQ] at h
  refine ⟨hF, hD, ?_, ?_, hr01⟩
  · have hprod : (mul R (onePlusI R)).Contains (r * (1 + r)) := hR.mul hOne
    have hinv := hprod.inv hrr1
    have h := hinv.neg.add (hexp.mul hB)
    simpa [D2I, D2paper, one_div] using h
  · have h := (hR.mul hexp).mul hQ
    simpa [MI, Mpaper] using h

/-- The `log X` enclosure over the cell, together with the pointwise facts it
needs (`D > 0`, `M ∈ (0,1)` from `mainChecks`). -/
theorem x_contains {R : Interval} {r : ℝ} (hR : R.Contains r)
    (hs : cellSafe R = true)
    (hDpos : 0 < (DI R).lo) (hMpos : 0 < (MI R).lo) (hMlt : (MI R).hi < scale) :
    (xIf R).Contains (Real.log (Xpaper r)) ∧
      Mpaper r ∈ Ioo (0 : ℝ) 1 ∧ 0 < Dpaper r := by
  obtain ⟨hbase, hrr1, hsafeM, hsafe1M, hsafeP, hsafeE, hpPos, h1MPos⟩ :=
    cellSafe_elim hs
  obtain ⟨hF, hD, hD2, hM, hr01⟩ := cell_contains hR hs
  have hD0 : 0 < Dpaper r := (value_pos hDpos).trans_le hD.1
  have hMIoo : Mpaper r ∈ Ioo (0 : ℝ) 1 :=
    ⟨(value_pos hMpos).trans_le hM.1, hM.2.trans_lt (value_lt_one hMlt)⟩
  have hOneM : (oneMinusMI R).Contains (1 - Mpaper r) := by
    simpa [oneMinusMI, sub_eq_add_neg] using contains_one.add hM.neg
  have hpC : (pIf R).Contains (1 - Real.exp (-Dpaper r)) := by
    simpa [pIf, sub_eq_add_neg] using
      contains_one.add (expNegBig_contains hD hsafeE).neg
  have hlogp := Sound.contains_log_of_safe hpC hsafeP
  have hlog1M := Sound.contains_log_of_safe hOneM hsafe1M
  have hinv := hOneM.inv h1MPos
  have h := hlog1M.add (hlogp.mul hinv)
  rw [log_Xpaper hD0 hMIoo]
  refine ⟨?_, hMIoo, hD0⟩
  have hshape : Real.log (1 - Real.exp (-Dpaper r)) / (1 - Mpaper r) +
      Real.log (1 - Mpaper r) =
      Real.log (1 - Mpaper r) +
        Real.log (1 - Real.exp (-Dpaper r)) * (1 - Mpaper r)⁻¹ := by
    rw [div_eq_mul_inv]; ring
  rw [hshape]
  exact h

/-! ### The fixed enclosures at `r = 1` -/

set_option maxHeartbeats 4000000 in
theorem base1_safe : baseSafe (point scale) = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem F1I_eq : FI (point scale) = F1I := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem D1I_eq : DI (point scale) = D1I := by decide +kernel

theorem F1I_contains : F1I.Contains (Fpaper 1) := by
  have h := (FD_contains contains_one base1_safe).1
  rwa [F1I_eq] at h

theorem D1I_contains : D1I.Contains (Dpaper 1) := by
  have h := (FD_contains contains_one base1_safe).2.1
  rwa [D1I_eq] at h

/-! ### Soundness of the slack (C2) check -/

theorem psi_slack {c : CellData} {R : Interval} {r Sb : ℝ}
    (hF : (FI R).Contains (Fpaper r))
    (hx : (xIf R).Contains (Real.log (Xpaper r)))
    (hR : R.Contains r)
    (hlogM : (logPos (MI R)).Contains (Real.log (Mpaper r)))
    (hS : (SIf c R).Contains Sb)
    (hpsi : 0 < (psiIf c R).lo) :
    0 < Fpaper r +
      (Real.log (Xpaper r) + (r * Real.log (Mpaper r) + -(r * Sb))) / 2 := by
  have hcont : (psiIf c R).Contains
      (Fpaper r +
        (Real.log (Xpaper r) + (r * Real.log (Mpaper r) + -(r * Sb))) / 2) := by
    have h := hF.add
      ((hx.add ((hR.mul hlogM).add ((hR.mul hS).neg))).divNat (k := 2) (by norm_num))
    simpa [psiIf, Nat.cast_ofNat] using h
  exact (value_pos hpsi).trans_le hcont.1

/-! ### The main per-cell soundness theorem -/

theorem checkCell_sound (c : CellData) (h : checkCell c = true) :
    (∀ r ∈ Icc (value c.lo) (value c.hi), 0 < Dpaper r ∧ D2paper r < 0) ∧
    (TangentUB → (∀ u ∈ Ioc (0 : ℝ) 1, Fpaper u ≤ (1 + u) * Dpaper u) →
      ∀ r ∈ Icc (value c.lo) (value c.hi) ∩ Ioc (0 : ℝ) 1, LadderFactsAt r) := by
  have h' : cellSafe ⟨c.lo, c.hi⟩ = true ∧ mainChecks ⟨c.lo, c.hi⟩ = true ∧
      caseChecks c ⟨c.lo, c.hi⟩ = true ∧ 0 < (psiIf c ⟨c.lo, c.hi⟩).lo := by
    simpa [checkCell, positive, Bool.and_eq_true, decide_eq_true_eq,
      and_assoc] using h
  obtain ⟨hsafe, hmain, hcase, hpsi⟩ := h'
  set R : Interval := ⟨c.lo, c.hi⟩ with hRdef
  have hmain' : 0 < (DI R).lo ∧ (D2I R).hi < 0 ∧ 0 < (MI R).lo ∧
      (MI R).hi < scale ∧ (xIf R).hi < 0 := by
    simpa [mainChecks, positive, Bool.and_eq_true, decide_eq_true_eq,
      and_assoc] using hmain
  obtain ⟨hDpos, hD2neg, hMpos, hMlt, _hxneg⟩ := hmain'
  constructor
  · -- derivative sign facts
    intro r hr
    have hRc : R.Contains r := ⟨hr.1, hr.2⟩
    obtain ⟨-, hD, hD2, -, -⟩ := cell_contains hRc hsafe
    exact ⟨(value_pos hDpos).trans_le hD.1, hD2.2.trans_lt (value_neg' hD2neg)⟩
  · -- ladder facts
    intro hT hkink r hr
    obtain ⟨hrIcc, hrIoc⟩ := hr
    have hRc : R.Contains r := ⟨hrIcc.1, hrIcc.2⟩
    obtain ⟨hF, hD, hD2, hM, hr01⟩ := cell_contains hRc hsafe
    obtain ⟨hx, hMIoo, hD0⟩ := x_contains hRc hsafe hDpos hMpos hMlt
    have hXIoo := Xpaper_mem_Ioo hD0 hMIoo
    have hlogM : (logPos (MI R)).Contains (Real.log (Mpaper r)) := by
      obtain ⟨-, -, hsafeM, -, -, -, -, -⟩ := cellSafe_elim hsafe
      exact logPos_contains hM hMIoo.1 hsafeM
    refine ⟨hMIoo, hXIoo, ?_⟩
    by_cases hk2 : c.kase = 2
    · -- kink case (`t₀ = 1`)
      have hcase' : 0 < F1I.lo + (xIf R).hi ∧ F1I.hi + (xIf R).hi ≤ D1I.lo ∧
          0 ≤ (xIf R).hi + D1I.lo := by
        simpa [caseChecks, hk2, Bool.and_eq_true, decide_eq_true_eq,
          and_assoc] using hcase
      obtain ⟨hkA, hkB, hkC⟩ := hcase'
      have hvA : 0 < value F1I.lo + value (xIf R).hi := by
        have := value_pos hkA
        rwa [value_add] at this
      have hvB : value F1I.hi + value (xIf R).hi ≤ value D1I.lo := by
        have := value_le_value hkB
        rwa [value_add] at this
      have hvC : 0 ≤ value (xIf R).hi + value D1I.lo := by
        have := value_nonneg hkC
        rwa [value_add] at this
      have hlx : Real.log (Xpaper r) ≤ value (xIf R).hi := hx.2
      have hlo : -Dpaper 1 ≤ value (xIf R).hi := by
        have := D1I_contains.1
        linarith
      have hhi : value (xIf R).hi ≤ Dpaper 1 - Fpaper 1 := by
        have h1 := F1I_contains.2
        have h2 := D1I_contains.1
        linarith
      have hly : -(Fpaper 1 + value (xIf R).hi) < 0 := by
        have := F1I_contains.1
        linarith
      have hS : (SIf c R).Contains (Fpaper 1 + value (xIf R).hi) := by
        have h := F1I_contains.add (contains_point (xIf R).hi)
        simpa [SIf, hk2] using h
      have hslack0 := psi_slack hF hx hRc hlogM hS hpsi
      refine exists_Y_of_logY hly (admissible_caseC hT hlx hlo hhi) ?_
      ring_nf at hslack0 ⊢
      linarith
    · -- witness cases
      have hcase' : baseSafe (point c.w) = true ∧
          (if c.kase = 0 then
            decide ((DI (point c.w)).hi + (xIf R).hi ≤ 0) &&
              positive (SbarIf (point c.w))
          else
            decide ((SbarIf (point c.w)).hi + (xIf R).hi ≤ 0) &&
              positive (DI (point c.w))) = true := by
        simpa [caseChecks, hk2, Bool.and_eq_true] using hcase
      obtain ⟨hbW, hcaseW⟩ := hcase'
      obtain ⟨hFw, hDw, hu01⟩ := FD_contains (contains_point c.w) hbW
      have hSbarC : (SbarIf (point c.w)).Contains
          (Fpaper (value c.w) - value c.w * Dpaper (value c.w)) := by
        have h := hFw.add ((contains_point c.w).mul hDw).neg
        simpa [SbarIf, sub_eq_add_neg] using h
      have hkinkw := hkink (value c.w) hu01
      by_cases hk0 : c.kase = 0
      · -- `t₀ = 1/u₀ > 1`, `log Y = -(F u₀ - u₀ D u₀)`
        have hcw : (DI (point c.w)).hi + (xIf R).hi ≤ 0 ∧
            0 < (SbarIf (point c.w)).lo := by
          simpa [hk0, positive, Bool.and_eq_true, decide_eq_true_eq] using hcaseW
        have hvsum : value (DI (point c.w)).hi + value (xIf R).hi ≤ 0 := by
          have := value_nonpos hcw.1
          rwa [value_add] at this
        have hC1 : Dpaper (value c.w) ≤ -Real.log (Xpaper r) := by
          have h1 := hDw.2
          have h2 := hx.2
          linarith
        have hly : value c.w * Dpaper (value c.w) - Fpaper (value c.w) < 0 := by
          have h1 := (value_pos hcw.2).trans_le hSbarC.1
          linarith
        have hS : (SIf c R).Contains
            (Fpaper (value c.w) - value c.w * Dpaper (value c.w)) := by
          simpa [SIf, hk2, hk0] using hSbarC
        have hslack0 := psi_slack hF hx hRc hlogM hS hpsi
        refine exists_Y_of_logY hly (admissible_caseB hT hu01 hkinkw hC1) ?_
        ring_nf at hslack0 ⊢
        linarith
      · -- `t₀ = u₀ ≤ 1`, `log Y = -D u₀`
        have hcw : (SbarIf (point c.w)).hi + (xIf R).hi ≤ 0 ∧
            0 < (DI (point c.w)).lo := by
          simpa [hk0, positive, Bool.and_eq_true, decide_eq_true_eq] using hcaseW
        have hvsum : value (SbarIf (point c.w)).hi + value (xIf R).hi ≤ 0 := by
          have := value_nonpos hcw.1
          rwa [value_add] at this
        have hC1 : Fpaper (value c.w) - value c.w * Dpaper (value c.w) ≤
            -Real.log (Xpaper r) := by
          have h1 := hSbarC.2
          have h2 := hx.2
          linarith
        have hly : -Dpaper (value c.w) < 0 := by
          have h1 := (value_pos hcw.2).trans_le hDw.1
          linarith
        have hS : (SIf c R).Contains (Dpaper (value c.w)) := by
          simpa [SIf, hk2, hk0] using hDw
        have hslack0 := psi_slack hF hx hRc hlogM hS hpsi
        refine exists_Y_of_logY hly (admissible_caseA hT hu01 hkinkw hC1) ?_
        ring_nf at hslack0 ⊢
        linarith

/-- Evaluation twin of `checkCell` with `let`-sharing of the common
sub-expressions (the kernel caches reductions of shared sub-terms, so `decide`
on `checkCellFast` avoids recomputing `DI R`, `MI R`, `xIf R`, …).
Definitionally equal to `checkCell` (`checkCellFast_eq`); the generated data
files state their kernel facts about `checkCellFast`. -/
def checkCellFast (c : CellData) : Bool :=
  let R : Interval := ⟨c.lo, c.hi⟩
  let onePlus := add (point scale) R
  let log1p := log 13 onePlus
  let logr := logPos R
  let ent := add (mul onePlus log1p) (neg (mul R logr))
  let e := exp 16 (neg R)
  let FL := add ent (mul e (mv cP dP R))
  let DL := add (add log1p (neg logr)) (mul e (mv cA dA R))
  let D2L := add (neg (inv (mul R onePlus))) (mul e (mv cB dB R))
  let ML := mul (mul R e) (mv cQ dQ R)
  let oneMinusM := add (point scale) (neg ML)
  let pL := add (point scale) (neg (expNegBig DL))
  let xL := add (log 13 oneMinusM) (mul (log 13 pL) (inv oneMinusM))
  let W : Interval := point c.w
  let onePlusW := add (point scale) W
  let log1pW := log 13 onePlusW
  let logw := logPos W
  let entW := add (mul onePlusW log1pW) (neg (mul W logw))
  let eW := exp 16 (neg W)
  let FW := add entW (mul eW (mv cP dP W))
  let DW := add (add log1pW (neg logw)) (mul eW (mv cA dA W))
  let SbarW := add FW (neg (mul W DW))
  let SL : Interval :=
    if c.kase = 2 then add F1I (point xL.hi)
    else if c.kase = 0 then SbarW
    else DW
  let psiL := add FL (divNat (add xL (add (mul R (logPos ML)) (neg (mul R SL)))) 2)
  -- cellSafe
  (decide (0 < R.lo) && decide (R.lo ≤ R.hi) && decide (R.hi ≤ scale) &&
    logSafe 13 onePlus && logPosSafe R && expSafe 16 (neg R) &&
    positive (mul R onePlus) && logPosSafe ML && logSafe 13 oneMinusM &&
    logSafe 13 pL && expSafe 16 (divNat (neg DL) 16) && positive pL &&
    positive oneMinusM) &&
  -- mainChecks
  (positive DL && decide (D2L.hi < 0) && positive ML && decide (ML.hi < scale) &&
    decide (xL.hi < 0)) &&
  -- caseChecks
  (if c.kase = 2 then
    decide (0 < F1I.lo + xL.hi) && decide (F1I.hi + xL.hi ≤ D1I.lo) &&
    decide (0 ≤ xL.hi + D1I.lo)
  else
    (decide (0 < W.lo) && decide (W.lo ≤ W.hi) && decide (W.hi ≤ scale) &&
      logSafe 13 onePlusW && logPosSafe W && expSafe 16 (neg W)) &&
    (if c.kase = 0 then
      decide (DW.hi + xL.hi ≤ 0) && positive SbarW
    else
      decide (SbarW.hi + xL.hi ≤ 0) && positive DW)) &&
  positive psiL

theorem checkCellFast_eq : checkCellFast = checkCell := rfl

/-! ### Chain (coverage) layer -/

/-- `chainBetween a b l`: the cells of `l` tile `[a/s, b/s]` exactly:
consecutive cells share their integer endpoints, starting at `a`, ending
at `b`. -/
def chainBetween (a b : Int) : List CellData → Bool
  | [] => decide (a = b)
  | c :: l => decide (c.lo = a) && chainBetween c.hi b l

theorem chainBetween_append {a b d : Int} {l₁ l₂ : List CellData}
    (h₁ : chainBetween a b l₁ = true) (h₂ : chainBetween b d l₂ = true) :
    chainBetween a d (l₁ ++ l₂) = true := by
  induction l₁ generalizing a with
  | nil =>
      have : a = b := by simpa [chainBetween] using h₁
      simpa [this] using h₂
  | cons c l ih =>
      simp only [chainBetween, Bool.and_eq_true, decide_eq_true_eq,
        List.cons_append] at h₁ ⊢
      exact ⟨h₁.1, ih h₁.2⟩

/-- Full coverage of `[λ₀, 1]`: the chain starts at or below
`953674 < 2^{-20}·10^12` and ends exactly at `scale`. -/
def checkCover (l : List CellData) : Bool :=
  match l with
  | [] => false
  | c :: _ => decide (c.lo ≤ 953674) && chainBetween c.lo scale l

/-- Coverage: any pointwise property established per cell holds on the whole
half-open chain range `(a/s, b/s]`. -/
theorem chain_cover {P : ℝ → Prop}
    (hP : ∀ c : CellData, checkCell c = true →
      ∀ r ∈ Icc (value c.lo) (value c.hi), P r) :
    ∀ (l : List CellData) (a b : Int), chainBetween a b l = true →
      l.all checkCell = true → ∀ r : ℝ, value a < r → r ≤ value b → P r := by
  intro l
  induction l with
  | nil =>
      intro a b hc _ r h1 h2
      have hab : a = b := by simpa [chainBetween] using hc
      rw [hab] at h1
      linarith
  | cons c l ih =>
      intro a b hc hall r h1 h2
      have hc' : c.lo = a ∧ chainBetween c.hi b l = true := by
        simpa [chainBetween, Bool.and_eq_true, decide_eq_true_eq] using hc
      have hall' : checkCell c = true ∧ l.all checkCell = true := by
        simpa [List.all_cons, Bool.and_eq_true] using hall
      by_cases hr : r ≤ value c.hi
      · refine hP c hall'.1 r ⟨?_, hr⟩
        rw [hc'.1]
        exact h1.le
      · exact ih c.hi b hc'.2 hall'.2 r (lt_of_not_ge hr) h2

theorem lam0_boundary {z : Int} (h : z ≤ 953674) : value z < lam0 := by
  have h1 : value z ≤ value 953674 := value_le_value h
  have h2 : value 953674 < lam0 := by
    unfold value scale lam0
    norm_num
  linarith

/-- The full coverage soundness: from the two kernel facts about the generated
list, both certificate-region goals follow. -/
theorem checkCover_sound {l : List CellData}
    (hcov : checkCover l = true) (hall : l.all checkCell = true) :
    (∀ r ∈ Icc lam0 (1 : ℝ), 0 < Dpaper r ∧ D2paper r < 0) ∧
    (TangentUB → (∀ u ∈ Ioc (0 : ℝ) 1, Fpaper u ≤ (1 + u) * Dpaper u) →
      ∀ r ∈ Icc lam0 (1 : ℝ), LadderFactsAt r) := by
  match l with
  | [] => simp [checkCover] at hcov
  | c :: l' =>
    have hcov' : c.lo ≤ 953674 ∧ chainBetween c.lo scale (c :: l') = true := by
      simpa [checkCover, Bool.and_eq_true, decide_eq_true_eq] using hcov
    have hstart : ∀ r ∈ Icc lam0 (1 : ℝ), value c.lo < r ∧ r ≤ value scale := by
      intro r hr
      exact ⟨(lam0_boundary hcov'.1).trans_le hr.1, by rw [value_scale]; exact hr.2⟩
    have hIoc : ∀ r ∈ Icc lam0 (1 : ℝ), r ∈ Ioc (0 : ℝ) 1 := by
      intro r hr
      have : (0 : ℝ) < lam0 := by norm_num [lam0]
      exact ⟨lt_of_lt_of_le this hr.1, hr.2⟩
    constructor
    · intro r hr
      exact chain_cover
        (fun d hd => (checkCell_sound d hd).1) (c :: l') c.lo scale
        hcov'.2 hall r (hstart r hr).1 (hstart r hr).2
    · intro hT hkink r hr
      exact chain_cover
        (P := fun x => x ∈ Ioc (0 : ℝ) 1 → LadderFactsAt x)
        (fun d hd x hx hx01 => (checkCell_sound d hd).2 hT hkink x ⟨hx, hx01⟩)
        (c :: l') c.lo scale hcov'.2 hall r (hstart r hr).1 (hstart r hr).2
        (hIoc r hr)

#eval FI (point scale)  -- expect ⟨1327542174938, 1327542175013⟩
#eval DI (point scale)  -- expect ⟨761480418862, 761480418902⟩
#eval checkCell ⟨953674, 958234, 2638760, 1⟩  -- near λ₀, case t₀ ≤ 1
#eval checkCell ⟨999990000000, 1000000000000, 241560000000, 0⟩  -- near r = 1
#eval checkCell ⟨300000000000, 300010000000, 1000000000000, 2⟩  -- kink zone

end CertCheck
end Bootstrap
end RamseyLean

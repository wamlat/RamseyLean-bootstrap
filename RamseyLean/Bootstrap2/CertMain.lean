import RamseyLean.Bootstrap2.CertData2.CertData2
import RamseyLean.Bootstrap2.Main2

/-!
# The concrete certificate theorems

The 35 770-cell certificate `CertData2.allCells` (emitted from
`pq_cert_final.json`, generated from the 10 560-interval fixed point of the
both-orientation self-consistent bootstrap) passes all four Boolean passes,
so `Fcert allCells` is a valid uniform exponential Ramsey bound with

  `F(1) = 2653604512524788171208898 / (2·10²⁴) = 1.32680225…`,
  `exp F(1) = 3.76897189… ≤ 3.7690`.

Final statements:
* `main_bootstrap2 : UniformRamseyExpBound (Fcert allCells)`
* `bootstrap2_diagonal : R(k,k) ≤ exp ((F_N + ε) k)` eventually, `F_N` the
  explicit rational above;
* `bootstrap2_diagonal_num : R(k,k) ≤ 3.7690^k` eventually.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

namespace RamseyLean
namespace Bootstrap2

open Set Filter CertData2

/-- Every cell passes `checkCell`. -/
theorem allCells_check : allCells.all checkCell = true := by
  rw [← checkCellFast_eq]; exact allCells_ok

theorem allCells_chain : checkChain allCells = true := by decide +kernel

theorem allCells_wit : checkWitnesses allCells = true := by decide +kernel

theorem allCells_tail : checkTail allCells = true := by decide +kernel

/-- The last cell of the certificate (whose `n1.F` is the diagonal value). -/
def lastCell : Cell :=
  ⟨⟨999948958333, 2653526738865849772019488, 761873756461, 392416722731⟩,
   ⟨1000000000000, 2653604512524788171208898, 761855061769, 392416722731⟩,
   215826269111, 831228246086,
   ⟨999897916667, 2653448963300018702616230, 761892451152, 392416722731⟩,
   ⟨240227777777, 1106367968235842123098880, 1533268675466, 200430999372⟩⟩

theorem allCells_last : allCells.getLast? = some lastCell := by decide +kernel

/-- **Main theorem**: the certificate's spline is a valid uniform exponential
Ramsey bound: `R(k,ℓ) ≤ exp (Fcert (ℓ/k) k + o(k))` uniformly in `1 ≤ ℓ ≤ k`. -/
theorem main_bootstrap2 : UniformRamseyExpBound (Fcert allCells) :=
  main_cert allCells_check allCells_chain allCells_wit allCells_tail

/-- Diagonal form with the explicit rational exponent. -/
theorem bootstrap2_diagonal :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k : ℕ in atTop,
        (ramseyNumber k k : ℝ) ≤
          Real.exp (((2653604512524788171208898 : ℝ) / (2 * 10 ^ 24) + ε) *
            (k : ℝ)) := by
  have h := cert_diagonal allCells_check allCells_chain allCells_wit
    allCells_tail allCells_last
  intro ε hε
  have h' := h ε hε
  have hFR : lastCell.n1.FR =
      (2653604512524788171208898 : ℝ) / (2 * 10 ^ 24) := by
    show ((2653604512524788171208898 : Int) : ℝ) / ((FS : Int) : ℝ) = _
    norm_num [FS]
  rwa [hFR] at h'

/-- The numeric enclosure `exp (F_N + 10⁻⁶) ≤ 3.7690`, by interval
arithmetic in the kernel (`exp` of the halved argument, squared). -/
theorem exp_FN_le :
    Real.exp ((2653604512524788171208898 : ℝ) / (2 * 10 ^ 24) + 1 / 1000000) ≤
      37690 / 10000 := by
  set x : ℝ := (2653604512524788171208898 : ℝ) / (2 * 10 ^ 24) + 1 / 1000000
    with hx
  have hI : (add (fpt 2653604512524788171208898)
      (Interval.point 1000000)).Contains x := by
    have h1 := fpt_contains 2653604512524788171208898
    have h2 := contains_point (1000000 : Int)
    have := h1.add h2
    convert this using 2
    · norm_num [FS]
    · show (1 : ℝ) / 1000000 = value 1000000
      norm_num [value, scale]
  have hIh : ((add (fpt 2653604512524788171208898)
      (Interval.point 1000000)).divNat 2).Contains (x / 2) := by
    have := hI.divNat (k := 2) (by norm_num)
    simpa [div_eq_mul_inv] using this
  have hsafe : expSafe 16 ((add (fpt 2653604512524788171208898)
      (Interval.point 1000000)).divNat 2) = true := by decide +kernel
  have hE := contains_exp_of_safe hIh hsafe
  have hE2 := hE.mul hE
  rw [← Real.exp_add] at hE2
  have hxx : x / 2 + x / 2 = x := by ring
  rw [hxx] at hE2
  have hhi : Real.exp x ≤ value ((mul
      (exp 16 ((add (fpt 2653604512524788171208898)
        (Interval.point 1000000)).divNat 2))
      (exp 16 ((add (fpt 2653604512524788171208898)
        (Interval.point 1000000)).divNat 2))).hi) := hE2.2
  refine hhi.trans ?_
  have hb : (mul
      (exp 16 ((add (fpt 2653604512524788171208898)
        (Interval.point 1000000)).divNat 2))
      (exp 16 ((add (fpt 2653604512524788171208898)
        (Interval.point 1000000)).divNat 2))).hi ≤ 3769000000000 := by
    decide +kernel
  calc value ((mul (exp 16 ((add (fpt 2653604512524788171208898)
          (Interval.point 1000000)).divNat 2))
        (exp 16 ((add (fpt 2653604512524788171208898)
          (Interval.point 1000000)).divNat 2))).hi)
      ≤ value 3769000000000 := by
        unfold value
        have hsc : (0:ℝ) < (scale : ℝ) := scale_pos_real
        exact div_le_div_of_nonneg_right (by exact_mod_cast hb) hsc.le
    _ = 37690 / 10000 := by norm_num [value, scale]

/-- **Numeric diagonal corollary**: `R(k,k) ≤ 3.7690^k` for all large `k`. -/
theorem bootstrap2_diagonal_num :
    ∀ᶠ k : ℕ in atTop,
      (ramseyNumber k k : ℝ) ≤ (37690 / 10000 : ℝ) ^ k := by
  filter_upwards [bootstrap2_diagonal (1 / 1000000) (by norm_num)] with k hk
  refine hk.trans ?_
  have hrw : ((2653604512524788171208898 : ℝ) / (2 * 10 ^ 24) + 1 / 1000000) *
      (k : ℝ) = (k : ℝ) *
      ((2653604512524788171208898 : ℝ) / (2 * 10 ^ 24) + 1 / 1000000) := by
    ring
  rw [hrw, Real.exp_nat_mul]
  exact pow_le_pow_left (Real.exp_pos _).le exp_FN_le k

end Bootstrap2
end RamseyLean

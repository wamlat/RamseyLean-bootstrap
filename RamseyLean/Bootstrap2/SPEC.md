# Spline-certificate specification (Bootstrap2)

Shared contract between the Python generator (`bootstrap/combined/pq_export.py`,
verifier `verify_pq.py` in the Conductor workspace) and the Lean development
`RamseyLean/Bootstrap2/`.  Target theorem: `R(k,k) ≤ c^{k+o(k)}` with
`c = exp(F(1)) ≈ 3.7690`, via the already-formalised ladder theorem
`RamseyLean.uniformRamseyExpBound_selfConsistent` (SelfConsistent.lean), whose
hypotheses we discharge for a **data-defined C¹ piecewise-quadratic concave F**.

## 0. Shape of the construction

Certificate = ordered list of cells covering `[λ₀, 1]`, `λ₀ = 10^{-4}`.
Node data `(λ_j, F_j, d_j, M_j)`, `j = 0..N`; cell `j` spans `[λ_j, λ_{j+1}]`
and carries constants `X_j, Y_j` and two tangent-witness nodes `wa_j, wb_j`
(each witness IS one of the certificate's nodes; validated by a global merge
pass, §5).

Real functions fed to the ladder theorem (all defined in Lean from the data,
`Bootstrap2/Defs.lean`):

* `D : ℝ → ℝ` — piecewise-linear interpolation of `(λ_j, d_j)`, **clamped**
  (constant `d_0` on `(-∞, λ₀]`, constant `d_N` on `[1, ∞)`).
* `M : ℝ → ℝ` — same for `(λ_j, M_j)`.
* `F : ℝ → ℝ` — `F r = F₀⁺ + ∫_{λ₀}^{r} D(t) dt` where `F₀⁺ := F_0` (real value
  of the scaled `F_0`).  On cell `j`, `F` is the quadratic with `F(λ_j) = F_j`,
  `F' = D`; on the tail `(0, λ₀]` it is linear with slope `d_0`.
* `X, Y : ℝ → ℝ` — step functions: value `X_j, Y_j` on `(λ_j, λ_{j+1}]`,
  clamped to `X_0, Y_0` on `(-∞, λ₀]` (tail reuses cell 0's pair).

The exact-integer consistency `F_{j+1} = F_j + (d_j + d_{j+1})(λ_{j+1} - λ_j)/2`
(§2) makes `F(λ_j) = value of F_j` exact.

## 1. Scales

* `SC = 10^12` for `λ, d, M, X, Y` (Int, same scale as
  `RamseyLean.Analysis.FixedPointInterval`).
* `FS = 2 * 10^24 = 2 * SC^2` for `F` (Int).  Then the chain identity of §2 is
  exact integer arithmetic.
* Real value of a node: `lam_j = L_j / SC`, `F(lam_j) = Fj / FS`, `D(lam_j) = Dj / SC`,
  `M(lam_j) = Mj / SC`.
* Interval ops at scale `SC` (existing `FixedPointInterval`).  Downscaling an
  `F`-value into an `SC`-interval: `fpt (f : Int) : Interval := ⟨f.fdiv (2*SC), -((-f).fdiv (2*SC))⟩`
  (floor/ceil directed rounding; width ≤ 1 ulp).

## 2. Data structures (Lean, `Bootstrap2/Defs.lean`)

```lean
structure Node where
  lam : Int  -- scale SC
  F   : Int  -- scale FS
  d   : Int  -- scale SC
  M   : Int  -- scale SC
deriving Repr, DecidableEq

structure Cell where
  n0 : Node
  n1 : Node
  X  : Int   -- scale SC, cell constant
  Y  : Int   -- scale SC, cell constant
  wa : Node  -- tangent witness, orientation a  (−log X − s log Y ≥ F s)
  wb : Node  -- tangent witness, orientation b  (−log Y − s log X ≥ F s)
deriving Repr, DecidableEq
```

Chain conditions (part of `checkChain`, structural walk):
* first cell: `n0.lam = 10^8` (= λ₀·SC); last cell: `n1.lam = SC`;
* consecutive cells `c, c'`: `c.n1 = c'.n0` (full `Node` equality);
* per cell: `n0.lam < n1.lam`, `0 < n1.d ≤ n0.d` (positivity + concavity),
  `0 < n0.M`, `n0.M ≤ n1.M`? — **NO monotonicity of M is assumed**; instead the
  per-cell box uses `Mlo = min(n0.M, n1.M)`, `Mhi = max(n0.M, n1.M)`;
* exact F-chain: `n1.F = n0.F + (n0.d + n1.d) * (n1.lam - n0.lam)`
  (both sides scale FS; note `(d·SC)(λ·SC)` has scale `SC² = FS/2`, and the
  trapezoid has the factor 1/2, so the raw product is exactly the increment).

## 3. Per-cell checker (`Bootstrap2/Check.lean`), all in `Interval` ops

Notation: `pt z = Interval.point z`, cell box intervals
`DIc = ⟨n1.d, n0.d⟩`, `MIc = ⟨Mlo, Mhi⟩`, real points `LI1 = pt n1.lam`.
Enclosures (each must pass its `Safe` predicate, `&&`-ed into the check):

```
lX  = logPos (pt X)                    -- log X_j  (X < SC checked)
lY  = logPos (pt Y)
lM  = logPos (pt Mlo)
oneMinusM = add (pt SC) (neg MIc)      -- 1 − M over the box
pI  = add (pt SC) (neg (expNegBig DIc))            -- 1 − e^{−D} over the box
rhsLog = add (mul (log 13 pI) (inv oneMinusM)) (log 13 oneMinusM)
                                       -- log[(1−e^{−D})^{1/(1−M)}(1−M)] over the box
Sa  = fpt wa.F  −  (pt wa.lam) * (pt wa.d)   -- S̄a = F(u_a) − u_a·d(u_a), Interval
Sb  = fpt wb.F  −  (pt wb.lam) * (pt wb.d)
-- ψ: two-endpoint form (v2, replaces the single crude psiLo)
lM0 = logPos (pt n0.M);  lM1 = logPos (pt n1.M)
psiLo0 = add (fpt n0.F) (divNat (add (add lX (mul (pt n0.lam) lM0)) (mul (pt n0.lam) lY)) 2)
psiLo1 = add (fpt n1.F) (divNat (add (add lX (mul (pt n1.lam) lM1)) (mul (pt n1.lam) lY)) 2)
dip    = divNat (mul (add lM1 (neg lM0)) (add (pt n1.lam) (neg (pt n0.lam)))) 8
```

Boolean checks per cell (in addition to chain conditions §2):

* (P)  `0 < X < SC`, `0 < Y < SC`, `0 < Mlo`, `Mhi < SC`  — Int comparisons.
* (XLE) `lX.hi ≤ rhsLog.lo`  — `X_j ≤ (1−e^{−D r})^{1/(1−M r)}(1−M r)` ∀r in cell.
* (A1) `Sa.hi ≤ −lX.lo`? Stated as `Sa.hi + lX.hi ≤ 0`… careful: need
  `S̄a ≤ −log X_j`, i.e. `(Sa + lX).hi ≤ 0` — use `(add Sa lX).hi ≤ 0`.
* (A2) `(add (add Sa (pt wa.d)) (add lX lY)).hi ≤ 0` — `S̄a + d(u_a) ≤ −log X − log Y`.
* (B1) `(add Sb lY).hi ≤ 0` — `S̄b ≤ −log Y_j`.
* (B2) `(add (add Sb (pt wb.d)) (add lY lX)).hi ≤ 0`.
* (MMONO) `n0.M ≤ n1.M` — Int comparison (needed for the ψ dip sign and the
  `log`-chord direction).
* (PSI0) `0 < (add psiLo0 (neg dip)).lo` and (PSI1) `0 < (add psiLo1 (neg dip)).lo`
  — hslack (`denseCaseExponent < F`) over the cell.  Soundness: write
  `r = (1−t)a + t b`, `a = n0.lamR`, `b = n1.lamR`, `t ∈ (0,1]`.  Then
  `F r ≥ (1−t)F(a) + tF(b)` (concavity ⟹ chord below), and `M r` is the linear
  interpolant, so `log (M r) ≥ (1−t)·log M₀ + t·log M₁` (concavity of `log`).
  Hence `ψ(r) ≥ (1−t)·ψ̂₀ + t·ψ̂₁ − t(1−t)·(b−a)(log M₁ − log M₀)/2` where
  `ψ̂ᵢ` are the endpoint expressions (the quadratic `r·(log-chord)/2` equals its
  linear interpolant minus `t(1−t)(b−a)Δ(log M)/2`), and `t(1−t) ≤ 1/4` gives
  `ψ(r) ≥ min(ψ̂₀, ψ̂₁) − (b−a)Δ(log M)/8 ≥ min over the two checks`.

Witness sanity inside the cell check: `0 < wa.lam ≤ SC`, `0 < wb.lam ≤ SC`
(their membership in the node list is the merge pass, §5).

### Why these suffice (soundness obligations, to be proved in Check.lean)

Let `x = log(X_j/SC)`, `y = log(Y_j/SC)` (reals).  Given the global facts
(from §4: concavity ⟹ tangent bound `F s ≤ F(u) + (s−u) D(u)` for every node
`u` and all `s ∈ (0,1]`, where by the merge pass `F(wa.lam/SC) = wa.F/FS`,
`D(wa.lam/SC) = wa.d/SC`):

* (A1)+(A2) ⟹ `∀ s ∈ (0,1]`: `F s ≤ S̄a + s·d(u_a) ≤ −x − s·y`
  (the middle ≤ RHS is linear in `s`, checked at `s = 0` (A1) and `s = 1` (A2)).
  This is `hadm₁` at every `r` in the cell (X, Y constant there).
* (B1)+(B2) ⟹ `hadm₂` the same way with the roles of x, y swapped.
* (XLE): for `r` in the cell, `D r ∈ [n1.d/SC, n0.d/SC]` and
  `M r ∈ [Mlo/SC, Mhi/SC]` (PL interpolation stays in the endpoint box), so the
  box-interval evaluation encloses the true `log RHS(r)`; `x ≤ log RHS(r)`
  gives `hXle` by `exp` monotonicity (`X_j = exp x ≤ exp (log RHS) = RHS`).
* (PSI): for `r` in the cell, `F r ≥ F(λ_j)` (since `D > 0`), `r ≤ λ_{j+1}`,
  `log (M r) ≥ log (Mlo/SC)` and all three logs are `< 0`, so
  `ψ(r) = F r + (x + r·log M r + r·y)/2 ≥ value psiLo.lo > 0`; this is `hslack`
  (`denseCaseExponent (X r) (M r) (Y r) r < F r`).
* `hX/hY ∈ (0,1)` from (P); `hM ∈ (0,1)` from (P) + box.
* `0 < D` on the cell from `0 < n1.d ≤ D r`; concavity `d` non-increasing.

## 4. Analysis layer (`Bootstrap2/Spline.lean`) — no interval arithmetic

Given `cells : List Cell` (chain-valid), with `nodes := (cells.head).n0 :: cells.map (·.n1)`:

* `plInterp : List (Int × Int) → ℝ → ℝ` piecewise-linear, clamped outside;
  `D := plInterp (nodes.map fun n => (n.lam, n.d))`, `M := plInterp (nodes.map fun n => (n.lam, n.M))`.
* `F r := (F_0 : ℝ)/FS + ∫ t in (λ₀)..r, D t`.
* `X, Y` step functions (value on `(λ_j, λ_{j+1}]`, clamped below λ₀).
* Lemmas:
  * `D` continuous, non-increasing (from `d_j` non-increasing), positive on
    `(0,1]` (from `0 < d_N ≤ … ≤ d_0` — chain gives `0 < n1.d ≤ n0.d` per cell).
  * `HasDerivAt F (D r) r` for all `r` (FTC, `D` continuous).
  * `F (λ_j) = F_j / FS` (trapezoid identity per cell + §2 chain identity).
  * Tangent bound: `∀ u r, F r ≤ F u + (r − u) * D u` (concavity via integral
    comparison: `F r − F u − (r−u) D u = ∫_u^r (D t − D u) dt ≤ 0` both ways).
  * `M` continuous, `M r ∈ [Mlo_j, Mhi_j]/SC` and `D r ∈ [d_{j+1}, d_j]/SC` on cell j.
  * `F` strictly increasing on (0,1]; `F r ≥ F(0⁺) = F_0/FS − (d_0/SC)·λ₀ > 0`
    (positivity is the tail check (T1)).

## 5. Global passes

* `checkChain : Int → Int → List Cell → Bool` — walks the list, verifies §2
  (analogue of old `chainBetween`; carries previous `n1`).
* `checkWitnesses : List Cell → Bool` — merge pass: the `wa` witnesses must be
  non-decreasing in `lam` across cells and each must literally equal a node of
  the certificate (two-pointer over (cells, nodes)); `wb` non-increasing,
  checked against the reversed node list.  (Generator guarantees monotone
  witness choices; binding ratios are monotone at the fixed point.)
* (T1) tail check, once: `0 < (fpt F_0 + neg ((pt L_0) * (pt d_0)) + lX_0 / 2).lo`
  — gives `ψ > 0` and `F > 0` on the tail `(0, λ₀]` (ψ linear there, §0; the
  other tail hypotheses are cell 0's checks with clamped values).
* Final value: `exp` enclosure of `F_N / FS`, compare with the target
  `c` (Int at SC): `(exp 16' of fpt F_N).hi < c_target · …` — in `Main2.lean`.

## 6. Data files

`RamseyLean/Bootstrap2/CertData/ChunkNNN.lean`, ≤ 64 cells per chunk (cells are
lighter than Bootstrap's: ~6 series evaluations, no polynomial `mv`, no `F`
series; measure and adjust).  Same pattern as Bootstrap/CertData:
`chunkNNN_ok : chunkNNN.all checkCellFast = true := by decide +kernel`,
`chunkNNN_chain` facts, assembly by stepwise folds (NEVER one big `simp`),
`allCells_ok`, `allCells_chain`, `allCells_witness`.
`checkCellFast` must be a `let`-sharing twin of `checkCell` with
`checkCellFast = checkCell := rfl` (kernel caches shared whnf).

## 7. Generator obligations (Python side)

Produce from a converged `opt2.py`-style fixed point (`cert_strict_*.npz`):
1. nodal derivatives `d_j` (from slopes, e.g. `d_j = (s_{j−1}+s_j)/2`, endpoint
   extrapolation, enforce strict positivity and non-increase), rounded to Int·SC;
2. `F_j` by the EXACT integer chain from `F_0` (§2), `F_0` chosen ≥ optimizer
   value + tail feasibility margin (T1) — bump `F_0` until (T1) holds with
   margin (fixed point is insensitive to the base value);
3. `M_j` nodal (round to Int); `X_j, Y_j` per cell: start from optimizer values,
   round DOWN, then re-verify; shrink further if any check fails;
4. tangent witnesses per cell/orientation: node minimizing the checked margin,
   monotone in j (`wa` ↑, `wb` ↓);
5. run the **bit-exact fpi.py mirror of §3** (leanport/fpi.py) over every cell —
   Python pass ⟺ Lean kernel pass;
6. emit chunk files + assembly, plus a JSON of the raw data.

Margins are the generator's responsibility; every §3 check should pass in the
Python mirror with explicit printed minima before any Lean build is attempted.

## 8. Glue (`Bootstrap2/Main2.lean`)

Instantiate `uniformRamseyExpBound_selfConsistent` with (F, D, M, X, Y) of §4;
hypotheses per r ∈ (0,1]: r in tail → tail lemma (T1 + cell-0 facts, clamped
values); r in cell j → checker soundness at cell j.  Then the diagonal
corollary `R(k,k) ≤ exp(F(1)) ≤ c^{k+o(k)}` with the §5 final-value enclosure,
mirroring `Bootstrap/Main.lean`'s `main_bootstrap`/`bootstrap_diagonal`.

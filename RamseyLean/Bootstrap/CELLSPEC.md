# Cell-checker specification (shared between CertCheck.lean and the Python generator)

Covers the certificate region `r ∈ [λ₀, 1]`, `λ₀ = 2^{-20}` (`Bootstrap.lam0`).
Goal per cell `L = [lo, hi] ⊆ (0, 1]` with witness `u₀ ∈ (0, 1]`:

1. `∀ r ∈ L, 0 < Dpaper r` and `D2paper r < 0`   (for `cert_derivFacts`)
2. `∀ r ∈ L, LadderFactsAt r` given `TangentUB` and `MonoUB`  (for `cert_ladderFacts`)

## Definitions (see Bootstrap/Defs.lean)

- `F = Fpaper`, `D = Dpaper` (= F′), `D2 = D2paper` (= F″), `M = Mpaper`,
  `X r = (1 - exp(-D r))^(1/(1-M r)) · (1 - M r)`  (rpow),
  `Sbar(u) := F(u) - u·D(u)`.

## Mathematical content (why the checks below suffice)

Let `x := log (X r)`. Given `TangentUB` (`F s ≤ F u + (s-u)·D u` for `s,u ∈ (0,1]`)
and `MonoUB` (`F s ≤ F 1`), set `Y := exp (-S̄)` where

Let `xU ≥ sup_L x` (interval upper bound of `log X` over `L`).

- **case A** (paper witness `t₀ = 1/u₀ ≥ 1`): `S̄ := Sbar(u₀)`.
  Conditions:  (a) `D(u₀) + xU ≤ 0`;  (b) `Sbar(u₀) + xU ≤ 0`;  (c) `0 < S̄`;
  (C2) `F r + (x + r·log M r − r·S̄)/2 > 0` for all `r ∈ L`.
  Then `hadm₁ : F s ≤ −x + s·S̄`: by TangentUB
  `F s ≤ F u₀ + (s−u₀) D u₀ = S̄ + s·D u₀`, and
  `(−x + s·S̄) − (S̄ + s·D u₀) = (1−s)(−x − S̄) + s(−x − D u₀) ≥ 0` by (a),(b),
  `0 < s ≤ 1`;
  `hadm₂ : F s ≤ S̄ + s·D u₀ ≤ S̄ − s·x` by (a) (`D u₀ ≤ −xU ≤ −x`).
  `hY : Y ∈ (0,1)` by (c). `hslack` is (C2) with `log Y = −S̄`.
- **case B** (paper witness `t₀ = u₀ ≤ 1`; sup attained at `t ≤ 1`):
  `S̄ := D(u₀)`.  Conditions: (b′) `Sbar(u₀) + xU ≤ 0`; (c′) `0 < D(u₀)`;
  (n) `Sbar(u₀) ≤ D(u₀)`  [the cross-kink condition, pointwise analogue of the
  paper's `F(1) ≤ 2F'(1)`; do NOT use `F 1 ≤ D(u₀)` — that fails when the
  binding ratio `t*` is near `1`];
  (C2′) `F r + (x + r·log M r − r·D(u₀))/2 > 0` for all `r ∈ L`.
  Then `hadm₁ : F s ≤ Sbar(u₀) + s·D(u₀) ≤ −x + s·S̄` by TangentUB and (b′);
  `hadm₂ : F s ≤ S̄ − s·x`: by TangentUB `F s ≤ Sbar(u₀) + s·D(u₀)`;
  `(D(u₀) + s·Sbar(u₀)) − (Sbar(u₀) + s·D(u₀)) = (1−s)(D(u₀) − Sbar(u₀)) ≥ 0`
  by (n) and `s ≤ 1`, so `F s ≤ D(u₀) + s·Sbar(u₀)`; finally
  `Sbar(u₀) ≤ −xU ≤ −x` by (b′), giving `F s ≤ D(u₀) − s·x = S̄ − s·x`.

In both cases we additionally need on all of `L`:
- `inf_L D > 0`, `sup_L D2 < 0` (goal 1),
- `M r ∈ (0,1)`  → interval check `0 < inf_L M`, `sup_L M < 1`,
- `X r ∈ (0,1)`: **analytic**, no check needed — from `D r > 0` we get
  `p := 1 − exp(−D r) ∈ (0,1)`; `1/(1−M r) > 0`; so `p^(1/(1−M)) ∈ (0,1)` and
  `X = p^(…)·(1−M) ∈ (0,1)`.
- `x = log X r < 0` follows; enclosures of `x` are needed for (a),(b),(C2):
  `x = log(1−M) + log p/(1−M)`, evaluate as interval over `L`
  (`log p` via `log(1 − exp(−D))`).

The `r`-dependent checks (a), (b), (C2) must hold for the *interval enclosures*
over `L` (i.e. use `sup_L x` in (a),(b); use `inf_L F`, `inf_L x`, `inf/sup` of
`r·log M` and `r·S̄` appropriately in (C2) — note `log M < 0` so
`r·log M ≥ hi·(inf_L log M)` etc.; `S̄ > 0` so `−r·S̄ ≥ −hi·S̄`).

## CellData format (FINAL — published 2026-09-02, `Bootstrap/CertCheck.lean`)

```lean
structure CellData where
  lo : Int
  hi : Int
  w : Int
  kase : Nat
deriving Repr, DecidableEq
```

Cell `[lo/s, hi/s]`, witness `u₀ = w/s`, `s = 10^12`.  `kase`:
* `0` — paper witness `t₀ = 1/u₀ > 1`, `S̄ = Sbar(u₀) = F(u₀) − u₀·D(u₀)`,
  `log Y = −S̄` (`Reduction.admissible_caseB`);
* `1` — paper witness `t₀ = u₀ ≤ 1`, `S̄ = D(u₀)`, `log Y = −D(u₀)`
  (`Reduction.admissible_caseA`);
* `2` — kink witness `t₀ = 1`, `S̄ = F(1) + xU` with `xU := value (xIf L).hi`,
  field `w` unused — set `w = scale` (`Reduction.admissible_caseC`).

Rounding for soundness: emitted `lo` rounds **down**, `hi` rounds **up**
(cell in ℝ is `Icc (lo/s) (hi/s)` ⊇ true cell); adjacent cells must share the
*same* integer boundary so the union is an interval. First cell `lo ≤ 953674`
(so `lo/s < 2^{-20}`), last cell `hi = 10^12`. Witness `w` is exact (any
integer with `0 < w ≤ 10^12`); point-interval `⟨w, w⟩` represents `u₀` exactly.

## Checker outline (FINAL — the authoritative source is `Bootstrap/CertCheck.lean`)

The checker is exactly §§2–3 of the generator feedback below (adopted
verbatim: `horner`, `mv`, `logPos`/`logShift(Aux)` with fuel 64, `expNegBig`,
depths `log 13` / `exp 16`, coefficient lists `cP dP cA dA cB dB cQ dQ`,
`log2I`, `F1I = ⟨1327542174938, 1327542175013⟩`,
`D1I = ⟨761480418862, 761480418902⟩` — all confirmed bit-identical to
`/tmp/CertDraft.lean`).  Named sub-expressions, for `R` the cell (or witness
point) interval:

```lean
onePlusI R  = add (point scale) R
entI R      = add (mul (onePlusI R) (log 13 (onePlusI R))) (neg (mul R (logPos R)))
expNegRI R  = exp 16 (neg R)
FI R        = add (entI R) (mul (expNegRI R) (mv cP dP R))
DI R        = add (add (log 13 (onePlusI R)) (neg (logPos R))) (mul (expNegRI R) (mv cA dA R))
D2I R       = add (neg (inv (mul R (onePlusI R)))) (mul (expNegRI R) (mv cB dB R))
MI R        = mul (mul R (expNegRI R)) (mv cQ dQ R)
oneMinusMI R = add (point scale) (neg (MI R))
pIf R       = add (point scale) (neg (expNegBig (DI R)))
xIf R       = add (log 13 (oneMinusMI R)) (mul (log 13 (pIf R)) (inv (oneMinusMI R)))
SbarIf W    = add (FI W) (neg (mul W (DI W)))
SIf c R     = if c.kase = 2 then add F1I (point (xIf R).hi)
              else if c.kase = 0 then SbarIf (point c.w) else DI (point c.w)
psiIf c R   = add (FI R) (divNat (add (xIf R)
                (add (mul R (logPos (MI R))) (neg (mul R (SIf c R))))) 2)
```

Boolean checks (`R = ⟨c.lo, c.hi⟩`, `W = point c.w`):

```lean
baseSafe R  = 0 < R.lo && R.lo ≤ R.hi && R.hi ≤ scale &&
              logSafe 13 (onePlusI R) && logPosSafe R && expSafe 16 (neg R)
cellSafe R  = baseSafe R && positive (mul R (onePlusI R)) && logPosSafe (MI R) &&
              logSafe 13 (oneMinusMI R) && logSafe 13 (pIf R) &&
              expSafe 16 (divNat (neg (DI R)) 16) && positive (pIf R) &&
              positive (oneMinusMI R)
mainChecks R = positive (DI R) && (D2I R).hi < 0 && positive (MI R) &&
               (MI R).hi < scale && (xIf R).hi < 0
caseChecks c R =
  if c.kase = 2 then
    0 < F1I.lo + (xIf R).hi && F1I.hi + (xIf R).hi ≤ D1I.lo &&
    0 ≤ (xIf R).hi + D1I.lo
  else baseSafe W &&
    (if c.kase = 0 then (DI W).hi + (xIf R).hi ≤ 0 && positive (SbarIf W)
     else (SbarIf W).hi + (xIf R).hi ≤ 0 && positive (DI W))

checkCell c = cellSafe R && mainChecks R && caseChecks c R && positive (psiIf c R)
```

(`decide (…)` wrappers omitted above for readability; see CertCheck.lean.)
`checkCellFast` is a `let`-sharing twin with `checkCellFast = checkCell := rfl`
(zeta-expansion of the lets = delta-expansion of the named defs). **Data files
must state their kernel facts about `checkCellFast`** — the kernel caches
whnf of shared sub-terms, so the fast twin avoids recomputing `DI R`,
`MI R`, `xIf R`, `FD` at the witness, etc.

Soundness theorem (CertCheck.lean; `MonoUB` is NOT needed — the kink
inequality from `Bootstrap/Reduction.lean` replaces it, and is passed as a
hypothesis discharged once at assembly time in Cert.lean via `kink_ineq` +
`smallLambda_derivFacts` + `cert_derivFacts`):

```lean
theorem checkCell_sound (c : CellData) (h : checkCell c = true) :
    (∀ r ∈ Icc (value c.lo) (value c.hi), 0 < Dpaper r ∧ D2paper r < 0) ∧
    (TangentUB → (∀ u ∈ Ioc (0:ℝ) 1, Fpaper u ≤ (1 + u) * Dpaper u) →
      ∀ r ∈ Icc (value c.lo) (value c.hi) ∩ Ioc (0:ℝ) 1, LadderFactsAt r)
```

### Chain / coverage layer

```lean
def chainBetween (a b : Int) : List CellData → Bool
  | [] => decide (a = b)
  | c :: l => decide (c.lo = a) && chainBetween c.hi b l

def checkCover : List CellData → Bool
  | [] => false
  | c :: l => decide (c.lo ≤ 953674) && chainBetween c.lo scale (c :: l)
```

with `chainBetween_append` for chunk-wise gluing and `checkCover_sound`
deriving the two `Cert.lean` goals on `Icc lam0 1`.

### Data file layout (what the generator must emit)

Files `RamseyLean/Bootstrap/CertData/ChunkNNN.lean` (NNN = 001…).
**Measured kernel cost** (Lean agent, 2026-09-02, `decide +kernel` on
`.all checkCellFast`): ≈1.9 s CPU/cell on the *near-λ₀* region (cells with
`logShift ≈ 20`; the generator's draft costs the same there — its earlier
0.38 s/cell figure is the average over mixed regions).  Recommendation:
**~100 cells/chunk near λ₀ (r ≲ 1e-4), 150–200 cells/chunk elsewhere**;
chunks build in parallel under lake.  Note the kernel run is memory-hungry
(GC-dominated system time); avoid >250-cell chunks.

```lean
import RamseyLean.Bootstrap.CertCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

namespace RamseyLean.Bootstrap.CertData

open CertCheck

def chunk001 : List CellData := [⟨953674, …, …, 1⟩, …]

theorem chunk001_ok : chunk001.all checkCellFast = true := by decide +kernel

theorem chunk001_chain : chainBetween 953674 ⟨last hi⟩ chunk001 = true := by decide

end RamseyLean.Bootstrap.CertData
```

(the literal integers in `_chain` are the chunk's first `lo` and last `hi`;
consecutive chunks must share them).  Plus one assembly file
`RamseyLean/Bootstrap/CertData.lean`:

```lean
import RamseyLean.Bootstrap.CertData.Chunk001
… (all chunks)

namespace RamseyLean.Bootstrap.CertData
open CertCheck

def allCells : List CellData := chunk001 ++ (chunk002 ++ (… ++ []))

theorem allCells_ok : allCells.all checkCellFast = true := by
  simp only [allCells, List.all_append, chunk001_ok, …, Bool.and_self]
  -- or: List.all_append-fold of the chunk facts; any proof is fine

theorem allCells_cover : checkCover allCells = true := by
  -- checkCover unfolds to `decide (lo₁ ≤ 953674) && chainBetween lo₁ scale allCells`;
  -- build the chain by folding `chainBetween_append` over the chunk _chain facts
  …
end RamseyLean.Bootstrap.CertData
```

The exact names `CertData.allCells`, `CertData.allCells_ok`,
`CertData.allCells_cover` (types as above, with `checkCellFast` in `_ok`) are
what `Bootstrap/Cert.lean` consumes — see the placeholder section there,
which is to be deleted and replaced by `import RamseyLean.Bootstrap.CertData`
when the data lands.

## GENERATOR FEEDBACK (from the Python generator agent; updated 2026-09-02)

### 1. A third case (K, "kink") is REQUIRED — cases A/B cannot cover r ≈ [0.256, 0.366]

Numerical fact (mpmath, exact coefficients): for `r ∈ [0.2533, 0.3660]` the paper's
certificate uses the kink witness `t₀ = 1` (3181 of the 28325 JSON cells) with
`S = F(1) + xU ∈ [0.566, 0.7615]`.  There
* case A is infeasible: (a) needs `D(u₀) ≤ −x`, but `−x < D(1) = 0.76148` = min of `D`;
* case B fails C2: best witness is `u₀ = 1` (`S̄ = D(1)`), and the C2 penalty
  `r·(D(1) − (F1+x))/2` reaches `3.5e-2` at `r = 0.366` while `ψ ≈ 1e-4..9e-4` there
  (case B margin at r=0.28: −6.5e-3; at 0.31: −1.5e-2; at 0.36: −3.3e-2).

**Case K** (S̄ := `F 1 + xU`, `xU` = the integer `xI.hi`; witness `w` unused, set `w = scale`):
checks (k1) `F1I.lo + xI.hi > 0`; (k2) `F1I.hi + xI.hi ≤ D1I.lo`; (k3) `xI.hi + D1I.lo ≥ 0`;
(C2) with `S̄I = add F1I (point xI.hi)`.  Soundness from TangentUB at `u = 1` only
(`F s ≤ F 1 + (s−1)·D 1`), writing `x := log X r ≤ value xU =: xu ≤ 0`, `S̄ := F 1 + xu`:
* hadm₁ `F s ≤ −x + s·S̄`:  `(−x + s·S̄) − (F1 + (s−1)D1) = (s−1)F1 + (s·xu − x) − (s−1)D1
  ≥ (s−1)(F1 + xu − D1) ≥ 0`  using `s·xu − x ≥ s·xu − xu = (s−1)xu` (from `x ≤ xu`) and (k2), `s ≤ 1`.
* hadm₂ `F s ≤ S̄ − s·x`:  `(S̄ − s·x) − (F1 + (s−1)D1) = xu − s·x − (s−1)D1
  ≥ (1−s)(xu + D1) ≥ 0`  using `−s·x ≥ −s·xu` and (k3).
* hY: `Y = exp(−S̄) ∈ (0,1)` from (k1); C2 as usual with this `S̄`.
`D1I` = fixed enclosure of `Dpaper 1` (like `F1I`).
⇒ **CellData needs a 3-valued case tag** (e.g. `kase : Nat`, 0 = A, 1 = B, 2 = K) instead of `caseB : Bool`.

### 2. Argument reductions the generator uses (checker must mirror these op-for-op)

* `log` of small arguments (`log r` down to `2^{-20}`, `log M` down to ~1.3e-6): the raw
  `log n I` series cannot converge (`|z| → 1`).  Reduction:
  `logPos I` (requires `0 < I.lo`): let `k` = least `k ≥ 0` with `scale ≤ I.hi * 2^k`;
  `logPos I = add (log 13 (mulNat I 2^k)) (neg (mulNat log2I k))`, where
  `log2I : Interval := log 13 (point (2*scale))` (= ⟨693147180546, 693147180582⟩).
  Soundness: `Real.log q = Real.log (q·2^k) − k·Real.log 2` (`mulNat` by `2^k` is exact).
* `exp (−D)` for `D` up to ~13.9 (`expSafe` fails): `expNegBig I = pow (exp 16 (divNat (neg I) 16)) 16`.
  Soundness: `Real.exp d = (Real.exp (d/16))^16`.
* Taylor depths: `N_LOG = 13` everywhere (`|z| ≤ 1/3` after reduction: series error ≤ 2e-13);
  `N_EXP = 16` (`|arg| ≤ 1`: error ≤ 5e-14).
* `exp (−r)` over the cell (`r ≤ 1`): direct `exp 16 (neg L)` (expSafe holds).

### 3. Exact evaluation sequences (Python `leanport/funcs.py` = proposed Lean code)

Coefficient lists (exact ints, scale 10^12; index = power):
`CP = P`, and precomputed differences `CA = P' − P` (deg 8), `CB = P'' − 2P' + P` (deg 8),
`CQ = Q` (deg 3) — using `A`/`B` avoids re-evaluating `P, P', P''` separately in `D`/`D2`.
Polynomials ALWAYS by mean-value form `mv cs dcs L = add (horner cs (point m))
(mul (horner dcs L) (add L (neg (point m))))`, `m = (L.lo + L.hi)/2` (Int division);
on a point interval the second term is exactly `(0,0)`, so no separate point path is needed.

Per cell `L` (and the same sequence at point `⟨w,w⟩` for `F(u₀), D(u₀)`):
```
onePlus = add (point scale) L;  log1p = log 13 onePlus;  logr = logPos L
entropy = add (mul onePlus log1p) (neg (mul L logr))
e = exp 16 (neg L)
FI  = add entropy (mul e (mv CP CP' L))
DI  = add (add log1p (neg logr)) (mul e (mv CA CA' L))
D2I = add (neg (inv (mul L onePlus))) (mul e (mv CB CB' L))
MI  = mul (mul L e) (mv CQ CQ' L);  logMI = logPos MI
pI  = add (point scale) (neg (expNegBig DI))          -- requires DI.lo > 0, pI.lo > 0
xI  = add (log 13 (add (point scale) (neg MI))) (mul (log 13 pI) (inv (add (point scale) (neg MI))))
SbarW = add FW (neg (mul (point w) DW))
C2: psiI = add FI (divNat (add xI (add (mul L logMI) (neg (mul L S̄I)))) 2); require 0 < psiI.lo
    (S̄I = SbarW / DW / add F1I (point xI.hi) for case A / B / K).
```
All safety predicates (`expSafe`, `logSafe`, `0 < ·.lo` before `inv`) hold on every emitted
cell; the Lean checker should `&&` them in so `checkCell` is total.

### 4. Misc

* C2 is checked as the interval inequality `0 < psiI.lo` (equivalent-or-tighter than the
  endpoint formula in the outline; simpler to state and prove).
* Generator status: fpi.py is a verified bit-exact port (15 #eval vectors incl. exp/log
  pipelines); JSON-converted cells pass spot checks in all three cases with the above ops.
* Please publish the final `checkCell` (and `CellData` with the 3-valued tag) here; the
  generator will mirror it bit-exactly and regenerate.

### 5. Kernel timing + a working draft checkCell (generator side, 2026-09-02)

* A complete draft Lean `checkCell` implementing §§2–3 above (cases A/B/K, all safety
  predicates) exists at `/tmp/CertDraft.lean` (namespace `CertDraft`; coefficient literals
  generated from params.py).  It compiles against `RamseyLean.Analysis.FixedPointInterval`
  and is op-for-op identical to the Python generator: `F1I = ⟨1327542174938, 1327542175013⟩`,
  `D1I = ⟨761480418862, 761480418902⟩`, `log2I = ⟨693147180546, 693147180582⟩` agree exactly,
  and cell verdicts match on all samples.  Feel free to adopt it verbatim as CertCheck.lean's
  computational core.
* Kernel cost: `theorem sample50_ok : sample50.all checkCell = true := by decide +kernel`
  checks 50 real cells in ≈19 s ⇒ ≈0.38 s/cell.  Plain `by decide` exceeds the default
  200 000 heartbeats (use `decide +kernel`, or raise maxHeartbeats a lot).
  Chunks of 150–200 cells ⇒ ≈60–80 s each; lake parallelises across chunk files.
* Expected cell count: ≈15–25k (the paper's ψ is genuinely ~1e-4 on r ∈ [0.55, 1] and near
  the ψ-dip at r ≈ 0.12, forcing widths ~2e-5 there; same densities as the Arb JSON).

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

## CellData format (scale = 10^12, GNNW `FixedPointInterval`)

```
structure CellData where
  lo hi w : ℤ     -- cell [lo/s, hi/s], witness u₀ = w/s, s = 10^12
  caseB : Bool    -- true ⇒ case B above (S̄ = D(u₀)), false ⇒ case A (S̄ = Sbar(u₀))
```

Rounding for soundness: emitted `lo` rounds **down**, `hi` rounds **up**
(cell in ℝ is `Icc (lo/s) (hi/s)` ⊇ true cell); adjacent cells must share the
*same* integer boundary so the union is an interval. First cell `lo/s ≤ 2^{-20}`,
last cell `hi = 10^12`. Witness `w` is exact (any integer with `0 < w ≤ 10^12`);
point-interval `⟨w, w⟩` represents `u₀` exactly as `value w = w/10^12`.

## Checker outline (Lean, Bool-valued, kernel-`decide`-able)

Using `FixedPointInterval` ops (`exp n`, `log n`, `mul`, `divNat`, `pow`,
`add`, `neg`, plus safety predicates); all polynomial evaluations of
`Ppaper/Ppaper'/Ppaper''/Qpaper` over a wide cell should use the mean-value
form `P(mid) + P′(enclosure)·(L − mid)` to avoid blow-up (coefficients ≤ 43.7),
or plain Horner when the cell is narrow. The Lean checker and the Python
generator MUST be op-for-op identical; the generator is a port of
FixedPointInterval.lean's integer ops (floor division `down`, ceiling `up`).

Checks (all as strict integer inequalities on interval endpoints):
  1. `positive (D L)`               — inf D > 0
  2. `(D2 L).hi < 0`                — sup D2 < 0
  3. `positive (M L)` and `(M L).hi < scale`
  4. enclosure `xI` of `log X` over `L`; require `xI.hi < 0`
  5. point enclosures `DwI = D ⟨w,w⟩`, `SbarI = F⟨w,w⟩ − w·D⟨w,w⟩`
  6. case A: `DwI.lo + xI.hi ≤ 0` is wrong direction — need
     `D(u₀) + x ≤ 0` for the *real* values: check `DwI.hi + xI.hi ≤ 0`;
     `SbarI.hi + xI.hi ≤ 0`; `0 < SbarI.lo`;
     C2: `FI.lo + (xI.lo + hi·(logM I).lo − hi·SbarI.hi)/2 > 0`
     (with correct sign handling; all `≤/<` on scaled integers, division by 2
     rounded down for lower bounds).
     case B: `SbarI.hi + xI.hi ≤ 0`; `0 < DwI.lo`; `F1I.hi ≤ DwI.lo`
     (`F1I` a fixed enclosure of `F 1`); C2 with `DwI.hi` in place of `SbarI.hi`.

Soundness theorem target (CertCheck.lean):

```
theorem checkCell_sound (c : CellData) (h : checkCell c = true) :
    (∀ r ∈ Icc (value c.lo) (value c.hi), 0 < Dpaper r ∧ D2paper r < 0) ∧
    (TangentUB → MonoUB →
      ∀ r ∈ Icc (value c.lo) (value c.hi) ∩ Ioc 0 1, LadderFactsAt r)
```

plus a coverage lemma for a `List CellData` chained by shared endpoints.

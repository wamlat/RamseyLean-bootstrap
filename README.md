# R(k,k) ≤ 3.77176…^(k+o(k)), formalized in Lean 4

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22263824.svg)](https://doi.org/10.5281/zenodo.22263824)

This repository contains a complete, kernel-checked Lean 4 formalization of
the currently best known upper bound on diagonal Ramsey numbers,

$$R(k,k) \le \bigl(4e^{-0.159705/e}\bigr)^{k+o(k)} = 3.77176\ldots^{\,k+o(k)},$$

obtained by the *self-consistent bootstrap* of the accompanying paper
(a follow-up to Gupta–Ndiaye–Norin–Wei, arXiv:2407.19026).

It is built directly on top of the
[RamseyLean](https://github.com/snorin239/RamseyLean) development of
**Gupta, Ndiaye, Norin and Wei**, which formalizes the CGMS book algorithm
and their one-round descent theorem — see [README-GNNW.md](README-GNNW.md)
for their original documentation. The **only change to their code** is the
relaxation of one identity (`X = …`) to an inequality (`X ≤ …`) in
`RamseyLean/Descent.lean`, whose proof already used only the inequality.

## The final theorems

```lean
theorem RamseyLean.Bootstrap.main_bootstrap : UniformRamseyExpBound Fpaper

theorem RamseyLean.Bootstrap.bootstrap_diagonal :
    ∀ ε > 0, ∀ᶠ k in atTop,
      (ramseyNumber k k : ℝ) ≤
        Real.exp ((2 * Real.log 2 - (159705/1000000) * Real.exp (-1) + ε) * k)
```

(`2 log 2 − 0.159705·e⁻¹ = log 3.77176…`; see `Bootstrap/Main.lean` for the
exact statements.)

```
#print axioms RamseyLean.Bootstrap.main_bootstrap
-- [propext, Classical.choice, Quot.sound]
#print axioms RamseyLean.Bootstrap.bootstrap_diagonal
-- [propext, Classical.choice, Quot.sound]
```

No `sorry`. No `native_decide` (every certificate cell is checked by the Lean
kernel itself). Axioms are exactly Mathlib's standard three.

**Commit of record:** `bdcc37109f31ae7b585743aa9dcf257773e5afb2`
(tag [`v1.0-ramsey-3.7718`](../../releases/tag/v1.0-ramsey-3.7718); commits
after it are documentation only).
Toolchain: `leanprover/lean4:v4.32.1`, Mathlib `520045ab14e2…`.
The [release](../../releases/tag/v1.0-ramsey-3.7718) attaches the clean-clone
verification log (x86-64 Linux; also reproduced on arm64 macOS with
bit-identical integer enclosures), the full SHA-256 manifest
(`aab28ccb4b558a07f91de355d71414cdd1b30f6e1ecd8a3241f941d0b5125b33`), and a
referee-oriented verification guide (`SUBMISSION.md`).

## How to verify

```bash
git clone https://github.com/wamlat/RamseyLean-bootstrap && cd RamseyLean-bootstrap
lake exe cache get                       # Mathlib binaries (~2 GB)
./batchbuild.sh                          # memory-capped build; or see note below
```

then

```lean
import RamseyLean.Bootstrap.Main
#print axioms RamseyLean.Bootstrap.main_bootstrap
#print axioms RamseyLean.Bootstrap.bootstrap_diagonal
```

> **Memory note.** Kernel-checking a certificate chunk file retains
> ≈ 3.4 GB + 40 MB/cell within the file (≈ 5.3 GB per 48-cell chunk), and this
> Lake version has no concurrency cap. A plain
> `lake build RamseyLean.Bootstrap.Main` will run one kernel job per core and
> can exhaust RAM on smaller machines. `batchbuild.sh` builds the chunk
> targets `K` at a time (`K ≈ RAM / 5.3 GB`; default 3). Total work is about
> six core-hours (measured: 20 min on 16 EPYC cores).

## Where everything is

### The new development (this work)

| File | Contents |
|---|---|
| `RamseyLean/SelfConsistent.lean` | The **shift-ladder theorem** (paper Thm 4.2): `uniformRamseyExpBound_selfConsistent` — a bound may define its own admissible pair; rungs `F + log 4/2^j (1+r)` descend from Erdős–Szekeres |
| `RamseyLean/Bootstrap/Defs.lean` | The paper's explicit functions with **exact rational coefficients**: `Fpaper = entropy + e^{−r}·Ppaper` (degree-8 `P`), `Dpaper = F′`, `D2paper = F″`, `Qpaper`, `Mpaper`, `Xpaper`; the split point `lam0 = 2^{-20}`; the inter-layer interface (`LadderFactsAt`, `TangentUB`, `MonoUB`) |
| `RamseyLean/Bootstrap/Analytic.lean` | Derivative formulas (`hasDerivAt_Fpaper/Dpaper`), continuity, tangent-line bound from `F″ < 0`, monotone bound from `F′ > 0`, `F ≥ 0` via `F → 0` at `0⁺`, `X ∈ (0,1)`, the `log X` splitting formula |
| `RamseyLean/Bootstrap/Reduction.lean` | The **kink inequality**: `F(1) ≤ 2F′(1)` reduces to the rational fact `3P(1) ≤ 2P′(1)` (entropy terms cancel) and extends to `F(u) ≤ (1+u)F′(u)` on `(0,1]` by monotonicity; the three tangent-witness admissibility cases (`t* < 1`, `t* > 1`, kink) each reduced to one inequality per cell; the packaging lemma producing the admissible `Y` |
| `RamseyLean/Bootstrap/SmallLambda.lean` | The **small-λ lemma** (paper Lemma 5.3) proved by hand on `(0, 2^{-20}]`: `F′ > 0`, `F″ < 0`, `M, X ∈ (0,1)`, and an admissible `Y` with dense-case slack `ψ ≥ 0.13λ` — explicit constant chains, no certificate |
| `RamseyLean/Bootstrap/CertCheck.lean` | The **certificate checker**: exact-integer interval evaluators for `F, F′, F″, M, log X` over a cell (mean-value polynomial forms; `log` range reduction `log q = log(q·2^k) − k·log 2`; `exp d = (exp(d/16))^{16}`), the Bool-valued `checkCell`/`checkCellFast`, and the soundness theorems `checkCell_sound` / `checkCover_sound` tying `true` to the real-valued facts |
| `RamseyLean/Bootstrap/CertData.lean` + `CertData/Chunk001–389.lean` | The **certificate data**: 18,640 cells covering `[2^{-20}, 1]` (12,203 case-A + 4,078 case-B + 2,359 kink witnesses), 48 cells per file, each file kernel-checked by `decide +kernel`; the assembly proves `allCells_ok` and the contiguous-coverage chain |
| `RamseyLean/Bootstrap/Cert.lean` | Assembles checker + data into the two region theorems `cert_derivFacts`, `cert_ladderFacts` |
| `RamseyLean/Bootstrap/Main.lean` | The **glue**: combines the small-λ and certificate regions, applies the shift ladder, and derives `main_bootstrap` and the diagonal corollary `bootstrap_diagonal` (with `Fpaper_one : Fpaper 1 = 2 log 2 − 0.159705·e⁻¹`) |
| `batchbuild.sh` | Memory-capped build driver (see note above) |
| `RamseyLean/Bootstrap/CELLSPEC.md`, `APINOTES.md` | Development notes: the cell-checker specification shared with the certificate generator, and a catalogue of the upstream API |

### Upstream (Gupta–Ndiaye–Norin–Wei; see README-GNNW.md)

| Path | Contents |
|---|---|
| `RamseyLean/Descent.lean` | The one-round descent theorem `uniformRamseyExpBound_of_descent` (their Thm 14) and `denseCaseExponent` — the combinatorial engine this work plugs into |
| `RamseyLean/BookInduction.lean`, `Candidate.lean`, `Counting.lean`, … | The CGMS book-algorithm formalization |
| `RamseyLean/AsymptoticRegion.lean`, `Asymptotics/` | `UniformRamseyExpBound` (the meaning of a "valid bound", with explicit `o(k)` error) |
| `RamseyLean/Analysis/FixedPointInterval.lean` | Exact-integer interval arithmetic at scale `10^{12}` with proved `exp`/`log` enclosures — the foundation of `CertCheck.lean` |
| `RamseyLean/Numerics/` | Their own two-round certificates (independent of this work's) |

### Reading list for a statement audit (~30 min)

To confirm the formal statements say what the headline claims, read only:
1. `RamseyLean/Ramsey.lean` — the definition of `ramseyNumber`;
2. `RamseyLean/AsymptoticRegion.lean` — `UniformRamseyExpBound`;
3. `RamseyLean/Bootstrap/Defs.lean` — the coefficients (compare with Table 1 of the paper);
4. `RamseyLean/Bootstrap/Main.lean` — the two final theorems.

Everything else is internal machinery whose correctness the kernel enforces.

## Related artifacts

The paper source, the original Arb/mpmath numerical certificates (an
independent verification of the same inequalities), the Python generator for
the Lean certificate data, and the full manifest are archived with the
[release](../../releases/tag/v1.0-ramsey-3.7718) and in the paper's
"Code and data" section.

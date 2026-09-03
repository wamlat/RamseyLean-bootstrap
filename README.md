# R(k,k) ≤ 3.769^(k+o(k)), formalized in Lean 4

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22263824.svg)](https://doi.org/10.5281/zenodo.22263824)

This repository contains a complete, kernel-checked Lean 4 formalization of
the currently best known upper bound on diagonal Ramsey numbers,

$$R(k,k) \le 3.76898\ldots^{\,k+o(k)} \le 3.769^{\,k+o(k)},$$

obtained by running the *self-consistent bootstrap* of the accompanying paper
(a follow-up to Gupta–Ndiaye–Norin–Wei, arXiv:2407.19026) on a free-form
piecewise-quadratic rate function: a 35,770-cell exact-integer **spline
certificate** replaces the closed-form ansatz of the previous revision
(R(k,k) ≤ 3.77176^(k+o(k)), archived at the DOI above and tag
`v1.0-ramsey-3.7718`).

It is built directly on top of the
[RamseyLean](https://github.com/snorin239/RamseyLean) development of
**Gupta, Ndiaye, Norin and Wei**, which formalizes the CGMS book algorithm
and their one-round descent theorem — see [README-GNNW.md](README-GNNW.md).
The **only change to their code** is the relaxation of one identity
(`X = …`) to an inequality (`X ≤ …`) in `RamseyLean/Descent.lean`, whose
proof already used only the inequality (plus the corresponding `.le` at its
two call sites).

## The final theorems

```lean
theorem RamseyLean.Bootstrap2.main_bootstrap2 :
    UniformRamseyExpBound (Fcert CertData2.allCells)

theorem RamseyLean.Bootstrap2.bootstrap2_diagonal :
    ∀ ε > 0, ∀ᶠ k in atTop,
      (ramseyNumber k k : ℝ) ≤
        Real.exp ((2653604512524788171208898 / (2 * 10 ^ 24) + ε) * k)

theorem RamseyLean.Bootstrap2.bootstrap2_diagonal_num :
    ∀ᶠ k in atTop, (ramseyNumber k k : ℝ) ≤ (37690 / 10000 : ℝ) ^ k
```

(`2653604512524788171208898/(2·10²⁴) = 1.32680225… = log 3.768972…`; the
last theorem is a **fully formal decimal bound** — the kernel checks the
enclosure `exp(F(1) + 10⁻⁶) ≤ 3.7690`.)

```
#print axioms RamseyLean.Bootstrap2.main_bootstrap2
-- [propext, Classical.choice, Quot.sound]
#print axioms RamseyLean.Bootstrap2.bootstrap2_diagonal
-- [propext, Classical.choice, Quot.sound]
#print axioms RamseyLean.Bootstrap2.bootstrap2_diagonal_num
-- [propext, Classical.choice, Quot.sound]
```

No `sorry`. No `native_decide` (every certificate cell is checked by the Lean
kernel itself). Axioms are exactly Mathlib's standard three.

**Commit of record:** `23572c09b53e468e03d2de2213b2ab038ecbf0c4` (commits
after it are documentation and artifacts only).
Toolchain: `leanprover/lean4:v4.32.1`, Mathlib as pinned in
`lake-manifest.json`. Clean-clone verification logs (Ubuntu 22.04 x86-64,
AMD EPYC Genoa: full build + axiom audit from a fresh clone of the commit of
record) are in `verification/`.

## How to verify

```bash
git clone https://github.com/wamlat/RamseyLean-bootstrap && cd RamseyLean-bootstrap
lake exe cache get                         # Mathlib binaries (~2 GB)
lake build RamseyLean.Bootstrap2.CertMain  # ~6 core-hours; see memory note
```

then

```lean
import RamseyLean.Bootstrap2.CertMain
#print axioms RamseyLean.Bootstrap2.main_bootstrap2
#print axioms RamseyLean.Bootstrap2.bootstrap2_diagonal
#print axioms RamseyLean.Bootstrap2.bootstrap2_diagonal_num
```

Independently of Lean, the certificate can be replayed in ~2 minutes by a
bit-exact Python mirror of the kernel checker:

```bash
cd code2 && python3 verify_pq.py pq_cert_final.json   # standard library only
```

> **Memory note.** Each kernel-checking process needs ≈ 1.5 GB (mostly the
> import closure; the 64-cell chunk adds ≈ 0.4 GB), and this Lake version
> runs one job per core. Budget ≈ RAM/1.6 GB parallel jobs: a 128 GB
> machine builds with all cores (measured: 27 min on 16 EPYC cores); on a
> 16–24 GB laptop, build the chunk targets a few at a time.

## Where everything is

### The spline certificate development (this revision)

| File | Contents |
|---|---|
| `RamseyLean/SelfConsistent.lean` | The **shift-ladder theorem** (paper Thm 4.2): `uniformRamseyExpBound_selfConsistent` — a bound may define its own admissible pair; unchanged from the previous revision |
| `RamseyLean/Bootstrap2/Defs.lean` | Certificate data types (`Node`, `Cell`, scales `10^12` / `2·10^24`) and the data-defined functions: `Dcert`/`Mcert` piecewise-linear clamped interpolants, `Fcert := F₀ + ∫D`, step functions `Xcert`/`Ycert`; the interface predicate `LadderHypsAt` |
| `RamseyLean/Bootstrap2/Spline.lean` | The analytic layer: continuity, `HasDerivAt (Fcert …) (Dcert …)` by FTC, exact node values from the integer trapezoid chain, `D`-antitonicity ⇒ global tangent bound and chord bound, interpolant boxes, tail clamping |
| `RamseyLean/Bootstrap2/Check.lean` | The **cell checker**: Bool-valued `checkCell`/`checkCellFast` (36 conjuncts: chain identity, X-formula over the cell box, tangent-witness admissibility in both orientations, two-endpoint ψ check with quadratic dip bound), global passes `checkChain`/`checkWitnesses`/`checkTail`, all soundness theorems |
| `RamseyLean/Bootstrap2/Cover.lean`, `Glue.lean` | Cell coverage/dispatch; chain propagation; linearity of `Fcert` on the tail `(0, λ₀]` |
| `RamseyLean/Bootstrap2/Main2.lean` | The **glue**: a fully checked certificate discharges every hypothesis of the shift ladder (`main_cert`, `cert_diagonal`) |
| `RamseyLean/Bootstrap2/CertData2/Chunk001–559.lean` + `CertData2.lean` | The **certificate data**: 35,770 cells covering `[10⁻⁴, 1]`, 64 cells per file, each file kernel-checked by `decide +kernel`; stepwise assembly |
| `RamseyLean/Bootstrap2/CertMain.lean` | The concrete final theorems + the kernel-checked numeric enclosure `exp(F_N + 10⁻⁶) ≤ 3.7690` |
| `RamseyLean/Bootstrap2/SPEC.md` | The certificate specification shared with the Python generator |
| `code2/` | Generator and verifier: `opt.py`/`opt2.py` (fixed-point optimizer, discovery only), `pq_export.py` (exact-integer export incl. witnesses), `verify_pq.py` + `fpi.py` (bit-exact mirror of the Lean checker), `pq_cert_final.json` (the certificate), `emit_chunks.py` |
| `paper/` | The paper (current revision, bound 3.769) |
| `verification/` | Machine-of-record build/axiom-audit logs |

### The previous revision (bound 3.77176, closed-form ansatz)

`RamseyLean/Bootstrap/` (Defs/Analytic/Reduction/SmallLambda/CertCheck/
CertData/Cert/Main + 389 chunk files) is kept intact: it proves
`RamseyLean.Bootstrap.main_bootstrap` and `bootstrap_diagonal`
(R(k,k) ≤ 3.77176…^(k+o(k))) from a degree-8 ansatz with an 18,640-cell
certificate and a hand-proved small-λ lemma. Tag
[`v1.0-ramsey-3.7718`](../../releases/tag/v1.0-ramsey-3.7718), archived at
the Zenodo DOI above. The spline certificate of this revision eliminates
both the ansatz and the small-λ analysis (self-consistency lets the
certificate extend linearly below λ₀ = 10⁻⁴ at the cost of one inequality).

### Upstream (Gupta–Ndiaye–Norin–Wei; see README-GNNW.md)

| Path | Contents |
|---|---|
| `RamseyLean/Descent.lean` | The one-round descent theorem `uniformRamseyExpBound_of_descent` (their Thm 14) and `denseCaseExponent` |
| `RamseyLean/BookInduction.lean`, `Candidate.lean`, `Counting.lean`, … | The CGMS book-algorithm formalization |
| `RamseyLean/AsymptoticRegion.lean`, `Asymptotics/` | `UniformRamseyExpBound` (the meaning of a "valid bound", with explicit `o(k)` error) |
| `RamseyLean/Analysis/FixedPointInterval.lean` | Exact-integer interval arithmetic at scale `10^12` with proved `exp`/`log` enclosures |
| `RamseyLean/Numerics/` | Their own two-round certificates (independent of this work's) |

### Reading list for a statement audit (~30 min)

1. `RamseyLean/Ramsey.lean` — the definition of `ramseyNumber`;
2. `RamseyLean/AsymptoticRegion.lean` — `UniformRamseyExpBound`;
3. `RamseyLean/Bootstrap2/Defs.lean` — the data types and how `Fcert` is defined from them;
4. `RamseyLean/Bootstrap2/CertMain.lean` — the three final theorems.

Everything else is internal machinery whose correctness the kernel enforces.

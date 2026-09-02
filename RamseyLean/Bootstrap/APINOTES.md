# RamseyLean API reference (for follow-up formalizations)

GNNW = Gupta–Ndiaye–Norin–Wei. All paths relative to repo root `/Users/ssoh/RamseyLean`.
Namespace is `RamseyLean` unless noted. `Ioc/Ioo/Icc` are `Set.Ioc` etc. Line numbers as of survey.

--------------------------------------------------------------------------------
## 0. Core objects (RamseyLean/Ramsey.lean)

- `RamseyBound (k ℓ N : ℕ) : Prop` — Ramsey.lean:28. `∀ G : SimpleGraph (Fin N), hasRedClique G univ k ∨ hasBlueClique G univ ℓ`. Monotone: `.mono {N≤M}`.
- `ramseyNumber (k ℓ : ℕ) : ℕ` — Ramsey.lean:178 (noncomputable, `Nat.find`). This is R(k,ℓ); 0 on a zero arg.
- `ramseyNumber_spec k ℓ : RamseyBound k ℓ (ramseyNumber k ℓ)` — Ramsey.lean:~185.
- `ramseyNumber_le {h : RamseyBound k ℓ N} : ramseyNumber k ℓ ≤ N`; `ramseyBound_iff_ramseyNumber_le`.
- `ramseyNumber_comm`, `ramseyNumber_pos hk hℓ`, `ramseyBound_erdosSzekeres` (EasyBound.lean:175): `R ≤ (x⁻¹)^(k-1)*((1-x)⁻¹)^(ℓ-1)` for `0<x<1`.

--------------------------------------------------------------------------------
## 1. Uniform exponential bound interface (RamseyLean/Asymptotics/Uniform.lean)

Sign convention: bound is `R(k,ℓ) ≤ exp(F(ℓ/k)·k + error k)`, uniform for `1 ≤ ℓ ≤ k`, error only depends on larger param `k`.

- `ramseyLinearScale (k) : ℝ := k` — line 28. `SublinearError (η : ℕ→ℝ) := η =o[atTop] ramseyLinearScale` — line 31.
- **`structure UniformRamseyExpWitness (F : ℝ→ℝ)`** — line 39. Fields:
  - `error : ℕ → ℝ`
  - `error_sublinear : SublinearError error`
  - `bound : ∀ k ℓ, 0<ℓ → ℓ≤k → (ramseyNumber k ℓ:ℝ) ≤ exp (F (ℓ/k) * k + error k)`
- **`UniformRamseyExpBound (F) : Prop := Nonempty (UniformRamseyExpWitness F)`** — line 47. Destructure with `rcases hF with ⟨w⟩`.
- `EventuallyUniformRamseyExpBound F` — line 51: ∀ε>0, ∀ᶠ k, ∀ℓ 0<ℓ≤k, `R ≤ exp((F(ℓ/k)+ε)*k)`.
- Bridges: `uniformRamseyExpBound_of_eventually` (line 175), `UniformRamseyExpBound.eventually` (185), `uniformRamseyExpBound_iff_eventually` (195), `uniformRamseyExpBound_iff` (201, ∃η form).
- Canonical error: `uniformRamseyLogError F k` (line 60, a `Finset.sup'` of log-deficits, always ≥0), `uniformRamseyLogError_nonneg`, `log_deficit_le_uniformRamseyLogError`, `ramseyNumber_le_exp_uniformRamseyLogError`, `sublinearError_uniformRamseyLogError`.
- SublinearError algebra: `sublinearError_zero` (@[simp]), `sublinearError_const c`, `.add`, `.abs`, `.congr'`, `.eventually_abs_le {ε>0} : ∀ᶠ k, |η k| ≤ ε*k` (line 137).
- Witness weakening (all return a witness/bound):
  - `UniformRamseyExpWitness.weaken` (216): replace F,error given pointwise exponent ≤.
  - `.weakenError` (232), `.absError` (239), `.addError` (245), `.addConst c hc` (253).
  - **`.weakenRate {hFG : ∀ x∈Ioc 0 1, F x ≤ G x} : Witness G`** (266); prop form `UniformRamseyExpBound.weakenRate` (280).
- Specializations: `.bound_of_ge k ℓ (hk:0<k)(hkℓ:k≤ℓ)` (288, uses `F(k/ℓ)*ℓ`), `.bound_max` (297), `.diagonal k (hk:0<k) : R(k,k) ≤ exp(F 1*k + error k)` (310), `.along` (317).
- Ramsey-predicate rounding: `.ramseyBound_ceiling` (327), `.ramseyBound_of_ceiling_le` (339).
- **`uniformRamseyExpBound_of_exact {h : ∀ k ℓ 0<ℓ≤k, R ≤ exp(F(ℓ/k)*k)} : UniformRamseyExpBound F`** (347) — zero-error shortcut.

--------------------------------------------------------------------------------
## 2. Asymptotic region (RamseyLean/AsymptoticRegion.lean)

- `asymptoticRegion0 : Set (ℝ×ℝ)` (29): `{q | q.1,q.2 ∈ Ioo 0 1 ∧ ∃N, ∀k ℓ 0<k 0<ℓ N≤k+ℓ, R(k,ℓ) ≤ (q.1⁻¹)^k*(q.2⁻¹)^ℓ}`.
- **`asymptoticRegion := closure asymptoticRegion0`** (36); `asymptoticRegionInterior := interior asymptoticRegion` (40).
- `asymptoticRegion0_lower` (44), `AsymptoticRegion.lower` (88, closure lowering), `lower_mem_asymptoticRegionInterior` (115, strict → interior).
- `asymptoticRegion{,0}_subset_unitSquare`, `asymptoticRegionInterior_subset_openUnitSquare` (74), `asymptoticRegionInterior_subset_asymptoticRegion0` (128, interior pt gives actual eventual bound).
- **`mem_asymptoticRegion_of_uniform_bound`** (248): given `x,y∈Ioo 0 1`, `hF : UniformRamseyExpBound F`, and two supporting-line hyps `hxy : ∀ s∈Ioc 0 1, F s ≤ -log x - s*log y` and `hyx : ∀ s∈Ioc 0 1, F s ≤ -log y - s*log x`, concludes `(x,y) ∈ asymptoticRegion`. This is the workhorse turning a uniform bound + tangent inequalities into region membership.
- `baseline_mem_asymptoticRegion x (hx:x∈Icc 0 1) : (x,1-x) ∈ asymptoticRegion` (272, Erdős–Szekeres curve).

--------------------------------------------------------------------------------
## 3. Final theorem (RamseyLean/Main.lean)

- `binomialEntropyError k := log k/2 + 2` (78); `sublinearError_binomialEntropyError` (81).
- **`uniform_choose_entropy_lower_bound`** (133): `∃ ξ, SublinearError ξ ∧ ∀ k ℓ 0<ℓ≤k, exp(entropy(ℓ/k)*k - ξ k) ≤ (choose (k+ℓ) ℓ : ℝ)`. One-sided Stirling; witness is `binomialEntropyError`.
- `main_uniform` (144): `∃η SublinearError, ∀k ℓ 0<ℓ≤k, R ≤ exp(g finalB (ℓ/k)*k + η k) * choose (k+ℓ) ℓ`. Built from `uniformRamseyExpBound_final` + `uniform_choose_entropy_lower_bound`.
- **`main`** (176) — paper t:main, printed form: `∃η, SublinearError η ∧ ∀k ℓ 0<ℓ≤k, R(k,ℓ) ≤ exp( ((-(1/4)r + (3/100)r² + (2/25)r³)·exp(-r))·k + η k ) · choose (k+ℓ) ℓ`, `r=ℓ/k`. NOTE: repo has **no** diagonal `R(k,k) ≤ 4^k`-style corollary; specialize `main`/`.diagonal` yourself.
- `uniformRamseyExpBound_final : UniformRamseyExpBound (F finalB)` — Numerics.lean:25 (assembled via `uniformRamseyExpBound_of_descent`).

--------------------------------------------------------------------------------
## 4. Analytic core (RamseyLean/Numerics/Core.lean)

- **`entropy (r) := (1+r)*log(1+r) - r*log r`** (23).
- `gPoly b r := -(1/4)r + b·r² + (2/25)r³` (27); `g b r := gPoly b r · exp(-r)` (31); **`F b r := entropy r + g b r`** (35); `FSlope b r` (39, = F'); `FCurvature b r` (50, = F''); `curvaturePoly` (45).
- Constants: `preliminaryB := 3/40` (54), `finalB := 3/100` (57), abbrevs `b₀,b₁`. `preliminaryM`, `finalM`, `numericalP b r := 1-exp(-FSlope b r)`, `numericalX b M r := (1-M r)·(numericalP b r)^(1/(1-M r))`.
- Derivatives: `hasDerivAt_entropy {r≠0,1+r≠0} : HasDerivAt entropy (log(1+r)-log r) r` (82); `hasDerivAt_gPoly` (96); `hasDerivAt_g` (108); **`hasDerivAt_F {0<r} : HasDerivAt (F b) (FSlope b r) r`** (118); `hasDerivAt_FSlope {0<r}` (126). `continuousOn_F`, `continuousOn_FSlope` (158,161).
- Sign lemmas on rectangle `b∈Icc finalB preliminaryB`, `r∈Ioc 0 1`: `FCurvature_neg` (220), `FSlope_pos` (295), `F_pos` (338).
- `entropy_gt_mul_log_two {r∈Ioc 0 1} : r*log 2 < entropy r` (329, private). `log_two_le_entropySlope` (273, private): `log 2 ≤ log(1+r)-log r`. `g_lower` (307): `-(r/4) ≤ g b r`.
- **`strictConcaveOn_F {b∈Icc finalB preliminaryB} : StrictConcaveOn ℝ (Ioc 0 1) (F b)`** (354) — via `strictAntiOn_of_hasDerivWithinAt_neg` (F''<0) then `StrictAntiOn.strictConcaveOn_of_deriv`.
- No dedicated entropy-limit lemma here; `entropy` continuity comes through `hasDerivAt_entropy.continuousAt`. Numeric constants used: `Real.log_two_gt_d9`, `Real.two_le_pi` (Main.lean), `exp_neg_mul_one_add_le_one` (212, via `Real.add_one_le_exp`).

--------------------------------------------------------------------------------
## 5. Concave frontier (RamseyLean/Frontier.lean)

- `frontierA D t := exp(-D t)` (23); `frontierB F D t := exp(t*D t - F t)` (28); `frontierY F D x` (47, 3-branch piecewise, param chosen noncomputably); `frontierAParameter`/`frontierBParameter` (34,39). `log_frontierA`,`log_frontierB` (@[simp], 56,61).
- **`concaveOn_le_tangentLine`** (117): `hconcave:ConcaveOn ℝ (Ioc 0 1) F`, `hs t∈Ioc 0 1`, `hderiv:HasDerivAt F (D t) t ⟹ F s ≤ F t + (s-t)*D t`. Uses `ConcaveOn.le_slope_of_hasDerivAt`/`.slope_le_of_hasDerivAt`.
- **`frontier_pair_mem_asymptoticRegion`** (136): given `UniformRamseyExpBound F`, `ConcaveOn`, `hderiv`, `hDpos>0`, `hBunit:frontierB∈Ioo 0 1`, `hAB:frontierA<frontierB`, and `t∈Ioc 0 1` → `frontierA t∈Ioo 0 1 ∧ frontierB t∈Ioo 0 1 ∧ (A,B)∈region ∧ (B,A)∈region`. Core tangent-to-region step.
- `frontier_middle_mem_asymptoticRegion` (185, hyperbolic middle segment). `frontier_mem_asymptoticRegion` (254, full Lemma; needs `StrictConcaveOn`, `hAonto`,`hBonto` level-set surjectivity) → `frontierY x∈Ioo 0 1 ∧ (x,frontierY x)∈region`.

--------------------------------------------------------------------------------
## 6. Descent (RamseyLean/Descent.lean)

- `redGraphDensity G := (∑ deg)/ (n*(n-1))` (33); `redGraphDensity_nonneg`; `exists_compl_degree_gt_of_redGraphDensity_lt` (52, averaging step).
- `bookCorThreshold x μ y k ℓ := sqrt((x⁻¹)^k*(y⁻¹)^ℓ*(μ⁻¹)^ℓ)` (113).
- **`denseCaseExponent (x μ y r : ℝ) := -(log x + r*log μ + r*log y)/2`** (119). SIGN: negative-of-sum-over-2; satisfies `bookCorThreshold_eq_exp_denseCaseExponent` (172): `bookCorThreshold x μ y k ℓ = exp(denseCaseExponent x μ y (ℓ/k) * k)` for `0<k`.
- `exists_small_ratio_erdosSzekeres ε>0` (230): ∃ρ∈Ioo 0 1 s.t. small ratios give `R ≤ exp(ε k)`.
- `Candidate.isGood_of_density_card_product` — BookInduction.lean:3336 (paper t:bookmain): `hμ₀,hx₀,hy₀,hp∈Ioo 0 1`, `hxstrict: x₀ < p^(1/(1-μ₀))*(1-μ₀)`, `hregion:(x₀,y₀)∈asymptoticRegionInterior` → `∃L₀, ∀ large graph …, Candidate.IsGood H A B k ℓ t`. Used in `ramseyBound_of_redDensity` (437).
- `ramseyBound_of_redDensity` (437, paper t:bookCor), `dense_case_uniform` (734, paper c:gen, compact-interval frozen-parameter patches).
- **`uniformRamseyExpBound_of_descent`** (843) — paper t:general. Full hypothesis list (all with F D M X Y : ℝ→ℝ):
  - `hderiv : ∀ r∈Ioc 0 1, HasDerivAt F (D r) r`
  - `hDcont : ContinuousOn D (Ioc 0 1)`
  - `_hMcont : ContinuousOn M (Ioc 0 1)` (unused, kept)
  - `hFnonneg : ∀ r∈Ioc 0 1, 0 ≤ F r`
  - `hDpos : ∀ r∈Ioc 0 1, 0 < D r`
  - `hM : ∀ r∈Ioc 0 1, M r ∈ Ioo 0 1`
  - `hX : ∀ r∈Ioc 0 1, X r ∈ Ioo 0 1`
  - `hY : ∀ r∈Ioc 0 1, Y r ∈ Ioo 0 1`
  - `hXle : ∀ r∈Ioc 0 1, X r ≤ (1-exp(-D r))^(1/(1-M r))*(1-M r)`  (note: ≤, not =)
  - `hregion : ∀ r∈Ioc 0 1, (X r, Y r) ∈ asymptoticRegion`
  - `hslack : ∀ r∈Ioc 0 1, denseCaseExponent (X r)(M r)(Y r) r < F r`
  - ⟹ `UniformRamseyExpBound F`.
- lemmas about denseCaseExponent: `bookCorThreshold_eq_exp_denseCaseExponent` (172); `denseCaseExponent_final_eq` (Numerics/Final.lean:169) `= F finalB r - finalSlack r y`; `denseCaseExponent_preliminary_eq/_lt` (Numerics/Preliminary.lean:77,96). Additivity under log-shift used inline (Descent.lean:645, SelfConsistent.lean:162): shifting `X→X·e^{-η}` adds `η(1+r)/2`.

--------------------------------------------------------------------------------
## 7. Final descent bridge (RamseyLean/Numerics/Final.lean)

- `finalX r := numericalX finalB finalM r` (36); **`finalX_mem_Ioo {r∈Ioc 0 1} : finalX r ∈ Ioo 0 1`** (90) — template for X∈(0,1). `finalX_eq_descent` (95). `hasDerivAt_F` lives in Numerics/Core.lean:118 (NOT NormalizedFunctions).
- `finalM`, `finalMRatio`, `finalARatio`, `finalU`, `finalSlack r y := F finalB r + (log(finalX r)+r log(finalM r)+r log y)/2` (53), `finalNormalizedSlack` (58), `finalY` (222, piecewise second coord).
- `finalSlack_eq_mul_normalized` (156): `finalSlack r y = r · finalNormalizedSlack r y`. Branch bridges: `finalSlack_small/middle/largeCap/large_eq_mul_normalized`.
- Certificate structs (Prop): `FinalRegionCertificate` (348, region-membership obligations), `FinalNumericalCertificate extends FinalRegionCertificate` (424, adds 4 `*_slack_pos` fields).
- `finalY_mem_asymptoticRegion` (371), `finalSlack_pos_of_certificate` (447), **`final_descent_of_certificate hF hcert {r∈Ioc 0 1}`** (484): `finalY r∈Ioo 0 1 ∧ (finalX r,finalY r)∈region ∧ denseCaseExponent (finalX r)(finalM r)(finalY r) r < F finalB r`. This is exactly the 3 outputs `uniformRamseyExpBound_of_descent` consumes.

--------------------------------------------------------------------------------
## 8. Interval arithmetic backend (RamseyLean/Analysis/FixedPointInterval.lean)

Fixed-point at `scale = 10^12` (line 12). Namespace `RamseyLean.FixedPointInterval`.
- `structure Interval := (lo hi : ℤ)` deriving DecidableEq,Repr (14). `value z : ℝ := z/scale` (160). `Interval.Contains I x := value I.lo ≤ x ∧ x ≤ value I.hi` (162).
- Constructors/ops (all pure ℤ): `point z` (19), `add` (20), `neg` (21), `mul` (four-corner via down/up, 31), `mulNonneg` (35, endpoints for ≥0 intervals), `inv` (38, needs lo>0), `divNat`/`mulNat` (44,47), `abs` (50, `⟨0, max|lo||hi|⟩`), `pow` (53, recursive), `down`/`up` (floor/ceil ÷scale, 27,29). Also `sumTerms`, `expPoly`/`expError`/`exp` (61-72, Taylor), `logSeries`/`logError`/`logArgument`/`log` (74-92), `qPoly`/`tPoly`/`ePoly` + `q`/`t`/`e` (normalized-fn evaluators).
- Soundness lemmas (namespace `Interval`, form `Contains.OP`): `contains_point` (271), `Contains.add/neg/mul/mulNonneg/inv/divNat/mulNat/abs/pow` (274-497), `contains_sumTerms` (499), `.expPoly/.expError` (509,518), **`Contains.exp {hn:0<n}{|value lo|≤1}{|value hi|≤1}`** (530), `.logSeries/.logError` (567,578), `logArgument_contains` (601).
- Safety predicates (Bool, kernel-decidable): `nonneg`,`positive` (129,130), `expSafe n I` (131, needs 0<n ∧ |lo|,|hi|≤scale), `qtSafe` (133), `eSafe` (139), `logSafe` (142).
- Namespace `Sound` "_of_safe" wrappers driven by decidable checks: **`contains_exp_of_safe`** (871), **`contains_log_of_safe`** (884), `contains_q_of_safe`/`contains_t_of_safe`/`contains_e_of_safe` (895,912,929). Also `checkLower`/`checkLowerEq` + `value_lt_of_checkLower`/`value_le_of_checkLowerEq` (615-636, extract strict/nonstrict scalar bounds from an enclosure).
- **Taylor-depth conventions in practice**: GNNW pass `exp 12`, `log 16`, `q/t 16`, `e` similar. See FinalCertificate.lean `common`: `exp 12 …`, `t 16 m`, `log 16 …`. `logArgument` maps `z ↦ (z-1)/(z+1)` so log Taylor is on artanh series.

--------------------------------------------------------------------------------
## 9. Reflected expressions (RamseyLean/Analysis/IntervalExpression.lean)

Namespace `RamseyLean.IntervalExpression`. Center-radius `Interval := ⟨center,radius⟩` (30), `Contains I x := |x-center|≤radius` (43), `lower/upper/ofBounds` (37,39,49). Ops `add/neg/mul/mulNonneg/inv` with `Contains.*` proofs (52-145).
- `inductive Expr` (150): `const q | var | add | neg | mul | mulNonneg | inv | exp n | log n | logOnePlusRatio n | negLogOneSubRatio n | oneSubExpNegRatio n`. `n` = Taylor degree.
- `Expr.eval x e` (167, real semantics), `Expr.bound input e` (182, computed enclosure), `Expr.Safe input e` (223, domain/Taylor side conditions as Prop).
- **`Expr.bound_sound {hx:input.Contains x} (e)(hsafe:Safe input e) : (bound input e).Contains (eval x e)`** (243). Helpers `lower_le_eval` (307), `eval_le_upper` (312). Syntax sugar `sub`,`div`,`pow` (296-303).
- Mesh wrappers (RamseyLean/Analysis/IntervalMesh.lean): `unitInterval N k` (22), `affineInterval a b N k` (26); **`eval_ge_of_unitMesh N (hN) e L (hcert: ∀ k≤N, Safe ∧ L ≤ bound.lower) {r∈Icc 0 1} : L ≤ eval r e`** (32); `eval_ge_of_affineMesh` (50). Mesh selection: UniformMesh.lean `unitPoint N k := k/N` (18), `floor_mem_unitMesh` (22), `affinePoint`/`floor_mem_affineMesh` (51,55).

--------------------------------------------------------------------------------
## 10. Certificate pattern (Numerics/FinalCertificate*.lean, FinalCertificateData/*)

Two interval backends: the reflected `IntervalExpression` DAG (small proofs) AND the ℤ `FixedPointInterval` DAG used by the generated data. The **final data uses FixedPointInterval**.
- Analyzers (FinalCertificate.lean): `common r` (95, staged enclosure of finalU & subexprs), `small`/`middle`/`largeAt`/`largeCap`/`large` (170-260) build `OuterResult{safe,parameter,coordinateGap,slack}` / `ScalarResult{safe,slack}`. `safe` is a `Bool` conjunction of `expSafe 12`/`logSafe 16`/`qtSafe 16`/`nonneg`/`positive`. Rational literals via `rationalInterval p q := divNat (point (p*scale)) q` (21).
- Row encoding (FinalCertificateData/Support.lean, FinalCertificateMesh.lean): `uniformCell start step k := ⟨start+step*k, start+step*(k+1)⟩` (Mesh:20); `iv lo hi` shorthand (Support:12). A chunk file (e.g. `CrossingCoarseChunk000.lean`) has: `indices : List Nat` (a `(List.range 1000).filter … |>.drop _ |>.take 25`), `rows : List <Data>` of 25 hand-generated rows, `inputs := indices.map (uniformCell 0 1000000000)`, `pairs := inputs.zip rows`, `checks := pairs.all crossingPairCheck`.
- **`decide` idiom (kernel, NOT native_decide — no `native_decide` anywhere in repo)**: each chunk proves
  `set_option maxHeartbeats 0 in / set_option maxRecDepth 100000 in / theorem checks_true : checks = true := by decide`
  plus `theorem map_fst : pairs.map Prod.fst = inputs := by decide`. **Chunk size = 25 rows**; ~415 chunk files. Crossing cells (indices 257,258,359,360) are filtered out and handled by fine meshes.
- Pair checks (Support.lean): `smallCoordinatePairCheck`, `middlePairCheck`, `capPairCheck`, `largePairCheck band`, `crossingPairCheck` — each `intervalEq input && recordEq band && <rowCheck>`. `exists_of_map_fst` (Support:37) lifts a `pairs.all checker` + `map Prod.fst = inputs` into `∀ I∈inputs, ∃ d, checker (I,d)`.
- Row soundness → real (FinalCertificateCoverage.lean): `small_of_check`/`middle_pos_of_check`/`cap_pos_of_check`/`large_of_check`/`crossing_{b,a}{Below,Above}_of_check` (131-320) turn one checked row into the real inequality on its cell. `*_on_uniform_band` (323-466) quantify over a whole band via `exists_uniformCell` (Mesh:71) + `uniformCell_contains`.
- Coverage → certificate (FinalCertificateAssembly.lean): `structure FinalContinuumCertificate` (21, 8 continuum fields with overlapping rational cut points 258/1000, 2578/10000, 3604/10000, 3605/10000, 361/1000) → `finalNumericalCertificate_of_continuum` (57) routes them into `FinalNumericalCertificate` by pure case analysis on the two irrational crossings.
- Assembly (FinalCertificateConcrete.lean): `finalRowCertificate : FinalRowCertificate` (21, fields = `Data.exists_checked_*`) → **`finalNumericalCertificate : FinalNumericalCertificate`** (39) via `finalNumericalCertificate_of_rows`. Consumed by Numerics.lean:46 into `uniformRamseyExpBound_final`.

--------------------------------------------------------------------------------
## 11. Mathlib lemmas GNNW rely on (by usage tally)

- Strict monotonicity from derivative sign: `strictAntiOn_of_hasDerivWithinAt_neg` (Core.lean:357) — used with F''<0.
- Concavity from monotone derivative: `StrictAntiOn.strictConcaveOn_of_deriv` (Core.lean:368). `StrictConcaveOn.concaveOn` used to downgrade. Slope facts: `ConcaveOn.le_slope_of_hasDerivAt`, `ConcaveOn.slope_le_of_hasDerivAt` (Frontier.lean:123-131).
- MVT: `exists_hasDerivAt_eq_slope` (Descent.lean:377).
- exp/log inequalities: `Real.add_one_le_exp` (Core.lean:216), `Real.log_le_sub_one_of_pos`, `Real.log_lt_sub_one_of_pos`, `Real.exp_le_exp`/`Real.exp_lt_exp`, `Real.le_exp_of_log_le`, `Real.log_le_iff_le_exp`. Numeric: `Real.log_two_gt_d9`, `Real.two_le_pi`.
- Limits: `tendsto_pow_atTop_atTop_of_one_lt` (Descent, x4), `Real.tendsto_exp_atTop`, `Real.isLittleO_log_id_atTop` (`.natCast_atTop`) for `log k = o(k)` (Main.lean:86, sublinear errors). Uniform continuity on compacts: `IsCompact.uniformContinuousOn_of_continuous` (Descent:311). `x log x → 0` at 0 is NOT used as a named lemma; entropy handled analytically via `hasDerivAt_entropy` + `entropy_gt_mul_log_two`.
- Stirling (Main.lean): `Stirling.stirlingSeq*`, `Stirling.log_stirlingSeq'_antitone`, `Stirling.le_log_factorial_stirling`, `Nat.choose_mul_factorial_mul_factorial`.

--------------------------------------------------------------------------------
## Reuse cheat-sheet for a new rate function F̂

1. Prove `HasDerivAt F̂ D̂`, `ContinuousOn D̂`, `F̂≥0`, `D̂>0` on `Ioc 0 1` (pattern: Core.lean §4).
2. Pick M,X,Y with X∈Ioo 0 1, Y∈Ioo 0 1, region membership, and `denseCaseExponent X M Y r < F̂ r` — discharge the last via a numerical certificate (§7,§10) or `final_descent_of_certificate`.
3. `uniformRamseyExpBound_of_descent` (§6) → `UniformRamseyExpBound F̂`.
4. Feed into `frontier_*` (§5) / `mem_asymptoticRegion_of_uniform_bound` (§2) for region facts, and combine with `uniform_choose_entropy_lower_bound` (§3) for a printed R(k,ℓ) bound (`main_uniform` is the template).

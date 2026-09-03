import RamseyLean.Descent
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Spline certificate (Bootstrap2): data structures and real-valued definitions

See `SPEC.md` in this directory.  A certificate is a list of `Cell`s covering
`[λ₀, 1]`, `λ₀ = 10^{-4}`.  From the data we define the real functions
`Dcert` (piecewise linear, clamped), `Mcert` (same), `Fcert` (integral of
`Dcert`, hence C¹ piecewise quadratic), and step functions `Xcert`, `Ycert`.
These are fed to `uniformRamseyExpBound_selfConsistent`.

Scales: `SC = 10^12` for `lam, d, M, X, Y`; `FS = 2 * 10^24` for `F`.
-/

namespace RamseyLean
namespace Bootstrap2

open Set

/-- Scale of `lam, d, M, X, Y` data (matches `FixedPointInterval`). -/
def SC : Int := 10 ^ 12

/-- Scale of `F` data: `FS = 2 * SC ^ 2`, so that the trapezoid chain identity
`F_{j+1} = F_j + (d_j + d_{j+1}) * (lam_{j+1} - lam_j)` is exact in `Int`. -/
def FS : Int := 2 * 10 ^ 24

/-- Left end of the certificate range, `λ₀ = 10^{-4}` (scaled: `10^8`). -/
def L0 : Int := 10 ^ 8

/-- `λ₀` as a real number. -/
noncomputable def lam0 : ℝ := (L0 : ℝ) / (SC : ℝ)

/-- A certificate node: abscissa, `F`-value, derivative, book parameter. -/
structure Node where
  lam : Int  -- scale SC
  F   : Int  -- scale FS
  d   : Int  -- scale SC
  M   : Int  -- scale SC
deriving Repr, DecidableEq

/-- A certificate cell `[n0.lam, n1.lam]` with its per-cell constants and the
two tangent-witness nodes (each must equal an actual node of the certificate;
that is the global merge check). -/
structure Cell where
  n0 : Node
  n1 : Node
  X  : Int   -- scale SC
  Y  : Int   -- scale SC
  wa : Node  -- witness for orientation a: `F s ≤ -log X - s log Y`
  wb : Node  -- witness for orientation b: `F s ≤ -log Y - s log X`
deriving Repr, DecidableEq

/-- Real abscissa of a node. -/
noncomputable def Node.lamR (n : Node) : ℝ := (n.lam : ℝ) / (SC : ℝ)

/-- Real `F`-value of a node. -/
noncomputable def Node.FR (n : Node) : ℝ := (n.F : ℝ) / (FS : ℝ)

/-- Real derivative value of a node. -/
noncomputable def Node.dR (n : Node) : ℝ := (n.d : ℝ) / (SC : ℝ)

/-- Real `M`-value of a node. -/
noncomputable def Node.MR (n : Node) : ℝ := (n.M : ℝ) / (SC : ℝ)

/-- The node sequence of a certificate. -/
def nodes (cells : List Cell) : List Node :=
  match cells with
  | [] => []
  | c :: _ => c.n0 :: cells.map (·.n1)

/-- Piecewise-linear interpolation through `(a_i, v_i)` (both at scale `SC`),
clamped to the first value on the left of `a_0` and to the last value on the
right of `a_k`.  On `[a_i, a_{i+1}]` it is the chord. -/
noncomputable def plInterp : List (Int × Int) → ℝ → ℝ
  | [], _ => 0
  | [(_, v)], _ => (v : ℝ) / (SC : ℝ)
  | (a, v) :: (b, w) :: rest, r =>
      if r ≤ (b : ℝ) / (SC : ℝ) then
        if r ≤ (a : ℝ) / (SC : ℝ) then (v : ℝ) / (SC : ℝ)
        else (v : ℝ) / (SC : ℝ) +
          (r - (a : ℝ) / (SC : ℝ)) *
            (((w : ℝ) - (v : ℝ)) / ((b : ℝ) - (a : ℝ)))
      else plInterp ((b, w) :: rest) r

/-- Step function: value `v_i` on `(a_i, a_{i+1}]`, clamped to `v_0` on
`(-∞, a_1]` and to the last value beyond the last breakpoint. -/
noncomputable def stepInterp : List (Int × Int) → ℝ → ℝ
  | [], _ => 0
  | [(_, v)], _ => (v : ℝ) / (SC : ℝ)
  | (_, v) :: (b, w) :: rest, r =>
      if r ≤ (b : ℝ) / (SC : ℝ) then (v : ℝ) / (SC : ℝ)
      else stepInterp ((b, w) :: rest) r

/-- The certificate's derivative function `D` (piecewise linear, clamped). -/
noncomputable def Dcert (cells : List Cell) : ℝ → ℝ :=
  plInterp ((nodes cells).map fun n => (n.lam, n.d))

/-- The certificate's book parameter `M` (piecewise linear, clamped). -/
noncomputable def Mcert (cells : List Cell) : ℝ → ℝ :=
  plInterp ((nodes cells).map fun n => (n.lam, n.M))

/-- The certificate's rate function
`F r = F_0/FS + ∫_{λ₀}^r D`: C¹ with `F' = Dcert`, piecewise quadratic,
linear with slope `d_0` on `(0, λ₀]`, and `F(λ_j) = F_j / FS` exactly (chain
identity). -/
noncomputable def Fcert (cells : List Cell) : ℝ → ℝ := fun r =>
  (match cells with
    | [] => 0
    | c :: _ => c.n0.FR) + ∫ t in lam0..r, Dcert cells t

/-- The certificate's `X` step function (cell constant, tail = cell 0). -/
noncomputable def Xcert (cells : List Cell) : ℝ → ℝ :=
  stepInterp (cells.map fun c => (c.n0.lam, c.X))

/-- The certificate's `Y` step function (cell constant, tail = cell 0). -/
noncomputable def Ycert (cells : List Cell) : ℝ → ℝ :=
  stepInterp (cells.map fun c => (c.n0.lam, c.Y))

/-- All pointwise hypotheses of `uniformRamseyExpBound_selfConsistent` at a
single `r` (the non-structural ones: everything except `hderiv`, `hDcont`,
`hMcont`).  The checker's soundness theorem produces these for every `r` in a
verified cell; the tail lemma produces them on `(0, λ₀]`. -/
def LadderHypsAt (F D M X Y : ℝ → ℝ) (r : ℝ) : Prop :=
  0 ≤ F r ∧ 0 < D r ∧ M r ∈ Ioo (0 : ℝ) 1 ∧ X r ∈ Ioo (0 : ℝ) 1 ∧
  Y r ∈ Ioo (0 : ℝ) 1 ∧
  X r ≤ (1 - Real.exp (-(D r))) ^ (1 / (1 - M r)) * (1 - M r) ∧
  (∀ s ∈ Ioc (0 : ℝ) 1, F s ≤ -Real.log (X r) - s * Real.log (Y r)) ∧
  (∀ s ∈ Ioc (0 : ℝ) 1, F s ≤ -Real.log (Y r) - s * Real.log (X r)) ∧
  denseCaseExponent (X r) (M r) (Y r) r < F r

/-- Tangent upper bound for the spline: at every node `u` of the certificate,
the tangent line at `u` dominates `Fcert` on `(0, 1]`.  Proved once in
`Spline.lean` from concavity (`d` non-increasing); consumed by the checker's
soundness theorem through the witness nodes. -/
def SplineTangentUB (cells : List Cell) : Prop :=
  ∀ n ∈ nodes cells, ∀ s ∈ Ioc (0 : ℝ) 1,
    Fcert cells s ≤ n.FR + (s - n.lamR) * n.dR

end Bootstrap2
end RamseyLean

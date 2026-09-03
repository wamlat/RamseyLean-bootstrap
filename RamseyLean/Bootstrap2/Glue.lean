import RamseyLean.Bootstrap2.Spline
import RamseyLean.Bootstrap2.Cover

/-!
# Glue helpers: chain abscissa bound and tail linearity

Two small facts needed by `Main2.lean` that sit between the spline layer and
the checker soundness:

* every cell's left abscissa is `≥` the head's (chain propagation);
* `Fcert` is linear with slope `d₀` on `(-∞, λ₀]` (from the clamped `Dcert`).
-/

namespace RamseyLean
namespace Bootstrap2

open Set

/-- Chain propagation: every cell's left abscissa is at least the head's. -/
theorem lam_ge_head :
    ∀ (cells : List Cell) (c0 : Cell), cells.head? = some c0 →
      List.IsChain (fun c c' => c.n1 = c'.n0) cells →
      (∀ c ∈ cells, c.n0.lam < c.n1.lam) →
      ∀ c ∈ cells, c0.n0.lam ≤ c.n0.lam := by
  intro cells
  induction cells with
  | nil => intro c0 h; simp at h
  | cons a rest ih =>
    intro c0 h0 hchain hmono c hc
    obtain rfl : c0 = a := ((by simpa using h0 : a = c0)).symm
    rcases List.mem_cons.mp hc with rfl | hc
    · exact le_rfl
    · match rest, hchain, hc with
      | a' :: rest', hchain, hc =>
        have haa' : c0.n1 = a'.n0 := hchain.rel_head? rfl
        have h1 : a'.n0.lam ≤ c.n0.lam :=
          ih a' rfl hchain.tail
            (fun d hd => hmono d (List.mem_cons_of_mem _ hd)) c hc
        have h2 : c0.n0.lam < a'.n0.lam := by
          rw [← haa']; exact hmono c0 (List.mem_cons_self ..)
        omega

/-- The head node's abscissa is `λ₀`. -/
theorem head_lamR {cells : List Cell} (h : ChainOK cells)
    {c0 : Cell} (hc0 : cells.head? = some c0) : c0.n0.lamR = lam0 := by
  have hl : c0.n0.lam = L0 := by
    have hh := h.2.1
    rw [hc0] at hh
    simpa using hh
  rw [Node.lamR, hl]; rfl

/-- `Fcert` is linear with slope `(head).n0.dR` on `(-∞, λ₀]`:
`F r = F(λ₀) + (r − λ₀) · d₀`. -/
theorem Fcert_tail_linear {cells : List Cell} (h : ChainOK cells)
    {c0 : Cell} (hc0 : cells.head? = some c0) :
    ∀ r ≤ lam0, Fcert cells r = c0.n0.FR + (r - c0.n0.lamR) * c0.n0.dR := by
  intro r hr
  have hlam0 : c0.n0.lamR = lam0 := head_lamR h hc0
  obtain ⟨rest, rfl⟩ : ∃ rest, cells = c0 :: rest := by
    cases cells with
    | nil => simp at hc0
    | cons a l =>
      have ha : a = c0 := by simpa using hc0
      exact ⟨l, by rw [ha]⟩
  have hDtail := tailVals h (cells := c0 :: rest) (c₀ := c0) rfl
  have hEq : Set.EqOn (Dcert (c0 :: rest)) (fun _ => c0.n0.dR)
      (Set.uIcc lam0 r) := by
    intro t ht
    have htle : t ≤ lam0 := by
      rcases Set.mem_uIcc.mp ht with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact h2.trans hr
      · exact h2
    exact (hDtail t htle).1
  have hInt : (∫ t in lam0..r, Dcert (c0 :: rest) t) = (r - lam0) * c0.n0.dR := by
    rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_const,
      smul_eq_mul]
  have hF : Fcert (c0 :: rest) r =
      c0.n0.FR + ∫ t in lam0..r, Dcert (c0 :: rest) t := rfl
  rw [hF, hInt, hlam0]

end Bootstrap2
end RamseyLean

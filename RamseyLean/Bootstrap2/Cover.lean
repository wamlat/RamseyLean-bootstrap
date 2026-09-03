import RamseyLean.Bootstrap2.Defs

/-!
# Coverage: every `r ∈ (λ₀, 1]` lies in some cell

From the chain facts (contiguity `c.n1 = c'.n0`, head abscissa `λ₀`, last
abscissa `1`) we locate, for each `r ∈ Ioc lam0 1`, a cell `c` of the
certificate with `r ∈ Ioc c.n0.lamR c.n1.lamR`.  This is the dispatch lemma of
the glue layer (`Main2.lean`).
-/

namespace RamseyLean
namespace Bootstrap2

open Set

/-- Auxiliary: walking a contiguous cell list starting at abscissa `a`,
every `r` with `a < r ≤ (last).n1.lamR` is covered by some cell. -/
theorem cover_aux :
    ∀ (cells : List Cell), cells ≠ [] →
      List.IsChain (fun c c' => c.n1 = c'.n0) cells →
      ∀ r : ℝ, (∀ c0, cells.head? = some c0 → c0.n0.lamR < r) →
        (∀ cN, cells.getLast? = some cN → r ≤ cN.n1.lamR) →
        ∃ c ∈ cells, r ∈ Ioc c.n0.lamR c.n1.lamR := by
  intro cells
  induction cells with
  | nil => intro h; exact absurd rfl h
  | cons c rest ih =>
    intro _ hchain r hlo hhi
    rcases le_or_gt r c.n1.lamR with hle | hgt
    · exact ⟨c, List.mem_cons_self ..,
        ⟨hlo c rfl, hle⟩⟩
    · match rest, hchain with
      | [], _ =>
        exact absurd (hhi c rfl) (not_le.mpr hgt)
      | c' :: rest', hchain =>
        have hcc' : c.n1 = c'.n0 := hchain.rel_head? (by simp)
        obtain ⟨cw, hcw, hmem⟩ :=
          ih (by simp) (hchain.tail) r
            (fun c0 h0 => by
              obtain rfl : c' = c0 := by simpa using h0
              rw [← hcc']; exact hgt)
            (fun cN hN => hhi cN (by
              simpa [List.getLast?_cons_cons] using hN))
        exact ⟨cw, List.mem_cons_of_mem _ hcw, hmem⟩

/-- Coverage: given the chain facts, every `r ∈ (λ₀, 1]` lies in a cell. -/
theorem cover (cells : List Cell) (hne : cells ≠ [])
    (hchain : List.IsChain (fun c c' => c.n1 = c'.n0) cells)
    (hhead : ∀ c0, cells.head? = some c0 → c0.n0.lam = L0)
    (hlast : ∀ cN, cells.getLast? = some cN → cN.n1.lam = SC) :
    ∀ r ∈ Ioc lam0 (1 : ℝ), ∃ c ∈ cells, r ∈ Ioc c.n0.lamR c.n1.lamR := by
  intro r hr
  refine cover_aux cells hne hchain r ?_ ?_
  · intro c0 h0
    have : c0.n0.lamR = lam0 := by
      rw [Node.lamR, hhead c0 h0]; rfl
    rw [this]; exact hr.1
  · intro cN hN
    have : cN.n1.lamR = 1 := by
      rw [Node.lamR, hlast cN hN]
      norm_num [SC]
    rw [this]; exact hr.2

end Bootstrap2
end RamseyLean

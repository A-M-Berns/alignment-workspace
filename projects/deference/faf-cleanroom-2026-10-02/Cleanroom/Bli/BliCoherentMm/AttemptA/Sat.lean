import Cleanroom.Bli.BliCoherentMm.AttemptA.Maker

/-!
# `bli-coherent-mm` (attempt A) · Sat: full-support coherent prices decide satisfiability (T5)

**T5 of the mandate** (bli-soto-a-2-004, PDF 04 fn. 2: "check whether it has positive
probability"). For a world measure `w` over `D` with full support on `WD D B`,
`0 < π w φ` iff some `D`-consistent finite world over `B` atoms holds `φ`
(`pos_iff_satisfiable`); in `PCWorld` terms (`pos_iff_satisfiable_pcWorld`, under the atom
bound), iff `φ` is satisfiable together with `D` — "`D`-relative SAT over `B` atoms". At the
interior maker (`interior_quote_pos_iff`) this says its day-`n` prices on `S` decide
`D`-relative satisfiability of every `φ ∈ S`, which is why the record prices `mentionedSet n`
(the maker's own `2^B` enumeration) and why the `smallSet` variant is a complexity question, not
an existence one (findings).

Sources: [[bli-coherent-mm-mandate]] T5; bli-soto-a-2-004 (PDF 04 fn. 2).
-/

namespace Cleanroom.Bli.BliCoherentMm.AttemptA

open LogicalInduction LO.Propositional BoolPCWorld Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliOverlay

/-- **T5. A full-support marginal is positive exactly on the sentences some `D`-consistent finite
world holds.**
Source: [[bli-coherent-mm-mandate]] T5; bli-soto-a-2-004
Kind: P
Fidelity: exact
Hyps: (a) `hw` (world measure), `hfull` (full support on `WD D B`) -/
theorem pos_iff_satisfiable {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : IsWorldMeasure w D) (hfull : ∀ u ∈ WD D B, 0 < w u) (φ : Sentence) :
    0 < marginal w φ ↔ ∃ u ∈ WD D B, (worldOf u).Holds φ := by
  constructor
  · intro hpos
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    have hzero : marginal w φ = 0 := by
      unfold marginal
      apply Finset.sum_eq_zero
      intro u _
      by_cases hu : u ∈ WD D B
      · rw [payoutRat_of_not_holds (hcon u hu), mul_zero]
      · have h : w u = 0 := by
          by_contra h
          exact hu (mem_WD.mpr (hw.2.2 u h))
        rw [h, zero_mul]
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  · rintro ⟨u, hu, hφ⟩
    exact marginal_pos_of_holds hw (hfull u hu) hφ

/-- **T5, `PCWorld` form: full-support coherent prices decide `D`-relative satisfiability.** Under
the atom bound on `D` and `φ`, `0 < π w φ` iff some `PCWorld` consistent with `D` holds `φ`.
Source: [[bli-coherent-mm-mandate]] T5; bli-soto-a-2-004 ("satisfiable by a world consistent with `D_n`")
Kind: C
Fidelity: exact
Hyps: (a) `hw`, `hfull`, `hD`, `hφ` (atom bounds) -/
theorem pos_iff_satisfiable_pcWorld {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : IsWorldMeasure w D) (hfull : ∀ u ∈ WD D B, 0 < w u) (hD : ∀ ψ ∈ D, atomBound ψ ≤ B)
    {φ : Sentence} (hφ : atomBound φ ≤ B) :
    0 < marginal w φ ↔ ∃ v : PCWorld, v.ConsistentWith D ∧ v.Holds φ := by
  rw [pos_iff_satisfiable hw hfull]
  constructor
  · rintro ⟨u, hu, h⟩
    exact ⟨worldOf u, mem_WD.mp hu, h⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨_, restrict_mem_WD hD hv, (holds_worldOf_restrict v hφ).mpr h⟩

/-- **T5 at the interior maker**: its day-`n` quote of `φ ∈ S` is positive iff `φ` is satisfiable
together with `D` (over `B` atoms): the interior maker's prices decide `D`-relative SAT on `S`.
Source: [[bli-coherent-mm-mandate]] T5 (corollary); bli-soto-a-2-004
Kind: C
Fidelity: exact
Hyps: (a) `hD`, `hφ` (atom bounds), `hS`, `hW`, `hε` -/
theorem interior_quote_pos_iff {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (S : Finset Sentence) (hS : mentionedSet T ⊆ S)
    (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D) {ε : ℚ} (hε : 0 < ε)
    (hD : ∀ ψ ∈ D, atomBound ψ ≤ B) {φ : Sentence} (hφS : φ ∈ S) (hφ : atomBound φ ≤ B) :
    0 < (interiorCoherentMarketMaker T past D B S hS hW hε).quote φ ↔
      ∃ v : PCWorld, v.ConsistentWith D ∧ v.Holds φ := by
  rw [interior_quote_eq_pi T past D B S hS hW hε hφS]
  exact pos_iff_satisfiable_pcWorld (interiorWeights_isWorldMeasure T past D B S hS hW hε)
    (interior_fullSupport T past D B S hS hW hε) hD hφ

end Cleanroom.Bli.BliCoherentMm.AttemptA

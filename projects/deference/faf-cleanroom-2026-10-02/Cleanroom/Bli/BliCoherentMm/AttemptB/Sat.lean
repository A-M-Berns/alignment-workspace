import Cleanroom.Bli.BliCoherentMm.AttemptB.Interior

/-!
# `bli-coherent-mm` (attempt B) · Sat: full-support coherent prices decide satisfiability (T5)

Soto's PDF 04 fn. 2 ("we can … query whether that formula is satisfiable, by checking whether it
has positive probability"), made precise and relative to a stage: for a world measure `w` with
full support on `W_D B`, `0 < π w φ` **iff** some `D`-consistent finite world holds `φ`
(`pos_iff_satisfiable`), and — within the atom bound — iff some `D`-consistent `PCWorld` holds
`φ` (`pos_iff_satisfiable_pcWorld`). Instantiated at the interior maker
(`interior_pos_iff_satisfiable`): the interior maker's day-`n` prices decide `D`-relative SAT
over `B` atoms on `S`. This is why the record prices `mentionedSet T` (the maker's own
enumeration of `|W_D| ≤ 2^B` worlds), and why the `smallSet` variant is a complexity question,
not an existence one (Known issue 4; findings).

Sources: [[bli-coherent-mm-mandate]] T5; bli-soto-a-2-inventory 2-004 (PDF 04 fn. 2).
-/

namespace Cleanroom.Bli.BliCoherentMm.AttemptB

open LogicalInduction LogicalInduction.BoolPCWorld LO.Propositional Cleanroom.Bli.BliFound
  Cleanroom.Bli.BliOverlay Cleanroom.Bli.BliFinite Finset

noncomputable section

/-- A world measure prices a sentence no `D`-consistent finite world holds at `0`.
Source: [[bli-coherent-mm-mandate]] T5
Kind: L
Fidelity: exact -/
lemma piTable_eq_zero_of_forall_not_holds {D : Finset Sentence} {B : ℕ} {w : FiniteWorld B → ℚ}
    (hw : IsWorldMeasure D B w) {φ : Sentence}
    (h : ∀ u ∈ worldsOf D B, ¬ (worldOf u).Holds φ) : piTable w φ = 0 := by
  unfold piTable
  apply sum_eq_zero
  intro u _
  by_cases hu : w u = 0
  · rw [hu, zero_mul]
  · rw [payoutRat_of_not_holds (h u (mem_worldsOf.mpr (hw.2.2 u hu))), mul_zero]

/-- **T5. Full-support coherent prices decide satisfiability** (finite-world form): for a world
measure with full support on `W_D B`, `0 < π w φ` iff some `D`-consistent finite world holds
`φ`. No atom bound is needed in this form (the worlds are the maker's own).
Source: [[bli-coherent-mm-mandate]] T5; PDF 04 fn. 2 (bli-soto-a-2-004)
Kind: P
Fidelity: exact (relative to `D`; "satisfiable by a world consistent with `D`")
Hyps: (a) `hw`, `hfull` — the interior maker supplies both -/
theorem pos_iff_satisfiable {D : Finset Sentence} {B : ℕ} {w : FiniteWorld B → ℚ}
    (hw : IsWorldMeasure D B w) (hfull : ∀ u ∈ worldsOf D B, 0 < w u) (φ : Sentence) :
    0 < piTable w φ ↔ ∃ u ∈ worldsOf D B, (worldOf u).Holds φ := by
  constructor
  · intro hpos
    by_contra h
    simp only [not_exists, not_and] at h
    have := piTable_eq_zero_of_forall_not_holds hw h
    rw [this] at hpos
    exact lt_irrefl _ hpos
  · exact piTable_pos_of_exists_holds hw hfull

/-- **T5, `PCWorld` form**: within the atom bound, `0 < π w φ` iff some `PCWorld` consistent
with `D` holds `φ` — `D`-relative propositional satisfiability of `φ`.
Source: [[bli-coherent-mm-mandate]] T5
Kind: P
Fidelity: exact
Hyps: (a) `hBD`, `hφ` (the atom bound covers `D` and `φ`) -/
theorem pos_iff_satisfiable_pcWorld {D : Finset Sentence} {B : ℕ} {w : FiniteWorld B → ℚ}
    (hw : IsWorldMeasure D B w) (hfull : ∀ u ∈ worldsOf D B, 0 < w u)
    (hBD : ∀ ψ ∈ D, atomBound ψ ≤ B) {φ : Sentence} (hφ : atomBound φ ≤ B) :
    0 < piTable w φ ↔ ∃ v : PCWorld, v.ConsistentWith D ∧ v.Holds φ := by
  rw [pos_iff_satisfiable hw hfull]
  constructor
  · rintro ⟨u, hu, hφu⟩
    exact ⟨worldOf u, mem_worldsOf.mp hu, hφu⟩
  · rintro ⟨v, hv, hφv⟩
    exact ⟨_, restrict_mem_worldsOf hBD hv, (holds_worldOf_restrict v hφ).mpr hφv⟩

/-- **T5 at the interior maker**: its day-`n` quote of `φ ∈ S` is positive iff `φ` is
satisfiable by a `D`-consistent world (within the atom bound) — the interior maker's prices
decide `D`-relative SAT on `S`.
Source: [[bli-coherent-mm-mandate]] T5; PDF 04 fn. 2
Kind: C
Fidelity: exact
Hyps: (a) `hB`, `hW`, `hS`, `hε`, `hφB` -/
theorem interior_pos_iff_satisfiable {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (hB : ∀ φ ∈ mentionedSet T ∪ D, atomBound φ ≤ B)
    (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D) (S : Finset Sentence)
    (hS : mentionedSet T ⊆ S) (ε : ℚ) (hε : 0 < ε) {φ : Sentence} (hφ : φ ∈ S)
    (hφB : atomBound φ ≤ B) :
    0 < (interiorCoherentMarketMaker T past D B hB hW S hS ε hε).quote φ ↔
      ∃ v : PCWorld, v.ConsistentWith D ∧ v.Holds φ := by
  rw [interior_quote_eq_pi T past D B hB hW S hS ε hε hφ]
  exact pos_iff_satisfiable_pcWorld (interior_isWorldMeasure T past D B hB hW S hS ε hε)
    (interior_fullSupport T past D B hB hW S hS ε hε)
    (fun ψ hψ => hB ψ (Finset.mem_union_right _ hψ)) hφB

end

end Cleanroom.Bli.BliCoherentMm.AttemptB

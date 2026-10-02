import Cleanroom.Bli.BliCoherentMm.Maker
import Cleanroom.Bli.BliCoherentMm.AttemptA.Sat
import Cleanroom.Bli.BliCoherentMm.AttemptB.Sat

/-!
# `bli-coherent-mm` · Sat (reconciled): T5, full-support coherent prices decide satisfiability

**Of record: attempt A's declarations**; attempt B proved the same three statements (finite
form, `PCWorld` form, at the interior maker) over its own names, and the finite form is given
by both routes (`pos_iff_satisfiable`, `pos_iff_satisfiable_viaB`). PDF 04 fn. 2 ("check
whether it has positive probability") is exactly this, relative to the stage: the interior
maker's day-`n` prices decide `D`-relative SAT on `S` over `B` atoms — which is why the record
prices `mentionedSet T` (the maker's own enumeration, `2^B` worlds) and why coherence on all of
`smallSet n` is a cost question, not an existence one (findings).

Sources: [[bli-coherent-mm-mandate]] T5; bli-soto-a-2-004 (PDF 04 fn. 2).
-/

namespace Cleanroom.Bli.BliCoherentMm

open LogicalInduction LO.Propositional BoolPCWorld Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliOverlay

/-- **T5 (of record). A full-support marginal is positive exactly on the sentences some
`D`-consistent finite world holds.**
Source: [[bli-coherent-mm-mandate]] T5; bli-soto-a-2-004
Kind: P
Fidelity: exact
Hyps: (a) `hw` (world measure), `hfull` (full support on `WD D B`) -/
theorem pos_iff_satisfiable {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : IsWorldMeasure w D) (hfull : ∀ u ∈ WD D B, 0 < w u) (φ : Sentence) :
    0 < marginal w φ ↔ ∃ u ∈ WD D B, (worldOf u).Holds φ :=
  AttemptA.pos_iff_satisfiable hw hfull φ

/-- **T5, attempt B's independent proof** of the record statement.
Source: [[bli-coherent-mm-mandate]] T5; §Deliverables (cross-check)
Kind: P
Fidelity: exact
Hyps: (a) as above -/
theorem pos_iff_satisfiable_viaB {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : IsWorldMeasure w D) (hfull : ∀ u ∈ WD D B, 0 < w u) (φ : Sentence) :
    0 < marginal w φ ↔ ∃ u ∈ WD D B, (worldOf u).Holds φ := by
  rw [WD_eq_attemptB]
  exact AttemptB.pos_iff_satisfiable hw.toB
    (fun u hu => hfull u (by rw [WD_eq_attemptB]; exact hu)) φ

/-- **T5, `PCWorld` form: full-support coherent prices decide `D`-relative satisfiability.**
Under the atom bound on `D` and `φ`, `0 < π w φ` iff some `PCWorld` consistent with `D` holds
`φ`.
Source: [[bli-coherent-mm-mandate]] T5; bli-soto-a-2-004 ("satisfiable by a world consistent with `D_n`")
Kind: C
Fidelity: exact
Hyps: (a) `hw`, `hfull`, `hD`, `hφ` -/
theorem pos_iff_satisfiable_pcWorld {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : IsWorldMeasure w D) (hfull : ∀ u ∈ WD D B, 0 < w u) (hD : ∀ ψ ∈ D, atomBound ψ ≤ B)
    {φ : Sentence} (hφ : atomBound φ ≤ B) :
    0 < marginal w φ ↔ ∃ v : PCWorld, v.ConsistentWith D ∧ v.Holds φ :=
  AttemptA.pos_iff_satisfiable_pcWorld hw hfull hD hφ

/-- **T5 at the interior maker**: its day-`n` quote of `φ ∈ S` is positive iff `φ` is satisfiable
together with `D` (over `B` atoms) — the interior maker's prices decide `D`-relative SAT on `S`.
Source: [[bli-coherent-mm-mandate]] T5 (corollary); bli-soto-a-2-004
Kind: C
Fidelity: exact
Hyps: (a) `hD`, `hφ` (atom bounds), `hS`, `hW`, `hε` -/
theorem interior_quote_pos_iff {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (S : Finset Sentence) (hS : mentionedSet T ⊆ S)
    (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D) {ε : ℚ} (hε : 0 < ε)
    (hD : ∀ ψ ∈ D, atomBound ψ ≤ B) {φ : Sentence} (hφS : φ ∈ S) (hφ : atomBound φ ≤ B) :
    0 < (interiorCoherentMarketMaker T past D B S hS hW hε).quote φ ↔
      ∃ v : PCWorld, v.ConsistentWith D ∧ v.Holds φ :=
  AttemptA.interior_quote_pos_iff T past D B S hS hW hε hD hφS hφ

end Cleanroom.Bli.BliCoherentMm

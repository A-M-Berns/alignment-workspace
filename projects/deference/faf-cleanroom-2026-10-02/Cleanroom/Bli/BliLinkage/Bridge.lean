import Cleanroom.Bli.BliLinkage.Defs

/-!
# `bli-linkage` — the bridge from the record definitions to attempt A's

Attempt A's `CellFamily DP` has `cellLit : ℕ → ℕ → ℕ → Sentence` on sentence *codes*; the record
`CellFamilyT DP` (attempt B's) has `literal : ℕ → Sentence → ℕ → Sentence`. `ofB` turns a record
family into an A-family by `cellLit m c r := literal m (sentenceOfCode c) r`. Under it

* `AttemptA.stateOf (ofB C) = stateOf C` by `rfl`;
* `AttemptA.cellMass = cellMass` by `rfl` (the two definitions coincide);
* `c ∈ AttemptA.pinned (ofB C) index n ↔ c ∈ pinned C index n` (a `Finset` versus a `List`;
  the membership conditions are definitionally the same);
* `AttemptA.D_NNUcell (ofB C) index Q ↔ D_NNUcell C index Q`;
* `AttemptA.Degenerate σ S P deg ↔ Degenerate σ P deg` by `Iff.rfl`;
* `AttemptA.PCPσTheory σ S DP P ↔ PCPσTheory (stateAtoms σ S) DP P` by `Iff.rfl`;
* `AttemptA.PCPσ (ofB C) σ S P → PCPσ (stateAtoms σ S) DP P` (forget the partition clause);
* `AttemptA.Tabular (ofB C) index S` gives `ValuesAtRep C S index n` for every `n` and
  `IndexCodes index m` for every `m`.

So every theorem of attempt A restates over the record definitions with no side condition. The
converse direction (an A-family into a record family) would need every code to be genuine and is
not needed. Nothing here is a headline.
-/

namespace Cleanroom.Bli.BliLinkage

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

variable {DP : DeductiveProcess}

/-- **A record family read as an attempt-A family**: the literal of a code is the literal of the
sentence it decodes to; cells, representatives, exclusivity and exhaustiveness carried over.
Source: none: infrastructure (reconciliation)
Kind: D
Fidelity: n/a -/
def ofB (C : CellFamilyT DP) : AttemptA.CellFamily DP where
  cellLit m c r := C.literal m (sentenceOfCode c) r
  cells := C.cells
  rep := C.rep
  excl m c r r' h v hv := C.excl m (sentenceOfCode c) r r' h v hv
  exh m c v hv := C.exh m (sentenceOfCode c) v hv

/-- The state sentences agree definitionally.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem stateOf_ofB (C : CellFamilyT DP) (m q : ℕ) :
    AttemptA.stateOf (ofB C) m q = stateOf C m q := rfl

/-- The two `cellMass` definitions coincide.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cellMass_eq (σ : ℕ → ℕ → Sentence) (S : StateSystem) (P : History) (n c r : ℕ) :
    AttemptA.cellMass σ S P n c r = cellMass σ S P n c r := rfl

/-- The pinned sets agree.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_pinned_ofB (C : CellFamilyT DP) (index : ℕ → List ℕ) (n c : ℕ) :
    c ∈ AttemptA.pinned (ofB C) index n ↔ c ∈ pinned C index n := by
  rw [AttemptA.mem_pinned, mem_pinned]
  exact Iff.rfl

/-- `D_NNUcell` agrees.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem d_nnucell_ofB (C : CellFamilyT DP) (index : ℕ → List ℕ) (Q : History) :
    AttemptA.D_NNUcell (ofB C) index Q ↔ D_NNUcell C index Q := by
  constructor
  · intro h n c hc
    exact h n c ((mem_pinned_ofB C index n c).2 hc)
  · intro h n c hc
    exact h n c ((mem_pinned_ofB C index n c).1 hc)

/-- `Degenerate` agrees (attempt A carries the unused `S`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem degenerate_iff (σ : ℕ → ℕ → Sentence) (S : StateSystem) (P : History) (deg : ℕ → ℕ) :
    AttemptA.Degenerate σ S P deg ↔ Degenerate σ P deg := Iff.rfl

/-- The two completed-theory coherence predicates agree at the record atom set.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pcpσTheory_iff (σ : ℕ → ℕ → Sentence) (S : StateSystem) (P : History) :
    AttemptA.PCPσTheory σ S DP P ↔ PCPσTheory (stateAtoms σ S) DP P := Iff.rfl

/-- Attempt A's partition-respecting coherence implies the record coherence (forget the
partition clause on the mixture worlds).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pcpσ_of_pcpσA (C : CellFamilyT DP) (σ : ℕ → ℕ → Sentence) (S : StateSystem)
    (P : History) (h : AttemptA.PCPσ (ofB C) σ S P) : PCPσ (stateAtoms σ S) DP P := by
  intro n
  obtain ⟨k, W, w, hW, hw, hsum, hrep⟩ := h n
  exact ⟨k, W, w, fun i => (hW i).1, hw, hsum, hrep⟩

/-- `Tabular` gives `ValuesAtRep` on every day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem valuesAtRep_of_tabular (C : CellFamilyT DP) {index : ℕ → List ℕ} {S : StateSystem}
    (hT : AttemptA.Tabular (ofB C) index S) (n : ℕ) : ValuesAtRep C S index n := by
  intro q hq c hc
  obtain ⟨r, hr, he⟩ := hT.keys (n + 1) q hq c hc
  exact ⟨r, hr, he, hT.val (n + 1) q hq c hc r he⟩

/-- `Tabular` gives `IndexCodes` on every day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem indexCodes_of_tabular (C : CellFamilyT DP) {index : ℕ → List ℕ} {S : StateSystem}
    (hT : AttemptA.Tabular (ofB C) index S) (m : ℕ) : IndexCodes index m :=
  hT.genuine m

end Cleanroom.Bli.BliLinkage

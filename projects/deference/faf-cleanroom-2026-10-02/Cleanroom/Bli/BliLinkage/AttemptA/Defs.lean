import Cleanroom.Bli.BliTrajectory.Defs
import Cleanroom.Bli.BliTrajectory.Partition

/-!
# `bli-linkage`, attempt A — definitions of record (cell-literal linkage)

Angle A of the dual package `bli-linkage` (area `bli`, namespace
`Cleanroom.Bli.BliLinkage.AttemptA`): **linkage is propositional**. The B2 state sentence
`stateSentence T round hround m q` (`bli-found` T7) is the conjunction of its cell literals
`cellSentence T round hround m c r` ("`round_m(𝑸_m(⌜c⌝)) = r`"), and the cell literals of one
coordinate are **mutually exclusive and exhaustive** in every completed-theory world
(`cellSentence_reflected`: the literal holds iff the rounded quote *is* `r`, and the rounding is a
total function into the grid). This file abstracts exactly that structure as `CellFamily` and
states the package's definitions of record over it.

## Deviations from the mandate's shapes (said loudly, per [[STANDARDS]])

1. **`cellLit` (the mandate's `lit`) takes a sentence *code*** (`cellLit m c r`, `c : ℕ`), not a `Sentence`: the B2 instance
   is `cellSentence T round hround m c r`, which takes the code, and `stateOf` is then
   *definitionally* `stateSentence` (`stateOf_eq_stateSentence` is `rfl`). With a `Sentence`
   argument the instance would need `cellSentence … (encode (sentenceOfCode c)) …`, which is
   `stateSentence` only up to a genuineness side condition on every table entry. The statements
   that quantify over a coordinate do so by its code `c` and read the sentence as
   `sentenceOfCode c`; `Tabular.genuine` ties the two for index codes.
2. **The coherence worlds of `PCPσ` respect the day-`(n+1)` cell partition**
   (`CellFamily.Partitions`). The stage `DP.D n` of FAF's process does not contain the
   exclusivity/exhaustiveness of the day-`(n+1)` literals (they enter a stage only after the
   day-`(n+1)` prices are computed), yet those are theorems of the theory `T` about a total
   computable rounding, and the sources' "coherent on the algebra of the small sentences and the
   quote atoms" takes the quote atoms to partition. A mixture of bare stage-consistent worlds
   could give a literal mass above the superbelief's marginal (a world holding `σ_q` and *also* a
   second literal of the same coordinate), so the determination theorem would fail for a reason
   that has nothing to do with linkage. `PCPσTheory` (completed-theory worlds) implies `PCPσ`
   (`PCPσ_of_PCPσTheory`), by the family's `excl`/`exh`; K1/K2 are stated at `PCPσ`, K4 at
   `PCPσTheory` (see `Faith.lean` for why both exist).
3. **The state system is tied to the family by `Tabular`**: every candidate of day `m` lists
   every index code with a cell in `C.cells m` (`keys`), and its value at a listed code is the
   representative of its cell (`val`). The B2 system `b2StateSystem` satisfies `val` by
   definition; `keys` is the "tables over `index (n+1)` with entries in `cells (n+1)`" of the
   mandate's K5a. The theorems are false without `keys` (a candidate that does not list the
   coordinate says nothing about its literal, and the marginal is then free) — so it is a
   hypothesis, not a side remark.

Every target quantifies over `pinned C index n` — the day-`(n+1)` index coordinates all of whose
cell literals are small on day `n` — never over a whole table (mandate § Definitions; plan risk
"empty pinned set"; the non-emptiness lemma at B2 is `InstanceB2.lean`'s).

One-way/two-way tag (plan §0.4 rule 1): not applicable — every target is about one base `Q` and
a market `P` computed from it; nothing reads `P` back into `Q`.
-/

namespace Cleanroom.Bli.BliLinkage.AttemptA

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliTrajectory

open Classical

noncomputable section

/-! ## The abstract linkage object -/

/-- **A cell-literal family over a deductive process `DP`** — the abstract linkage object of
record (angle A). `cellLit m c r` is the cell literal (the mandate's `lit`; `lit` is a reserved token in this environment) "`round_m(𝑸_m(⌜c⌝)) = r`" for the day `m`,
the sentence code `c` and the grid index `r`; `cells m` is the day-`m` grid; `rep m r` the
representative of cell `r` (the value a table assigns a coordinate it places in cell `r`).
`excl`/`exh`: in every completed-theory world of `DP`, the literals of one coordinate are
exclusive and exhaustive. B2 instance: `cellLit := cellSentence T round hround`, `excl`/`exh` from
`cellSentence_reflected` and the rounding being total into `cells` (`InstanceB2.lean`).
Source: [[bli-program]] §3.6; mandate § Definitions (`CellFamily`)
Kind: D
Fidelity: variant: `lit` takes the sentence code (module docstring, deviation 1); `DP` is a parameter -/
structure CellFamily (DP : DeductiveProcess) where
  /-- The cell literal of day `m`, coordinate code `c`, grid index `r`. -/
  cellLit : ℕ → ℕ → ℕ → Sentence
  /-- The grid indices of day `m`. -/
  cells : ℕ → Finset ℕ
  /-- The representative value of cell `r` on day `m`. -/
  rep : ℕ → ℕ → ℚ
  /-- Exclusivity in every completed-theory world. -/
  excl : ∀ m c r r', r ≠ r' → ∀ v : PCWorld, v.ConsistentWithTheory DP →
    ¬ (v.Holds (cellLit m c r) ∧ v.Holds (cellLit m c r'))
  /-- Exhaustiveness in every completed-theory world. -/
  exh : ∀ m c, ∀ v : PCWorld, v.ConsistentWithTheory DP → ∃ r ∈ cells m, v.Holds (cellLit m c r)

variable {DP : DeductiveProcess}

/-- **The linked state sentence** over an abstract family: the conjunction of the family's
literals over the entries of the table with code `q`. At B2 it is definitionally
`stateSentence` (`InstanceB2.stateOf_eq_stateSentence`, `rfl`). Linkage is propositional:
`stateOf → lit` is a conjunct (`holds_lit_of_holds_stateOf`).
Source: mandate § Definitions (`stateOf`); bli-paper-032/038
Kind: D
Fidelity: exact -/
def stateOf (C : CellFamily DP) (m q : ℕ) : Sentence :=
  conjList ((tableOfCode q).map fun e => C.cellLit m e.1 e.2)

/-- A world holds the linked state sentence iff it holds every entry's literal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_stateOf (C : CellFamily DP) (m q : ℕ) (v : PCWorld) :
    v.Holds (stateOf C m q) ↔ ∀ e ∈ tableOfCode q, v.Holds (C.cellLit m e.1 e.2) := by
  unfold stateOf
  rw [holds_conjList]
  constructor
  · intro h e he
    exact h _ (List.mem_map.2 ⟨e, he, rfl⟩)
  · intro h ψ hψ
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hψ
    exact h e he

/-- **Linkage is a conjunct**: a world holding the state sentence holds the literal of every
listed coordinate at the state's own index.
Source: mandate § Definitions ("`stateOf → lit` is a conjunct")
Kind: L
Fidelity: n/a -/
lemma holds_lit_of_holds_stateOf {C : CellFamily DP} {m q c r : ℕ} {v : PCWorld}
    (hv : v.Holds (stateOf C m q)) (he : entryOf c (tableOfCode q) = some r) :
    v.Holds (C.cellLit m c r) :=
  (holds_stateOf C m q v).1 hv (c, r) (mem_of_entryOf_eq_some he)

/-- The atoms of the state sentence are the atoms of its literals.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sentenceAtomCodes_conjList : ∀ l : List Sentence,
    sentenceAtomCodes (conjList l) = l.foldr (fun φ s => sentenceAtomCodes φ ∪ s) ∅
  | [] => by simp [conjList]
  | φ :: l => by rw [conjList, sentenceAtomCodes_and, sentenceAtomCodes_conjList l]; rfl

/-- An atom of a conjunct is an atom of the conjunction, and conversely every atom of the
conjunction is an atom of some conjunct.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_sentenceAtomCodes_conjList {a : ℕ} : ∀ {l : List Sentence},
    a ∈ sentenceAtomCodes (conjList l) ↔ ∃ φ ∈ l, a ∈ sentenceAtomCodes φ
  | [] => by simp [conjList]
  | φ :: l => by
      rw [conjList, sentenceAtomCodes_and, Finset.mem_union, mem_sentenceAtomCodes_conjList]
      simp

/-! ## Worlds that respect the cell partition -/

/-- **`v` respects the day-`m` cell partition**: on every coordinate code, exactly one of the
family's day-`m` literals holds, with its index in `cells m`. Every completed-theory world does
(`CellFamily.partitions_of_consistentWithTheory`); `PCPσ`'s mixture worlds are required to
(module docstring, deviation 2).
Source: [[bli-program]] §3.6 (the quote atoms partition); mandate § Definitions (`PCPσ`)
Kind: D
Fidelity: exact -/
def CellFamily.Partitions (C : CellFamily DP) (m : ℕ) (v : PCWorld) : Prop :=
  ∀ c, (∃ r ∈ C.cells m, v.Holds (C.cellLit m c r)) ∧
    ∀ r r', r ≠ r' → ¬ (v.Holds (C.cellLit m c r) ∧ v.Holds (C.cellLit m c r'))

/-- Completed-theory worlds respect every day's partition (the family's `excl`/`exh`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma CellFamily.partitions_of_consistentWithTheory (C : CellFamily DP) (m : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory DP) : C.Partitions m v :=
  fun c => ⟨C.exh m c v hv, fun r r' hne => C.excl m c r r' hne v hv⟩

/-- In a partition-respecting world, a held state sentence decides every listed coordinate's
literal: `lit m c r` holds iff `r` is the table's entry at `c`.
Source: none: infrastructure (the one-step content of "linkage is propositional")
Kind: L
Fidelity: n/a -/
lemma holds_lit_iff_of_partitions {C : CellFamily DP} {m q c r r₀ : ℕ} {v : PCWorld}
    (hpart : C.Partitions m v) (hv : v.Holds (stateOf C m q))
    (he : entryOf c (tableOfCode q) = some r₀) :
    v.Holds (C.cellLit m c r) ↔ r = r₀ := by
  have h0 := holds_lit_of_holds_stateOf hv he
  constructor
  · intro hr
    by_contra hne
    exact (hpart c).2 r r₀ hne ⟨hr, h0⟩
  · rintro rfl; exact h0

/-! ## Coherence, σ-parametric -/

/-- **Coherence on a finite Boolean algebra, relative to a stage and the day-`m` cell
partition**: `p` is a convex combination of the payouts of finitely many `PCWorld`s that are
consistent with the stage `D` *and* respect the day-`m` cell partition, on every sentence whose
atoms lie in `A`. This is `bli-found`'s `CoherentOn D A p` with the partition clause added
(module docstring, deviation 2).
Source: bli-slides-003/011; [[bli-program]] §2.6, §3.6; mandate § Definitions (`PCPσ`)
Kind: D
Fidelity: variant: the mixture worlds respect the day-`m` cell partition -/
def CoherentOnCell (C : CellFamily DP) (D : Finset Sentence) (m : ℕ) (A : Finset ℕ)
    (p : Sentence → ℝ) : Prop :=
  ∃ (k : ℕ) (W : Fin k → PCWorld) (w : Fin k → ℝ),
    (∀ i, (W i).ConsistentWith D ∧ C.Partitions m (W i)) ∧ (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
    ∀ φ, sentenceAtomCodes φ ⊆ A → p φ = ∑ i, w i * (W i).payout φ

/-- **Coherence relative to the completed theory**: as `CoherentOn`, with the mixture worlds
consistent with every stage of `DP`.
Source: mandate § Definitions (`CoherentOnTheory`)
Kind: D
Fidelity: exact -/
def CoherentOnTheory (DP : DeductiveProcess) (A : Finset ℕ) (p : Sentence → ℝ) : Prop :=
  ∃ (k : ℕ) (W : Fin k → PCWorld) (w : Fin k → ℝ),
    (∀ i, (W i).ConsistentWithTheory DP) ∧ (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
    ∀ φ, sentenceAtomCodes φ ⊆ A → p φ = ∑ i, w i * (W i).payout φ

/-- The atoms of the day-`n` small sentences.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def smallAtoms (n : ℕ) : Finset ℕ := (smallSet n).biUnion sentenceAtomCodes

/-- The atoms of the day-`(n+1)` state sentences `σ (n+1) q`, `q ∈ S.states (n+1)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def stateAtomsσ (σ : ℕ → ℕ → Sentence) (S : StateSystem) (n : ℕ) : Finset ℕ :=
  (S.states (n + 1)).biUnion fun q => sentenceAtomCodes (σ (n + 1) q)

/-- The day-`n` coherence algebra's atoms: the small sentences' and the day-`(n+1)` states'.
A pinned coordinate's literals are small on day `n`, so their atoms are already in
`smallAtoms n` — that is the point of `pinned`, not a nuisance (mandate § K1).
Source: mandate § Definitions (`PCPσ`: "`atoms n` ⊇ the atom codes of `σ (n+1) q`")
Kind: D
Fidelity: exact -/
def pcpAtomsσ (σ : ℕ → ℕ → Sentence) (S : StateSystem) (n : ℕ) : Finset ℕ :=
  smallAtoms n ∪ stateAtomsσ σ S n

/-- **`PCPσ` — σ-parametric coherence of `P`, stage form**: on every day `n`, `P n` is a
mixture of worlds consistent with the stage `DP.D n` and respecting the day-`(n+1)` cell
partition, on the algebra generated by the day-`n` small sentences and the day-`(n+1)` state
sentences `σ (n+1) q`. The σ-parametric coherence `bli-found` F-17 left to this package.
Source: [[bli-program]] §2.6, §3.6; mandate § Definitions (`PCPσ`); bli-found F-17
Kind: D
Fidelity: variant: partition-respecting stage worlds (module docstring, deviation 2) -/
def PCPσ (C : CellFamily DP) (σ : ℕ → ℕ → Sentence) (S : StateSystem) (P : History) : Prop :=
  ∀ n, CoherentOnCell C (DP.D n) (n + 1) (pcpAtomsσ σ S n) (P n)

/-- **`PCPσTheory` — σ-parametric coherence of `P`, completed-theory form**: as `PCPσ`, with
worlds consistent with the whole of `DP`. Stronger than `PCPσ` (`PCPσ_of_PCPσTheory`); under
linkage it is *very* strong — in a completed-theory world exactly the actual next table holds
(`bli-found`'s `fixedStates_decided` at B2), so with `E5σ` the superbelief is a point mass on the
realized state (`Forced.theory_coherent_point_mass`). K4 needs it (the liar's biconditional with
its cell literal is a fact of the completed theory, not of the stage); K1/K2 do not.
Source: mandate § Definitions (`PCPσTheory`)
Kind: D
Fidelity: exact -/
def PCPσTheory (σ : ℕ → ℕ → Sentence) (S : StateSystem) (DP : DeductiveProcess) (P : History) :
    Prop :=
  ∀ n, CoherentOnTheory DP (pcpAtomsσ σ S n) (P n)

/-- `PCPσTheory → PCPσ`: a completed-theory world is consistent with every stage and respects
every day's partition.
Source: mandate § Definitions ("Prove `PCPσTheory → PCPσ` (L)")
Kind: L
Fidelity: n/a -/
theorem PCPσ_of_PCPσTheory (C : CellFamily DP) (σ : ℕ → ℕ → Sentence) (S : StateSystem)
    (P : History) (h : PCPσTheory σ S DP P) : PCPσ C σ S P := by
  intro n
  obtain ⟨k, W, w, hW, hw, hsum, hrep⟩ := h n
  exact ⟨k, W, w, fun i => ⟨hW i n, C.partitions_of_consistentWithTheory _ _ (hW i)⟩, hw, hsum,
    hrep⟩

/-! ## The pinned set, the marginal, the exact no-net-update, the degenerate superbelief -/

/-- **The pinned set of record**: the day-`(n+1)` index coordinates all of whose cell literals
are small on day `n` — the coordinates on which the day-`n` market prices tomorrow's cell. The
theorems quantify over it, never over a whole table.
Source: mandate § Definitions (`pinned`); [[bli-program-desiderata]] §10 item 10
Kind: D
Fidelity: exact -/
def pinned (C : CellFamily DP) (index : ℕ → List ℕ) (n : ℕ) : Finset ℕ :=
  (index (n + 1)).toFinset.filter fun c => ∀ r ∈ C.cells (n + 1), SmallOn n (C.cellLit (n + 1) c r)

/-- `mem_pinned`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_pinned {C : CellFamily DP} {index : ℕ → List ℕ} {n c : ℕ} :
    c ∈ pinned C index n ↔
      c ∈ index (n + 1) ∧ ∀ r ∈ C.cells (n + 1), SmallOn n (C.cellLit (n + 1) c r) := by
  simp [pinned]

/-- A pinned coordinate's literals are day-`n` small sentences.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lit_mem_smallSet_of_mem_pinned {C : CellFamily DP} {index : ℕ → List ℕ} {n c r : ℕ}
    (hc : c ∈ pinned C index n) (hr : r ∈ C.cells (n + 1)) :
    C.cellLit (n + 1) c r ∈ smallSet n :=
  mem_smallSet.mpr ((mem_pinned.1 hc).2 r hr)

/-- A small sentence's atoms lie in `smallAtoms n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma atoms_subset_smallAtoms {n : ℕ} {φ : Sentence} (h : φ ∈ smallSet n) :
    sentenceAtomCodes φ ⊆ smallAtoms n :=
  Finset.subset_biUnion_of_mem sentenceAtomCodes h

/-- A day-`(n+1)` state sentence's atoms lie in `stateAtomsσ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma atoms_subset_stateAtomsσ {σ : ℕ → ℕ → Sentence} {S : StateSystem} {n q : ℕ}
    (hq : q ∈ S.states (n + 1)) : sentenceAtomCodes (σ (n + 1) q) ⊆ stateAtomsσ σ S n :=
  Finset.subset_biUnion_of_mem (fun q => sentenceAtomCodes (σ (n + 1) q)) hq

/-- **The superbelief's marginal on coordinate `c`, cell `r`**: the day-`n` mass of the
day-`(n+1)` states whose table places `c` in cell `r`.
Source: mandate § Definitions (`cellMass`); [[bli-program]] §3.6(i)
Kind: D
Fidelity: exact -/
def cellMass (σ : ℕ → ℕ → Sentence) (S : StateSystem) (P : History) (n c r : ℕ) : ℝ :=
  ∑ q ∈ (S.states (n + 1)).filter (fun q => entryOf c (tableOfCode q) = some r),
    P n (σ (n + 1) q)

/-- **`D_NNUcell` — exact, finite-time no-net-expected-update, cell form**: on every pinned
coordinate the base's price today is the representative-weighted sum of its prices of
tomorrow's cell literals. The definition of record of this package for the program's
`D-NNU(Q)`; `bli-found`'s interval `D_NNU` has interval quotes and midpoints where this has cell
literals and representatives, and a slack `ε` where this has none.
Source: [[bli-program]] §3.6(ii); desiderata I6; mandate § Definitions (`D_NNUcell`)
Kind: D
Fidelity: variant: cell literals and representatives in place of interval quotes and midpoints -/
def D_NNUcell (C : CellFamily DP) (index : ℕ → List ℕ) (Q : History) : Prop :=
  ∀ n, ∀ c ∈ pinned C index n,
    Q n (sentenceOfCode c) = ∑ r ∈ C.cells (n + 1), (C.rep (n + 1) r : ℝ) * Q n (C.cellLit (n + 1) c r)

/-- **The degenerate (point-mass) superbelief, σ-parametric**: all of day `n`'s mass on the
state `deg n` (at B2: the table copying today's rounded entries). `bli-trajectory`'s `b0History`
is its B1 instance.
Source: mandate § Definitions (`Degenerate`); bli-paper-043; [[bli-program]] §3.6(iii)
Kind: D
Fidelity: exact -/
def Degenerate (σ : ℕ → ℕ → Sentence) (_S : StateSystem) (P : History) (deg : ℕ → ℕ) : Prop :=
  ∀ n, P n (σ (n + 1) (deg n)) = 1

/-- **`E2xσIdx` — exact faith on the written-out coordinates**: `bli-found`'s `E2xσ` restricted
to the sentences the day-`m` index lists (`φ = sentenceOfCode c`, `c ∈ index m`), still within
faith's scope `Sminus m m`. `E2xσ → E2xσIdx` (`e2xσIdx_of_e2xσ`). **Why it exists**: over a
list-table system whose value off the index is a junk `0` (`b2StateSystem`), the full `E2xσ`
is unsatisfiable by any coherent `P` with a charged state as soon as the scope contains an
unlisted tautology (`⊤ ⋏ ⊤ ∈ Sminus m m` from `m = 2`): faith demands
`P n (⊤ ⋏ ⊤ ⋏ σ_q) = 0 · P n σ_q = 0` while coherence gives `P n σ_q` — `B2.e2xσ_unsat_of_unlisted_tautology`, `B2.fixedSystem01_e2xσ_unsat`.
K2 reads faith only at the pinned coordinate, so it is stated at this predicate (weaker
hypothesis, stronger theorem), with the full-`E2xσ` form as a corollary.
Source: mandate § K2 (b) ("`E2xσ` at `(n, n+1, q, φ)`"); bli-found F-2/F-12 (the junk-value problem)
Kind: D
Fidelity: weaker: faith only on the listed coordinates (the sentences the written-out state prices) -/
def E2xσIdx (σ : ℕ → ℕ → Sentence) (index : ℕ → List ℕ) (S : StateSystem) (P : History) :
    Prop :=
  ∀ n m, n < m → ∀ q ∈ S.states m, ∀ c ∈ index m, sentenceOfCode c ∈ Sminus m m →
    P n (sentenceOfCode c ⋏ σ m q) = S.val m q (sentenceOfCode c) * P n (σ m q)

/-- `E2xσ → E2xσIdx`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem e2xσIdx_of_e2xσ {σ : ℕ → ℕ → Sentence} (index : ℕ → List ℕ) {S : StateSystem}
    {P : History} (h : E2xσ σ S P) : E2xσIdx σ index S P :=
  fun n m hnm q hq _ _ hc => h n m hnm q hq _ hc

/-- **`Tabular C index S` — the state system is a system of tables over `index` with cells in
`C.cells` and the representatives as values**: every candidate of day `m` lists every index
code of day `m` with an index in `C.cells m` (`keys`); its value at a listed index code is the
representative of the listed cell (`val`); and the index codes are genuine sentence codes
(`genuine`). `b2StateSystem` satisfies `val` by definition and `genuine` for any list of
`Encodable.encode`s; `keys` is the "tables over `index (n+1)`" of mandate K5a and is a genuine
hypothesis (module docstring, deviation 3).
Source: mandate § K2 (`hval`), § K5a ("tables over `index (n+1)` with entries in `cells (n+1)`")
Kind: D
Fidelity: exact -/
structure Tabular (C : CellFamily DP) (index : ℕ → List ℕ) (S : StateSystem) : Prop where
  /-- Every candidate lists every index code with a legitimate cell. -/
  keys : ∀ m, ∀ q ∈ S.states m, ∀ c ∈ index m, ∃ r ∈ C.cells m, entryOf c (tableOfCode q) = some r
  /-- The value at a listed index code is the representative of its cell. -/
  val : ∀ m, ∀ q ∈ S.states m, ∀ c ∈ index m, ∀ r, entryOf c (tableOfCode q) = some r →
    S.val m q (sentenceOfCode c) = C.rep m r
  /-- The index codes are genuine sentence codes. -/
  genuine : ∀ m, ∀ c ∈ index m, Encodable.encode (sentenceOfCode c) = c

end

end Cleanroom.Bli.BliLinkage.AttemptA

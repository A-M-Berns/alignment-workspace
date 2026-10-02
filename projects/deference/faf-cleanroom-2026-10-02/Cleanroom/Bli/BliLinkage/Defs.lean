import Cleanroom.Bli.BliLinkageB.Defs
import Cleanroom.Bli.BliLinkage.AttemptA.Defs

/-!
# `bli-linkage` — definitions of record (reconciled package)

The dual package `bli-linkage` was attacked by two formalizers: **attempt A**
(`Cleanroom/Bli/BliLinkage/AttemptA/`, exact cell-literal linkage with partition-respecting
coherence worlds, `cellLit` taking the sentence *code*) and **attempt B**
(`Cleanroom/Bli/BliLinkageB/`, interval linkage with overlapping cells, plain stage coherence,
`literal` taking the *sentence*, the grid condition `SpuriousEntails`). This module fixes the
**definitions of record** of the reconciled package and says why.

## The decision

The definitions of record are **attempt B's** (`Cleanroom.Bli.BliLinkageB.Defs`), re-exported
here under the package namespace `Cleanroom.Bli.BliLinkage`:

* `CellFamily 𝒲` (`literal : ℕ → Sentence → ℕ → Sentence`, the mandate's type for `lit`;
  the world class `𝒲` a parameter, `CellFamilyT DP` the mandate's completed-theory form),
  `stateOf`, `pinned` (a `List ℕ`, the mandate's `(index (n+1)).filter`), `cellMass`,
  `D_NNUcell` (identical in both attempts), `Degenerate` (the mandate's unused `S` dropped),
  `IndexCodes`, `SpuriousEntails`, `ValuesAtRep`;
* the coherence predicates `CoherentOnW`, `CoherentOnTheory`, `smallAtoms`, `stateAtoms`,
  `PCPσ atoms DP P` (**plain** `bli-found` `CoherentOn (DP.D n)` on `smallAtoms n ∪ atoms n` —
  exactly the mandate's `PCPσ`, with the extra atom set a parameter) and `PCPσTheory`;
* the interval-side objects `IntervalSem`, `IntervalFamily`, `LinkedWorld`, `pinnedI`.

Three reasons. (i) **Fidelity to the mandate and to FAF**: B's `PCPσ` is `bli-found`'s
`CoherentOn` unchanged; A's `PCPσ` adds a partition clause to the mixture worlds
(`CoherentOnCell`), a disclosed variant that the determination theorem does not need once the
grid is closed under single-entry changes (`SpuriousEntails`, a condition on *instance data*,
discharged for `Grid.fixedStates` and for every full product grid). (ii) **The conversion is
definitional in one direction only**: from a B-family one obtains an A-family by
`cellLit m c r := literal m (sentenceOfCode c) r` (`Bridge.ofB`), under which `stateOf`,
`cellMass`, `D_NNUcell` and `Degenerate` agree by `rfl` or by membership, so every theorem of
attempt A transports to the record definitions for free; the other direction needs genuineness
of every code (`IndexCodes`), so choosing A's definitions would have put a side condition under
every theorem of attempt B. (iii) **Where the content is**: K3's conclusion of record (the
price-reading trader at FAF's LIA), K5a/b, the dissolution witness and the trilemma's horns are
attempt B's, already over these definitions.

What the record takes from **attempt A**: the faith predicate `E2xσIdx` (faith on the
written-out coordinates only), because `bli-found`'s full `E2xσ` is unsatisfiable over every
list-table B2 system under coherence with a charged state (A's F-A1, `⊤ ⋏ ⊤ ∈ Sminus 2 2` is
unlisted and valued at the junk `0`; re-proved over the record coherence in
`InstanceB2.e2xσ_unsat_of_unlisted_tautology`). The determination theorem of record
(`Determination.determination`) is therefore stated over `E2xσIdx`, with the `E2xσ` form a
corollary — a strictly stronger theorem than either attempt's.

What the record loses from A, disclosed: `stateOf = stateSentence` is `rfl` for A's code-taking
`cellLit` and is an equation on tables listing genuine codes for the record's sentence-taking
`literal` (`BliLinkageB.InstanceB2.stateOf_cellFamilyB2_eq`); the mandate asked for `rfl` *and*
for the sentence-taking type, which cannot both hold, since `cellSentence` takes a code.

Nothing here is a headline: every declaration is `D` or `L`. The one-way/two-way tag
(plan §0.4 rule 1) is not applicable to this package — every target is about one base `Q` and
a market `P` computed from it.
-/

namespace Cleanroom.Bli.BliLinkage

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

export Cleanroom.Bli.BliLinkageB (CoherentOnW coherentOn_iff_coherentOnW CoherentOnTheory
  smallAtoms stateAtoms atoms_subset_smallAtoms atoms_subset_stateAtoms PCPσ PCPσTheory
  IntervalSem IntervalFamily LinkedWorld lnkcell_iff_linkedWorld CellFamily CellFamilyT stateOf
  holds_stateOf holds_lit_of_holds_stateOf pinned mem_pinned cellMass IndexCodes D_NNUcell
  Degenerate pinnedI mem_pinnedI SpuriousEntails ValuesAtRep)

export Cleanroom.Bli.BliLinkage.AttemptA (E2xσIdx e2xσIdx_of_e2xσ)

/-- **The σ-parametric coherence of the mandate's shape**, `PCPσ` at the atom set the
mandate names: the day-`n` small sentences and the day-`(n+1)` state sentences of the
candidates. The theorems take the atom set as a parameter `atoms` with
`stateAtoms σ S n ⊆ atoms n` (attempt B's shape), of which this is the least instance.
Source: mandate § Definitions (`PCPσ`: "`atoms n` ⊇ the atom codes of `σ (n+1) q`")
Kind: D
Fidelity: exact -/
abbrev PCPσState (σ : ℕ → ℕ → Sentence) (S : StateSystem) (DP : DeductiveProcess)
    (P : History) : Prop :=
  PCPσ (stateAtoms σ S) DP P

/-- `PCPσTheory` at the mandate's atom set.
Source: mandate § Definitions (`PCPσTheory`)
Kind: D
Fidelity: exact -/
abbrev PCPσTheoryState (σ : ℕ → ℕ → Sentence) (S : StateSystem) (DP : DeductiveProcess)
    (P : History) : Prop :=
  PCPσTheory (stateAtoms σ S) DP P

/-- `PCPσTheory → PCPσ` (the mandate's `L`), at the record atom set.
Source: mandate § Definitions ("Prove `PCPσTheory → PCPσ` (L)")
Kind: L
Fidelity: n/a -/
theorem PCPσState_of_PCPσTheoryState {σ : ℕ → ℕ → Sentence} {S : StateSystem}
    {DP : DeductiveProcess} {P : History} (h : PCPσTheoryState σ S DP P) : PCPσState σ S DP P :=
  Cleanroom.Bli.BliLinkageB.PCPσTheory.toPCPσ h

end Cleanroom.Bli.BliLinkage

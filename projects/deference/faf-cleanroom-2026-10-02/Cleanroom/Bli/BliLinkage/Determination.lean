import Cleanroom.Bli.BliLinkage.Bridge
import Cleanroom.Bli.BliLinkageB.Determination
import Cleanroom.Bli.BliLinkage.AttemptA.Determination
import Cleanroom.Bli.BliLinkage.AttemptA.Trilemma

/-!
# `bli-linkage` — K1 (constraint 4′ forced) and K2 (the determination theorem), of record

Over the record definitions (`Defs.lean`: attempt B's) and the faith predicate `E2xσIdx`
(attempt A's). The two attempts proved K1/K2 by two different routes:

* **attempt B** (`BliLinkageB.Determination.determination_stage`, `d_nnucell_of_package`): plain
  stage coherence `PCPσ` plus the grid condition `SpuriousEntails` (a candidate together with a
  cell literal it does not list entails another candidate); faith as `bli-found`'s full `E2xσ`;
* **attempt A** (`AttemptA.Forced.forced_marginal`, `AttemptA.Determination.determination`):
  coherence over *partition-respecting* mixture worlds (`CoherentOnCell`) plus `Tabular`; faith
  as `E2xσIdx`.

The **theorem of record** takes B's route (the mandate's `PCPσ`, the grid condition on instance
data) with A's faith predicate (`E2xσIdx`, strictly weaker than `E2xσ` and the only one a
list-table B2 system can satisfy — `InstanceB2.e2xσ_unsat_of_unlisted_tautology`), so it has
strictly weaker hypotheses than B's `d_nnucell_of_package` and is **incomparable** with A's
(A's needs no `SpuriousEntails`; findings FR-5 — "stronger than either" was round 0's
overstatement, audit r1 fidelity N4). It is proved here from a **per-day engine**
(`forced_marginal_day`, `balance_day_idx`, `nnu_day`) that takes coherence and partition on the
one day in question — which is also what A's `no_T2_over_coherent_base` needs to transport,
giving the record form of this run's strengthening of the trilemma (the coherence horn is the
*base's*). A's partition-respecting variant is restated through the bridge as
`determination_partition`.

Both attempts' K1/K2 are **grade (a)**: no FAF theorem is assumed; `SpuriousEntails`,
`ValuesAtRep` and the scope condition `hscope` are conditions on the index and grid, discharged
at B2 in `InstanceB2.lean`. The only inherited `(c)` is `bli-found` F-14's `Sminus`
under-approximation of the prose scope, carried by the faith predicate.
-/

namespace Cleanroom.Bli.BliLinkage

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound
open Cleanroom.Bli.BliLinkageB (IsMixture PartitionAt coherentOnW_iff partitionAt_of_E5σ)

section Day

variable {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) {S : StateSystem} {atoms : ℕ → Finset ℕ}
variable {DP : DeductiveProcess} {P Q : History} {index : ℕ → List ℕ}

/-- **K1 on one day (the partition engine, attempt B's route).** If `P n` is a mixture of worlds
consistent with the stage `DP.D n` on the algebra of the day-`n` small sentences and the extra
atoms (containing the day-`(n+1)` state atoms), `P n` partitions the day-`(n+1)` candidates, and
the grid has `SpuriousEntails`, then on every pinned coordinate `c` and cell `r`,
`P n (lit_{n+1,c,r}) = cellMass_r`. No linkage hypothesis, no interval semantics, no fact about
what the stage has decided: a charged world holds exactly one candidate; that candidate's
literal at `c` is a conjunct; a second literal at `c` would, with the candidate, entail a second
candidate, against exclusivity.
Source: [[bli-program]] §3.6(i); bli-slides-010/011; mandate K1; attempt B `determination_stage`
Kind: P
Fidelity: exact (stage level, grids with `SpuriousEntails`)
Hyps: (a); `SpuriousEntails` is a grid condition discharged by the instance -/
theorem forced_marginal_day {n : ℕ}
    (hcoh : CoherentOn (DP.D n) (smallAtoms n ∪ atoms n) (P n))
    (hatoms : stateAtoms (stateOf C) S n ⊆ atoms n)
    (hpart : PartitionAt (stateOf C) S (P n) (n + 1))
    (hsp : SpuriousEntails (stateOf C) C.literal S index C.cells n) {c : ℕ}
    (hc : c ∈ pinned C index n) {r : ℕ} (hr : r ∈ C.cells (n + 1)) :
    P n (C.literal (n + 1) (sentenceOfCode c) r) = cellMass (stateOf C) S P n c r := by
  obtain ⟨k, W, w, -, hM⟩ :=
    (coherentOnW_iff _ _ _).1 ((coherentOn_iff_coherentOnW _ _ _).1 hcoh)
  have hσA : ∀ q ∈ S.states (n + 1),
      sentenceAtomCodes (stateOf C (n + 1) q) ⊆ smallAtoms n ∪ atoms n := fun q hq =>
    (atoms_subset_stateAtoms (stateOf C) S hq).trans (hatoms.trans Finset.subset_union_right)
  have hlitA : sentenceAtomCodes (C.literal (n + 1) (sentenceOfCode c) r) ⊆
      smallAtoms n ∪ atoms n :=
    (atoms_subset_smallAtoms (by rw [mem_smallSet]; exact ((mem_pinned C index n c).1 hc).2 r hr)).trans
      Finset.subset_union_left
  have hcidx : c ∈ index (n + 1) := ((mem_pinned C index n c).1 hc).1
  rw [hM.sum_and_state hσA hpart hlitA, cellMass, Finset.sum_filter]
  refine Finset.sum_congr rfl fun q hq => ?_
  by_cases he : entryOf c (tableOfCode q) = some r
  · rw [if_pos he]
    exact hM.and_state_eq_of_forced (hσA q hq) hlitA fun i _ hs =>
      holds_lit_of_holds_stateOf C hs he
  · rw [if_neg he]
    refine hM.and_state_eq_zero_of_excluded (hσA q hq) hlitA fun i hi hs hl => ?_
    obtain ⟨q', hq', hne, hent⟩ := hsp q hq c hcidx r hr he
    exact hM.charged_not_both hσA hpart hi hq' hq hne ⟨hent (W i) hs hl, hs⟩

/-- **Balance on the base, one day (K2 (b))**: with faith at `φ` on every candidate and small
agreement, `Q n φ = ∑_q val_q(φ) · P n σ_q` — the law of total probability over the partition
inside the mixture, read through `E1x`. Stated for any state family `σ`; the scope of faith
enters only when `hfaith` is derived from `E2xσIdx` (needs `φ ∈ Sminus (n+1) (n+1)` and `φ`
listed).
Source: mandate K2 (b); bli-found F-11; attempt B `balance_day`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem balance_day_idx {σ : ℕ → ℕ → Sentence} {n : ℕ}
    (hcoh : CoherentOn (DP.D n) (smallAtoms n ∪ atoms n) (P n))
    (hatoms : stateAtoms σ S n ⊆ atoms n) (hpart : PartitionAt σ S (P n) (n + 1))
    (hE1 : E1x Q P) {φ : Sentence}
    (hfaith : ∀ q ∈ S.states (n + 1),
      P n (φ ⋏ σ (n + 1) q) = S.val (n + 1) q φ * P n (σ (n + 1) q))
    (hφn : φ ∈ smallSet n) :
    Q n φ = ∑ q ∈ S.states (n + 1), S.val (n + 1) q φ * P n (σ (n + 1) q) := by
  obtain ⟨k, W, w, -, hM⟩ :=
    (coherentOnW_iff _ _ _).1 ((coherentOn_iff_coherentOnW _ _ _).1 hcoh)
  rw [← hE1 n _ hφn]
  exact hM.balance_of_faith (fun q hq =>
      (atoms_subset_stateAtoms σ S hq).trans (hatoms.trans Finset.subset_union_right)) hpart
    ((atoms_subset_smallAtoms hφn).trans Finset.subset_union_left) hfaith

/-- **The no-net-update identity on one day (K2 (c))**: with coherence and partition on day
`n`, small agreement, faith at the pinned coordinate `c` on every candidate, `SpuriousEntails`
and `ValuesAtRep`: `Q n φ_c = ∑_r rep_r · Q n (lit_{n+1,c,r})`. Route: balance by faith,
regrouped by cells (`sum_val_eq_sum_rep_cellMass`), each cell mass the literal's price (K1).
Source: [[bli-program]] §3.6(ii); desiderata I6; mandate K2 (c)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem nnu_day {n : ℕ}
    (hcoh : CoherentOn (DP.D n) (smallAtoms n ∪ atoms n) (P n))
    (hatoms : stateAtoms (stateOf C) S n ⊆ atoms n)
    (hpart : PartitionAt (stateOf C) S (P n) (n + 1)) (hE1 : E1x Q P)
    (hsp : SpuriousEntails (stateOf C) C.literal S index C.cells n)
    (hval : ValuesAtRep C S index n) {c : ℕ} (hc : c ∈ pinned C index n)
    (hfaith : ∀ q ∈ S.states (n + 1),
      P n (sentenceOfCode c ⋏ stateOf C (n + 1) q) =
        S.val (n + 1) q (sentenceOfCode c) * P n (stateOf C (n + 1) q))
    (hφn : sentenceOfCode c ∈ smallSet n) :
    Q n (sentenceOfCode c) =
      ∑ r ∈ C.cells (n + 1), (C.rep (n + 1) r : ℝ) * Q n (C.literal (n + 1) (sentenceOfCode c) r) := by
  have hcidx : c ∈ index (n + 1) := ((mem_pinned C index n c).1 hc).1
  rw [balance_day_idx hcoh hatoms hpart hE1 hfaith hφn,
    Cleanroom.Bli.BliLinkageB.sum_val_eq_sum_rep_cellMass C (stateOf C) S P n hval hcidx]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [← hE1 n _ (by rw [mem_smallSet]; exact ((mem_pinned C index n c).1 hc).2 r hr),
    forced_marginal_day C hcoh hatoms hpart hsp hc hr]

end Day

section Record

variable {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) {S : StateSystem} {atoms : ℕ → Finset ℕ}
variable {DP : DeductiveProcess} {P Q : History} {index : ℕ → List ℕ}

/-- **K1 — constraint 4′ is forced by coherence with the quote atoms (of record).** Under
`PCPσ ∧ E5σ` at `σ := stateOf C` over a grid with `SpuriousEntails`, for every day `n`, pinned
coordinate `c` and cell `r`: `P n (lit_{n+1,c,r}) = cellMass (stateOf C) S P n c r`.
Source: [[bli-program]] §3.6(i); desiderata P5e; bli-slides-010/011; bli-soto-a-007; mandate K1
Kind: C
Fidelity: exact (stage level; grids with `SpuriousEntails`)
Hyps: (a) -/
theorem forced_marginal (hcoh : PCPσ atoms DP P)
    (hatoms : ∀ n, stateAtoms (stateOf C) S n ⊆ atoms n) (hE5 : E5σ (stateOf C) S P) (n : ℕ)
    (hsp : SpuriousEntails (stateOf C) C.literal S index C.cells n) {c : ℕ}
    (hc : c ∈ pinned C index n) {r : ℕ} (hr : r ∈ C.cells (n + 1)) :
    P n (C.literal (n + 1) (sentenceOfCode c) r) = cellMass (stateOf C) S P n c r :=
  forced_marginal_day C (hcoh n) (hatoms n) (partitionAt_of_E5σ hE5 n) hsp hc hr

/-- **K1 on the base**: with `E1x`, the base's day-`n` belief about tomorrow's cell is the
superbelief's marginal — constraint 4′ of bli-slides-011 as a consequence, not a desideratum.
Source: bli-slides-011 (4′); [[bli-program]] §3.6(i); mandate K1
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem forced_marginal_base (hcoh : PCPσ atoms DP P)
    (hatoms : ∀ n, stateAtoms (stateOf C) S n ⊆ atoms n) (hE5 : E5σ (stateOf C) S P)
    (hE1 : E1x Q P) (n : ℕ) (hsp : SpuriousEntails (stateOf C) C.literal S index C.cells n)
    {c : ℕ} (hc : c ∈ pinned C index n) {r : ℕ} (hr : r ∈ C.cells (n + 1)) :
    Q n (C.literal (n + 1) (sentenceOfCode c) r) = cellMass (stateOf C) S P n c r := by
  rw [← hE1 n _ (by rw [mem_smallSet]; exact ((mem_pinned C index n c).1 hc).2 r hr)]
  exact forced_marginal C hcoh hatoms hE5 n hsp hc hr

/-- **K2 — the linked determination theorem (of record).** `PCPσ ∧ E5σ ∧ E1x Q P ∧ E2xσIdx` at
`σ := stateOf C`, over a grid with `SpuriousEntails` and `ValuesAtRep` on every day, with every
pinned coordinate small today and in faith's scope `Sminus (n+1) (n+1)` (`hscope`): the base
satisfies **exact finite-time no-net-expected-update** `D_NNUcell C index Q` on every pinned
coordinate. Faith is read only at the pinned listed coordinates (`E2xσIdx`); the full-`E2xσ`
form is `determination_e2xσ`. Scope clauses, as the mandate asks: `pinned`, `Sminus (n+1) (n+1)`,
stage-level `PCPσ` (not `PCPσTheory`, which with `E5σ` collapses the superbelief to a point mass).
Source: [[bli-program]] §3.6(ii); [[bli-program-desiderata]] I6; mandate K2 (judged item 1)
Kind: C
Fidelity: exact (stage level; `E2xσIdx`; scope conditions stated)
Hyps: (a); (c) inherited: `Sminus` under-approximates the prose scope (bli-found F-14), through the faith predicate; `SpuriousEntails`/`ValuesAtRep`/`hscope` are instance conditions -/
theorem determination (hcoh : PCPσ atoms DP P)
    (hatoms : ∀ n, stateAtoms (stateOf C) S n ⊆ atoms n) (hE5 : E5σ (stateOf C) S P)
    (hE1 : E1x Q P) (hE2 : E2xσIdx (stateOf C) index S P)
    (hsp : ∀ n, SpuriousEntails (stateOf C) C.literal S index C.cells n)
    (hval : ∀ n, ValuesAtRep C S index n)
    (hscope : ∀ n, ∀ c ∈ pinned C index n,
      sentenceOfCode c ∈ smallSet n ∧ sentenceOfCode c ∈ Sminus (n + 1) (n + 1)) :
    D_NNUcell C index Q := by
  intro n c hc
  have hcidx : c ∈ index (n + 1) := ((mem_pinned C index n c).1 hc).1
  exact nnu_day C (hcoh n) (hatoms n) (partitionAt_of_E5σ hE5 n) hE1 (hsp n) (hval n) hc
    (fun q hq => hE2 n (n + 1) (Nat.lt_succ_self n) q hq c hcidx (hscope n c hc).2)
    (hscope n c hc).1

/-- **K2 at the mandate's `E2xσ` shape** (`bli-found`'s full faith): a corollary of
`determination`. Over any list-table B2 system this hypothesis package is empty
(`InstanceB2.e2xσ_unsat_of_unlisted_tautology`); over attempt B's conditioning-valued systems
it is inhabited (`Trilemma.determination_package_inhabited`).
Source: mandate K2; attempt B `d_nnucell_of_package`
Kind: C
Fidelity: exact as stated; vacuous over list-table systems (see `InstanceB2`)
Hyps: (a) -/
theorem determination_e2xσ (hcoh : PCPσ atoms DP P)
    (hatoms : ∀ n, stateAtoms (stateOf C) S n ⊆ atoms n) (hE5 : E5σ (stateOf C) S P)
    (hE1 : E1x Q P) (hE2 : E2xσ (stateOf C) S P)
    (hsp : ∀ n, SpuriousEntails (stateOf C) C.literal S index C.cells n)
    (hval : ∀ n, ValuesAtRep C S index n)
    (hscope : ∀ n, ∀ c ∈ pinned C index n,
      sentenceOfCode c ∈ smallSet n ∧ sentenceOfCode c ∈ Sminus (n + 1) (n + 1)) :
    D_NNUcell C index Q :=
  determination C hcoh hatoms hE5 hE1 (e2xσIdx_of_e2xσ index hE2) hsp hval hscope

/-- **The trilemma, horn (0)**: over a base violating `D_NNUcell`, no superbelief satisfies
`PCPσ ∧ E1x ∧ E2xσIdx ∧ E5σ` — the contrapositive of `determination` (Kind C, not P).
Source: [[bli-program]] §3.6(ii) (the linkage trilemma); mandate K2 (T0)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem trilemma_T0 (hviol : ¬ D_NNUcell C index Q)
    (hsp : ∀ n, SpuriousEntails (stateOf C) C.literal S index C.cells n)
    (hval : ∀ n, ValuesAtRep C S index n)
    (hscope : ∀ n, ∀ c ∈ pinned C index n,
      sentenceOfCode c ∈ smallSet n ∧ sentenceOfCode c ∈ Sminus (n + 1) (n + 1))
    (hatoms : ∀ n, stateAtoms (stateOf C) S n ⊆ atoms n) (P : History) :
    ¬ (PCPσ atoms DP P ∧ E1x Q P ∧ E2xσIdx (stateOf C) index S P ∧ E5σ (stateOf C) S P) := by
  rintro ⟨hcoh, hE1, hE2, hE5⟩
  exact hviol (determination C hcoh hatoms hE5 hE1 hE2 hsp hval hscope)

/-- **The coherence horn is the base's (this run's strengthening, of record).** If the base `Q`
is itself a stage-world mixture on the day-`n` algebra (containing the state atoms), the grid
has `SpuriousEntails`/`ValuesAtRep`, and the day-`(n+1)` linked states, their pairwise
conjunctions and their conjunctions with the pinned coordinate are all small on day `n`, then
`E1x Q P ∧ E2xσIdx ∧ E5σ` already force the no-net-update identity at `(n, c)` for `Q` — with
**no coherence assumption on `P`**. So "drop coherence" is not a free horn over a coherent base
once the state sentences are small: a T2 witness must be over an incoherent base (both attempts
found this independently: A's `no_T2_over_coherent_base`, B's `no_T2_over_dP`/
`faith_transfers_to_base`).
Source: this run (A's F-A4, B's FB-15); mandate K2 (T2)
Kind: C
Fidelity: exact
Hyps: (a); the smallness of the state algebra is an explicit hypothesis -/
theorem no_T2_over_coherent_base {n : ℕ}
    (hcohQ : CoherentOn (DP.D n) (smallAtoms n ∪ atoms n) (Q n))
    (hatoms : stateAtoms (stateOf C) S n ⊆ atoms n)
    (hsp : SpuriousEntails (stateOf C) C.literal S index C.cells n)
    (hval : ValuesAtRep C S index n)
    (hsmallσ : ∀ q ∈ S.states (n + 1), stateOf C (n + 1) q ∈ smallSet n)
    (hsmallσσ : ∀ q ∈ S.states (n + 1), ∀ q' ∈ S.states (n + 1),
      (stateOf C (n + 1) q ⋏ stateOf C (n + 1) q') ∈ smallSet n)
    (hE1 : E1x Q P) (hE2 : E2xσIdx (stateOf C) index S P) (hE5 : E5σ (stateOf C) S P)
    {c : ℕ} (hc : c ∈ pinned C index n)
    (hsmallφσ : ∀ q ∈ S.states (n + 1), (sentenceOfCode c ⋏ stateOf C (n + 1) q) ∈ smallSet n)
    (hφn : sentenceOfCode c ∈ smallSet n) (hφS : sentenceOfCode c ∈ Sminus (n + 1) (n + 1)) :
    Q n (sentenceOfCode c) =
      ∑ r ∈ C.cells (n + 1), (C.rep (n + 1) r : ℝ) * Q n (C.literal (n + 1) (sentenceOfCode c) r) := by
  have hcidx : c ∈ index (n + 1) := ((mem_pinned C index n c).1 hc).1
  have hpart : PartitionAt (stateOf C) S (Q n) (n + 1) := by
    refine ⟨?_, ?_⟩
    · rw [← (hE5 n).1]
      exact Finset.sum_congr rfl fun q hq => (hE1 n _ (hsmallσ q hq)).symm
    · intro q₁ hq₁ q₂ hq₂ hne
      rw [← (hE5 n).2 q₁ hq₁ q₂ hq₂ hne]
      exact (hE1 n _ (hsmallσσ q₁ hq₁ q₂ hq₂)).symm
  refine nnu_day C hcohQ hatoms hpart (fun _ _ _ => rfl) hsp hval hc (fun q hq => ?_) hφn
  rw [← hE1 n _ (hsmallφσ q hq), ← hE1 n _ (hsmallσ q hq)]
  exact hE2 n (n + 1) (Nat.lt_succ_self n) q hq c hcidx hφS

end Record

section Variant

variable {DP : DeductiveProcess} {S : StateSystem} {P Q : History} {index : ℕ → List ℕ}

/-- **K2, attempt A's variant (partition-respecting coherence, `Tabular`)**, restated over the
record family through the bridge: if `P` is a mixture of stage worlds that *respect the
day-`(n+1)` cell partition* (`AttemptA.PCPσ`), over a `Tabular` system, then
`E5σ ∧ E1x ∧ E2xσIdx` force `D_NNUcell`. Neither this nor `determination` implies the other:
this one needs no `SpuriousEntails` (so it covers grids missing a candidate) but modifies the
coherence worlds; the record one keeps the mandate's `PCPσ` and asks the grid to be closed.
Source: mandate K2; attempt A `determination`
Kind: C
Fidelity: variant: partition-respecting mixture worlds in place of the mandate's `PCPσ`
Hyps: (a); (c) disclosed: the mixture worlds respect the cell partition (attempt A's deviation 2) -/
theorem determination_partition (C : CellFamilyT DP) (hT : AttemptA.Tabular (ofB C) index S)
    (hcoh : AttemptA.PCPσ (ofB C) (stateOf C) S P) (hE5 : E5σ (stateOf C) S P) (hE1 : E1x Q P)
    (hE2 : E2xσIdx (stateOf C) index S P)
    (hscope : ∀ n, ∀ c ∈ pinned C index n,
      sentenceOfCode c ∈ smallSet n ∧ sentenceOfCode c ∈ Sminus (n + 1) (n + 1)) :
    D_NNUcell C index Q :=
  (d_nnucell_ofB C index Q).1 (AttemptA.determination (ofB C) index S Q P hT hcoh hE5 hE1 hE2
    fun n c hc => hscope n c ((mem_pinned_ofB C index n c).1 hc))

end Variant

end Cleanroom.Bli.BliLinkage

import Cleanroom.Bli.BliLinkageB.Bracket

/-!
# bli-linkage, angle B — the exact determination theorem, and why interval linkage does not
dissolve it for B2

The decisive question of angle B is whether the trilemma survives when linkage is the
*interval* linkage with overlapping open cells. The answer this module proves is: **for the B2
state sentence it survives, because the exact linkage is propositional** — the state sentence
*is* the conjunction of its cell literals (`stateOf`), so the determination of the marginals
does not go through any quote, interval or theory fact at all:

* `determination_stage`: over a grid in which a candidate together with a cell literal it does
  not list entails another candidate (`SpuriousEntails` — true of every full product grid, and
  of `Grid.fixedStates`), under stage-level coherence and the partition constraint alone,
  `P n (lit_{n+1,φ,r}) = cellMass_r` on every pinned coordinate. No linkage hypothesis, no
  interval semantics, no exclusivity fact about the stage: the only ingredients are "exactly one
  candidate holds in a charged world" (`Mixture.lean`) and the grid's closure.
* `determination_theory`: the same over an arbitrary grid listing the coordinate, under
  theory-level coherence, with the completed theory's exclusivity of literals (`C.excl`) doing
  the grid's work.
* `d_nnucell_of_package`: with `E1x` and faith (`E2xσ`) the exact identity `D_NNUcell` follows
  — the determination theorem of record, stage-level — and `trilemma_T0` is its contrapositive:
  over a base violating `D_NNUcell`, no `P` satisfies `PCPσ ∧ E1x ∧ E2xσ ∧ E5σ`.

So the interval brackets of `Bracket.lean` are *consequences* of the B2 state sentence, not an
alternative linkage: the exact determination holds beneath them, at the stage level, and the
trilemma stands under both linkages. Where interval linkage is the *only* link — an abstract
state family linked to the quotes but not to the cell literals — the package is satisfiable with
`D_NNUcell` violated; that is `Dissolve.lean`'s witness, and the comparison between the two is
this angle's answer to the mandate's decisive question.
-/

namespace Cleanroom.Bli.BliLinkageB

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

section Stage

variable {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) {S : StateSystem} {atoms : ℕ → Finset ℕ}
variable {DP : DeductiveProcess} {P Q : History} {index : ℕ → List ℕ}

/-- The cell literal of a pinned coordinate is small on day `n`, hence has its atoms in the
day-`n` algebra.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem literal_atoms_subset {n c : ℕ} (hc : c ∈ pinned C index n) {r : ℕ}
    (hr : r ∈ C.cells (n + 1)) :
    sentenceAtomCodes (C.literal (n + 1) (sentenceOfCode c) r) ⊆ smallAtoms n ∪ atoms n :=
  (atoms_subset_smallAtoms (by
    rw [mem_smallSet]; exact ((mem_pinned C index n c).1 hc).2 r hr)).trans
    Finset.subset_union_left

/-- **The exact determination theorem, stage level (K1 for the B2 state sentence).** Over a
grid with `SpuriousEntails` at day `n`, under stage-relative coherence on the day-`n` small
sentences and the day-`(n+1)` state sentences, and the partition constraint: for every pinned
coordinate `c` and every cell `r`, the mixture's price of tomorrow's cell literal is the mass of
the candidates assigning `c` the cell `r`. Propositional: a charged world holds exactly one
candidate; that candidate's literal at `c` holds (conjunct); any other literal at `c` would, with
the candidate, entail a second candidate (`SpuriousEntails`), contradicting exclusivity.
Source: [[bli-program]] §3.6(i); mandate K1; bli-slides-010/011
Kind: P
Fidelity: exact (over grids with `SpuriousEntails`; at the stage level, where the mandate's theory-level `C.excl` is unavailable)
Hyps: (a); `SpuriousEntails` is a grid condition discharged by the instance -/
theorem determination_stage (hcoh : PCPσ atoms DP P)
    (hatoms : ∀ n, stateAtoms (stateOf C) S n ⊆ atoms n) (hE5 : E5σ (stateOf C) S P) (n : ℕ)
    (hsp : SpuriousEntails (stateOf C) C.literal S index C.cells n) {c : ℕ}
    (hc : c ∈ pinned C index n) {r : ℕ} (hr : r ∈ C.cells (n + 1)) :
    P n (C.literal (n + 1) (sentenceOfCode c) r) = cellMass (stateOf C) S P n c r := by
  obtain ⟨k, W, w, -, hM⟩ :=
    (coherentOnW_iff _ _ _).1 ((coherentOn_iff_coherentOnW _ _ _).1 (hcoh n))
  have hσA : ∀ q ∈ S.states (n + 1),
      sentenceAtomCodes (stateOf C (n + 1) q) ⊆ smallAtoms n ∪ atoms n := fun q hq =>
    (atoms_subset_stateAtoms (stateOf C) S hq).trans ((hatoms n).trans Finset.subset_union_right)
  have hpart := partitionAt_of_E5σ hE5 n
  have hlitA := literal_atoms_subset C (atoms := atoms) hc hr
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

/-- **The exact determination theorem on the base** (constraint 4′ is forced): with `E1x`, the
base's day-`n` price of tomorrow's cell literal equals the superbelief's marginal.
Source: [[bli-program]] §3.6(i); [[bli-program-desiderata]] P5e; mandate K1
Kind: C
Fidelity: exact (stage level, grids with `SpuriousEntails`)
Hyps: (a) -/
theorem forced_marginal (hcoh : PCPσ atoms DP P)
    (hatoms : ∀ n, stateAtoms (stateOf C) S n ⊆ atoms n) (hE5 : E5σ (stateOf C) S P)
    (hE1 : E1x Q P) (n : ℕ) (hsp : SpuriousEntails (stateOf C) C.literal S index C.cells n)
    {c : ℕ} (hc : c ∈ pinned C index n) {r : ℕ} (hr : r ∈ C.cells (n + 1)) :
    Q n (C.literal (n + 1) (sentenceOfCode c) r) = cellMass (stateOf C) S P n c r := by
  rw [← hE1 n _ (by rw [mem_smallSet]; exact ((mem_pinned C index n c).1 hc).2 r hr)]
  exact determination_stage C hcoh hatoms hE5 n hsp hc hr

/-- **D_NNUcell is forced (K2 (c), the determination theorem of record).** Under
`PCPσ ∧ E5σ ∧ E1x ∧ E2xσ` at `σ := stateOf C`, over a grid with `SpuriousEntails` and
`ValuesAtRep` on every day, with every pinned coordinate itself small today and in faith's scope:
the base satisfies exact finite-time no-net-expected-update on every pinned coordinate.
Route: balance by faith (`balance_day`), regrouped by cells (`sum_val_eq_sum_rep_cellMass`), each
cell mass equal to the literal's price (`forced_marginal`).
Source: [[bli-program]] §3.6(ii); [[bli-program-desiderata]] I6; mandate K2
Kind: C
Fidelity: exact (stage level; scope conditions on the pinned coordinates stated)
Hyps: (a); `SpuriousEntails`/`ValuesAtRep`/`hscope` are instance conditions -/
theorem d_nnucell_of_package (hcoh : PCPσ atoms DP P)
    (hatoms : ∀ n, stateAtoms (stateOf C) S n ⊆ atoms n) (hE5 : E5σ (stateOf C) S P)
    (hE1 : E1x Q P) (hE2 : E2xσ (stateOf C) S P)
    (hsp : ∀ n, SpuriousEntails (stateOf C) C.literal S index C.cells n)
    (hval : ∀ n, ValuesAtRep C S index n)
    (hscope : ∀ n, ∀ c ∈ pinned C index n,
      sentenceOfCode c ∈ smallSet n ∧ sentenceOfCode c ∈ Sminus (n + 1) (n + 1)) :
    D_NNUcell C index Q := by
  intro n c hc
  have hcidx : c ∈ index (n + 1) := ((mem_pinned C index n c).1 hc).1
  rw [balance_day hcoh hatoms hE5 hE2 hE1 n (hscope n c hc).1 (hscope n c hc).2,
    sum_val_eq_sum_rep_cellMass C (stateOf C) S P n (hval n) hcidx]
  exact Finset.sum_congr rfl fun r hr => by
    rw [forced_marginal C hcoh hatoms hE5 hE1 n (hsp n) hc hr]

/-- **The trilemma, horn (0)**: over a base violating `D_NNUcell`, no superbelief satisfies
`PCPσ ∧ E1x ∧ E2xσ ∧ E5σ` (the contrapositive of `d_nnucell_of_package`; Kind C, not P).
Source: [[bli-program]] §3.6(ii) (the linkage trilemma); mandate K2 (T0)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem trilemma_T0 (hviol : ¬ D_NNUcell C index Q)
    (hsp : ∀ n, SpuriousEntails (stateOf C) C.literal S index C.cells n)
    (hval : ∀ n, ValuesAtRep C S index n)
    (hscope : ∀ n, ∀ c ∈ pinned C index n,
      sentenceOfCode c ∈ smallSet n ∧ sentenceOfCode c ∈ Sminus (n + 1) (n + 1))
    (hatoms : ∀ n, stateAtoms (stateOf C) S n ⊆ atoms n) :
    ¬ (PCPσ atoms DP P ∧ E1x Q P ∧ E2xσ (stateOf C) S P ∧ E5σ (stateOf C) S P) := by
  rintro ⟨hcoh, hE1, hE2, hE5⟩
  exact hviol (d_nnucell_of_package C hcoh hatoms hE5 hE1 hE2 hsp hval hscope)

end Stage

section Theory

variable {DP : DeductiveProcess} (C : CellFamilyT DP) {S : StateSystem} {atoms : ℕ → Finset ℕ}
variable {P Q : History} {index : ℕ → List ℕ}

/-- **The exact determination theorem, theory level** (the mandate's K1 as sketched): under
theory-relative coherence and the partition constraint, over any grid every candidate of which
lists the coordinate, the completed theory's exclusivity of literals (`C.excl`) replaces the
grid closure: `P n (lit_{n+1,φ,r}) = cellMass_r` on every pinned coordinate.
Source: [[bli-program]] §3.6(i); mandate K1
Kind: P
Fidelity: exact (theory level: see `theory_coherent_e1x_decides` for why this level is degenerate with `E1x`)
Hyps: (a) -/
theorem determination_theory (hcoh : PCPσTheory atoms DP P)
    (hatoms : ∀ n, stateAtoms (stateOf C) S n ⊆ atoms n) (hE5 : E5σ (stateOf C) S P) (n : ℕ)
    {c : ℕ} (hc : c ∈ pinned C index n)
    (hlist : ∀ q ∈ S.states (n + 1), ∃ r', entryOf c (tableOfCode q) = some r') {r : ℕ}
    (hr : r ∈ C.cells (n + 1)) :
    P n (C.literal (n + 1) (sentenceOfCode c) r) = cellMass (stateOf C) S P n c r := by
  obtain ⟨k, W, w, hW, hM⟩ := (coherentOnW_iff _ _ _).1 (hcoh n)
  have hσA : ∀ q ∈ S.states (n + 1),
      sentenceAtomCodes (stateOf C (n + 1) q) ⊆ smallAtoms n ∪ atoms n := fun q hq =>
    (atoms_subset_stateAtoms (stateOf C) S hq).trans ((hatoms n).trans Finset.subset_union_right)
  have hpart := partitionAt_of_E5σ hE5 n
  have hlitA := literal_atoms_subset C (atoms := atoms) hc hr
  rw [hM.sum_and_state hσA hpart hlitA, cellMass, Finset.sum_filter]
  refine Finset.sum_congr rfl fun q hq => ?_
  by_cases he : entryOf c (tableOfCode q) = some r
  · rw [if_pos he]
    exact hM.and_state_eq_of_forced (hσA q hq) hlitA fun i _ hs =>
      holds_lit_of_holds_stateOf C hs he
  · rw [if_neg he]
    refine hM.and_state_eq_zero_of_excluded (hσA q hq) hlitA fun i _ hs hl => ?_
    obtain ⟨r', he'⟩ := hlist q hq
    have hne : r' ≠ r := fun h => he (by rw [he', h])
    exact C.excl (n + 1) (sentenceOfCode c) r' r hne (W i) (hW i)
      ⟨holds_lit_of_holds_stateOf C hs he', hl⟩

end Theory

end Cleanroom.Bli.BliLinkageB

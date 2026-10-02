import Cleanroom.Decision.DpCartesianFrames.Local
import Cleanroom.Decision.DpFairnessReloc.Singleton
import Mathlib.Data.Fintype.Card

/-!
# The straddle machinery and the surviving forward direction

Package `dp-cartesian-frames`, file 4 (T6, headline 3). Lazy seeding throughout.

* **Consulted straddling** (CFF-B′): `Straddles B S d` — some pure run consulting `d` has its
  outcome in `S` and some other has it outside `S`.
* **The no-straddle theorem** (ZO-12 / CFF-12, `observable2_fr_of_not_straddles`): if no point
  with at least two actions straddles `S`, then `{S, Sᶜ}` is observable in `Fr B` — the
  witnessing policy answers `f(S)` at the points consulted on `S`-runs and `f(Sᶜ)` elsewhere.
  Stated **without** a column-determinedness hypothesis (the sources carry one; it is a
  consequence, `columnDetermined_fr_of_not_straddles`, through CF-8).
* **Lemma A** (ZO-12, `cell_eq_of_sameRoute`): for column-determined `S`, the cell of the
  outcome at `(π, ε)` is a function of `ε`'s *prefix route* — the chance choices down to the
  first decision node with `≥ 2` actions (`SameRoute`). Proved by hybridizing profiles across
  that node's subtrees. Corollary (`cell_eq_of_two_le`): a tree whose root is a decision node
  with `≥ 2` actions admits only trivial column-determined partitions. Consequence
  (`cell_eq_of_mem_leavesBelow`): all runs through one `≥ 2`-action decision node share a cell,
  so ZO-12's `cell(q)` is well defined and its node-straddling is the run-straddling above.
* **CFF-13(a)** (`observable2_fr_of_stronglyFair`): strongly fair ⟹ every column-determined
  two-cell partition is observable in the lazy frame, through "strongly fair ⟹ no straddle"
  (`not_straddles_of_stronglyFair`): isomorphic fiber members share their realizable outcomes
  (a leaf below one member has a label-matching leaf below the other, and on an almost-fair
  tree every leaf is the run of some pure profile), while Lemma A pins each member's runs to
  one cell. Neither veridicality nor coverage appears.
-/

namespace Cleanroom.Decision.DpCartesianFrames

open CartesianFrames
open scoped CartesianFrames.Frame
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpFairnessReloc

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

section straddle

variable [DecidableEq ι] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]

/-! ### Consulted straddling and the no-straddle theorem -/

/-- **`d` straddles `S`** (consulted straddling, CFF-B′): some pure run consulting `d`
(`#_d > 0` on its leaf) has its outcome in `S`, and some pure run consulting `d` has its
outcome outside `S`. With column-determined `S` this is ZO-12's "the fiber of `d` straddles
two cells" (`cell_eq_of_mem_leavesBelow` makes the node cells well defined).
Source: cf-frontier CFF-B′ (line 50: "A point `d` straddles `S` iff some pure run consulting
`d` passes an `S`-exit and some pure run consulting `d` passes a `¬S`-exit"); zoo ZO-12
(line 107)
Kind: D
Fidelity: exact (run form; the exit form is equivalent under column-determinedness by Lemma A) -/
def Straddles (B : Tree Ω ι acts K) (S : Set (Ω × K)) (d : ι) : Prop :=
  (∃ (π : (e : ι) → acts e) (ε : ChanceProfile B),
      0 < count d B (runLeaf π B ε) ∧ readout B (runLeaf π B ε) ∈ S) ∧
  (∃ (π : (e : ι) → acts e) (ε : ChanceProfile B),
      0 < count d B (runLeaf π B ε) ∧ readout B (runLeaf π B ε) ∉ S)

omit [∀ d, DecidableEq (acts d)] in
/-- **The no-straddle theorem** (ZO-12 / CFF-12, headline 3): if no point with at least two
actions straddles `S`, then `{S, Sᶜ}` is observable in the lazy frame `Fr B`. The witnessing
policy for the conditional policy `(a₀ on S, a₁ off S)` answers `a₀` at every point consulted
by some `S`-run and `a₁` elsewhere; on an `S`-column it agrees with `a₀` at every point its run
consults, on a `Sᶜ`-column with `a₁` (a point consulted there and also on an `S`-run would
straddle), so by `runLeaf_congr` its run is `a₀`'s, resp. `a₁`'s. Single-action points need no
hypothesis (any two policies agree there). **No column-determinedness hypothesis**: the sources
assume it, and here it follows (`columnDetermined_fr_of_not_straddles`).
Source: zoo ZO-12 Theorem (line 107); cf-frontier CFF-12 (line 80)
Kind: P
Fidelity: stronger: no column-determinedness hypothesis; single-action points exempt (ZO-12
exempts only those on the prefix)
Hyps: none -/
theorem observable2_fr_of_not_straddles (B : Tree Ω ι acts K) (S : Set (Ω × K))
    (hns : ∀ d, 2 ≤ Fintype.card (acts d) → ¬ Straddles B S d) : Observable2 (Fr B) S := by
  classical
  intro a₀ a₁
  let inS : ι → Prop := fun d => ∃ (π : (e : ι) → acts e) (ε : ChanceProfile B),
    0 < count d B (runLeaf π B ε) ∧ readout B (runLeaf π B ε) ∈ S
  let πf : (d : ι) → acts d := fun d => if inS d then a₀ d else a₁ d
  refine ⟨πf, fun ε => ?_⟩
  simp only [Fr_outcome]
  by_cases hS : readout B (runLeaf πf B ε) ∈ S
  · refine ⟨fun _ => ?_, fun h => absurd hS h⟩
    have heq : runLeaf πf B ε = runLeaf a₀ B ε := runLeaf_congr πf a₀ B ε fun d hd => by
      have hin : inS d := ⟨πf, ε, hd, hS⟩
      show (if inS d then a₀ d else a₁ d) = a₀ d
      rw [if_pos hin]
    rw [heq]
  · refine ⟨fun h => absurd h hS, fun _ => ?_⟩
    have heq : runLeaf πf B ε = runLeaf a₁ B ε := runLeaf_congr πf a₁ B ε fun d hd => by
      by_cases h2 : 2 ≤ Fintype.card (acts d)
      · have hnot : ¬ inS d := fun hin => hns d h2 ⟨hin, ⟨πf, ε, hd, hS⟩⟩
        show (if inS d then a₀ d else a₁ d) = a₁ d
        rw [if_neg hnot]
      · haveI : Subsingleton (acts d) := Fintype.card_le_one_iff_subsingleton.mp (by omega)
        exact Subsingleton.elim _ _
    rw [heq]

omit [∀ d, DecidableEq (acts d)] in
/-- No straddling ⟹ column-determined membership (through CF-8).
Source: zoo ZO-12 (the sources take column-determinedness as a hypothesis; here it is derived)
Kind: C
Fidelity: exact
Hyps: none -/
theorem columnDetermined_fr_of_not_straddles (B : Tree Ω ι acts K) (S : Set (Ω × K))
    (hns : ∀ d, 2 ≤ Fintype.card (acts d) → ¬ Straddles B S d) : ColumnDetermined (Fr B) S :=
  (observable2_fr_of_not_straddles B S hns).columnDetermined

end straddle

/-! ### Lemma A: the cell is a function of the prefix route -/

section lemmaA

variable [DecidableEq ι] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]

/-- **Same prefix route**: two profiles agree on every chance choice from the root down to the
first decision node with at least two actions (a decision node with fewer actions is forced
and the route continues through its children).
Source: zoo ZO-12 Lemma A (line 105: "prefix route `r(ε)` (root-to-first-`≥2`-action-decision-
node chance path)")
Kind: D
Fidelity: exact -/
def SameRoute : (B : Tree Ω ι acts K) → ChanceProfile B → ChanceProfile B → Prop
  | .leaf _ _, _, _ => True
  | .chance _ _ child, ε, ε' => ε.1 = ε'.1 ∧ SameRoute (child ε.1) (ε.2 ε.1) (ε'.2 ε.1)
  | .decision d child, ε, ε' =>
      2 ≤ Fintype.card (acts d) ∨ ∀ a, SameRoute (child a) (ε a) (ε' a)

omit [DecidableEq ι] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] in
/-- Column-determinedness of `Fr` descends to the children of a chance node (fill the other
coordinates arbitrarily).
Source: none: infrastructure
Kind: L -/
theorem columnDetermined_fr_chance_child {n : ℕ} {β : FinDistr K (Fin n)}
    {child : Fin n → Tree Ω ι acts K} {S : Set (Ω × K)}
    (hcd : ColumnDetermined (Fr (.chance n β child)) S) (i : Fin n) :
    ColumnDetermined (Fr (child i)) S := by
  intro ε π π'
  have h := hcd (i, Function.update (fun j => Classical.arbitrary (ChanceProfile (child j))) i ε)
    π π'
  simp only [Fr_outcome, runLeaf_chance, Function.update_self] at h
  exact h

omit [DecidableEq ι] [∀ d, Fintype (acts d)] in
/-- Column-determinedness of `Fr` descends to the child of a forced (single-action) decision
node.
Source: none: infrastructure
Kind: L -/
theorem columnDetermined_fr_decision_child_forced {d : ι} {child : acts d → Tree Ω ι acts K}
    {S : Set (Ω × K)} [Subsingleton (acts d)]
    (hcd : ColumnDetermined (Fr (.decision d child)) S) (a : acts d) :
    ColumnDetermined (Fr (child a)) S := by
  intro ε π π'
  have h := hcd (Function.update (fun b => Classical.arbitrary (ChanceProfile (child b))) a ε)
    π π'
  have hπ : π d = a := Subsingleton.elim _ _
  have hπ' : π' d = a := Subsingleton.elim _ _
  simp only [Fr_outcome, runLeaf_decision] at h
  rw [hπ, hπ', Function.update_self] at h
  exact h

/-- **Lemma A's corollary / the hybridization step**: on a tree whose root is a decision node
with at least two actions, a column-determined partition is trivial — any two runs' outcomes
lie on the same side of `S`. Hybridize: for `π d ≠ π' d` the profile `ε'[π d ↦ ε (π d)]` is
read by `π` as `ε` and by `π'` as `ε'`, and column-determinedness bridges the two rows; for
`π d = π' d` pass through a third policy answering `b ≠ π d`.
Source: zoo ZO-12 Lemma A corollary (line 105: "a decision root admits only trivial
chance-determined partitions")
Kind: P
Fidelity: exact
Hyps: none -/
theorem cell_eq_of_two_le {d : ι} {child : acts d → Tree Ω ι acts K} {S : Set (Ω × K)}
    (hcd : ColumnDetermined (Fr (.decision d child)) S) (h2 : 2 ≤ Fintype.card (acts d))
    (π π' : (e : ι) → acts e) (ε ε' : ChanceProfile (.decision d child)) :
    (readout _ (runLeaf π (.decision d child) ε) ∈ S ↔
      readout _ (runLeaf π' (.decision d child) ε') ∈ S) := by
  have key : ∀ (π π' : (e : ι) → acts e) (ε ε' : ChanceProfile (.decision d child)),
      π d ≠ π' d → (readout _ (runLeaf π (.decision d child) ε) ∈ S ↔
        readout _ (runLeaf π' (.decision d child) ε') ∈ S) := by
    intro π π' ε ε' hne
    have h1 : runLeaf π (.decision d child) (Function.update ε' (π d) (ε (π d))) =
        runLeaf π (.decision d child) ε := by
      simp only [runLeaf_decision, Function.update_self]
    have h2 : runLeaf π' (.decision d child) (Function.update ε' (π d) (ε (π d))) =
        runLeaf π' (.decision d child) ε' := by
      simp only [runLeaf_decision, Function.update_of_ne (Ne.symm hne)]
    have h := hcd (Function.update ε' (π d) (ε (π d))) π π'
    simp only [Fr_outcome] at h
    rw [h1, h2] at h
    exact h
  by_cases hne : π d = π' d
  · obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card (by omega) (π d)
    have hb' : Function.update π d b d = b := Function.update_self ..
    exact (key π (Function.update π d b) ε ε' (by rw [hb']; exact hb.symm)).trans
      (key (Function.update π d b) π' ε' ε' (by rw [hb']; exact fun h => hb (h.trans hne.symm)))
  · exact key π π' ε ε' hne

/-- **Lemma A** (ZO-12): for column-determined `S`, the cell of the outcome at `(π, ε)` depends
only on `ε`'s prefix route — profiles with the same route give outcomes on the same side of `S`
for all policies. Structural induction: through chance nodes and forced decision nodes by the
descent lemmas; at the first decision node with `≥ 2` actions by hybridization.
Source: zoo ZO-12 Lemma A (line 105)
Kind: P
Fidelity: exact
Hyps: none -/
theorem cell_eq_of_sameRoute [∀ d, Nonempty (acts d)] (S : Set (Ω × K)) :
    (B : Tree Ω ι acts K) → ColumnDetermined (Fr B) S →
      ∀ (ε ε' : ChanceProfile B), SameRoute B ε ε' → ∀ π π' : (e : ι) → acts e,
        (readout B (runLeaf π B ε) ∈ S ↔ readout B (runLeaf π' B ε') ∈ S)
  | .leaf _ _, _, _, _, _, _, _ => Iff.rfl
  | .chance n β child, hcd, ⟨i, εs⟩, ⟨i', εs'⟩, hsr, π, π' => by
      obtain ⟨hi, hr⟩ := hsr
      simp only at hi
      subst hi
      exact cell_eq_of_sameRoute S (child i) (columnDetermined_fr_chance_child hcd i)
        (εs i) (εs' i) hr π π'
  | .decision d child, hcd, ε, ε', hsr, π, π' => by
      by_cases h2 : 2 ≤ Fintype.card (acts d)
      · exact cell_eq_of_two_le hcd h2 π π' ε ε'
      · haveI : Subsingleton (acts d) := Fintype.card_le_one_iff_subsingleton.mp (by omega)
        have hforced : ∀ a, SameRoute (child a) (ε a) (ε' a) := hsr.resolve_left h2
        have hπ : π' d = π d := Subsingleton.elim _ _
        have ih := cell_eq_of_sameRoute S (child (π d))
          (columnDetermined_fr_decision_child_forced hcd (π d)) (ε (π d)) (ε' (π d))
          (hforced (π d)) π π'
        simp only [runLeaf_decision]
        rw [hπ]
        exact ih

omit [DecidableEq ι] in
/-- Two runs through the same decision node with at least two actions have the same prefix
route (the route ends at or above that node, and both runs take the node's path).
Source: zoo ZO-12 (line 107: "`cell(q)` for decision nodes `q` at or below the first
`≥2`-action decision node of their path")
Kind: P
Fidelity: exact
Hyps: none -/
theorem sameRoute_of_mem_leavesBelow :
    (B : Tree Ω ι acts K) → ∀ (q : B.DecNode), 2 ≤ Fintype.card (acts (pt B q)) →
      ∀ (π : (e : ι) → acts e) (ε : ChanceProfile B) (π' : (e : ι) → acts e)
        (ε' : ChanceProfile B), runLeaf π B ε ∈ leavesBelow B q →
        runLeaf π' B ε' ∈ leavesBelow B q → SameRoute B ε ε'
  | .leaf _ _, q, _, _, _, _, _, _, _ => q.elim
  | .chance n β child, ⟨i, q⟩, h2, π, ⟨j, εs⟩, π', ⟨j', εs'⟩, hm, hm' => by
      rw [mem_leavesBelow] at hm hm'
      simp only [runLeaf_chance, edgeOf_chance] at hm hm'
      by_cases hj : j = i
      · subst hj
        by_cases hj' : j = j'
        · subst hj'
          rw [dif_pos rfl] at hm hm'
          exact ⟨rfl, sameRoute_of_mem_leavesBelow (child j) q h2 π (εs j) π' (εs' j)
            ((mem_leavesBelow _ _ _).mpr hm) ((mem_leavesBelow _ _ _).mpr hm')⟩
        · rw [dif_neg (fun h => hj' h.symm)] at hm'
          exact absurd hm' (by simp)
      · rw [dif_neg hj] at hm
        exact absurd hm (by simp)
  | .decision d child, q, h2, π, ε, π', ε', hm, hm' => by
      by_cases hd : 2 ≤ Fintype.card (acts d)
      · exact Or.inl hd
      · right
        haveI : Subsingleton (acts d) := Fintype.card_le_one_iff_subsingleton.mp (by omega)
        rcases q with _ | ⟨b, q'⟩
        · exact absurd h2 hd
        · intro a
          have ha : a = b := Subsingleton.elim _ _
          subst ha
          have hrun : runLeaf π (.decision d child) ε = ⟨a, runLeaf π (child a) (ε a)⟩ := by
            have hπ : π d = a := Subsingleton.elim _ _
            rw [runLeaf_decision, hπ]
          have hrun' : runLeaf π' (.decision d child) ε' = ⟨a, runLeaf π' (child a) (ε' a)⟩ := by
            have hπ : π' d = a := Subsingleton.elim _ _
            rw [runLeaf_decision, hπ]
          rw [hrun, mem_leavesBelow, edgeOf_decision_some, dif_pos rfl] at hm
          rw [hrun', mem_leavesBelow, edgeOf_decision_some, dif_pos rfl] at hm'
          exact sameRoute_of_mem_leavesBelow (child a) q' h2 π (ε a) π' (ε' a)
            ((mem_leavesBelow _ _ _).mpr hm) ((mem_leavesBelow _ _ _).mpr hm')

/-- **The cell of a node is well defined** (ZO-12's `cell(q)`): for column-determined `S`, all
runs through one decision node with at least two actions have outcomes on the same side of
`S`. Lemma A composed with `sameRoute_of_mem_leavesBelow`.
Source: zoo ZO-12 (line 107)
Kind: C
Fidelity: exact
Hyps: none -/
theorem cell_eq_of_mem_leavesBelow [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    {S : Set (Ω × K)} (hcd : ColumnDetermined (Fr B) S) (q : B.DecNode)
    (h2 : 2 ≤ Fintype.card (acts (pt B q))) (π : (e : ι) → acts e) (ε : ChanceProfile B)
    (π' : (e : ι) → acts e) (ε' : ChanceProfile B) (hm : runLeaf π B ε ∈ leavesBelow B q)
    (hm' : runLeaf π' B ε' ∈ leavesBelow B q) :
    (readout B (runLeaf π B ε) ∈ S ↔ readout B (runLeaf π' B ε') ∈ S) :=
  cell_eq_of_sameRoute S B hcd ε ε' (sameRoute_of_mem_leavesBelow B q h2 π ε π' ε' hm hm') π π'

end lemmaA

/-! ### Strongly fair ⟹ no straddle ⟹ observable (CFF-13(a)) -/

section fair

variable [DecidableEq ι] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]

omit [DecidableEq ι] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] in
/-- The payoff at an embedded subtree leaf is the subtree's payoff (companion of
`dp-fairness-reloc`'s `world_embedLeaf`).
Source: none: infrastructure
Kind: L -/
theorem payoff_embedLeaf : (B : Tree Ω ι acts K) → ∀ (q : B.DecNode) (ℓ : (subtreeAt B q).Leaves),
    payoff B (embedLeaf B q ℓ) = payoff (subtreeAt B q) ℓ
  | .leaf _ _, q, _ => q.elim
  | .chance _ _ child, ⟨i, q⟩, ℓ => payoff_embedLeaf (child i) q ℓ
  | .decision _ _, none, _ => rfl
  | .decision _ child, some ⟨a, q⟩, ℓ => payoff_embedLeaf (child a) q ℓ

omit [∀ d, Fintype (acts d)] in
/-- **Every leaf of an almost-fair tree is the run of some pure profile**: build the policy
along the leaf's path; since no point recurs on the path, the answers are consistent.
Source: cf-frontier CFF-B′ (line 50: "on a tree with no nested fiber every leaf is
realizable")
Kind: P
Fidelity: exact
Hyps: none -/
theorem exists_run_of_almostFair [∀ d, Nonempty (acts d)] :
    (B : Tree Ω ι acts K) → AlmostFair B → ∀ ℓ : B.Leaves,
      ∃ (π : (e : ι) → acts e) (ε : ChanceProfile B), runLeaf π B ε = ℓ
  | .leaf _ _, _, _ => ⟨fun e => Classical.arbitrary (acts e), (), rfl⟩
  | .chance n β child, haf, ⟨i, ℓ⟩ => by
      have haf' : AlmostFair (child i) := fun d ℓ' => haf d ⟨i, ℓ'⟩
      obtain ⟨π, ε, hε⟩ := exists_run_of_almostFair (child i) haf' ℓ
      refine ⟨π, (i, Function.update (fun j => Classical.arbitrary (ChanceProfile (child j))) i ε),
        ?_⟩
      simp only [runLeaf_chance, Function.update_self]
      rw [hε]
  | .decision d child, haf, ⟨a, ℓ⟩ => by
      have haf' : AlmostFair (child a) := fun e ℓ' =>
        le_trans (Nat.le_add_left _ _) (haf e ⟨a, ℓ'⟩)
      obtain ⟨π, ε, hε⟩ := exists_run_of_almostFair (child a) haf' ℓ
      refine ⟨Function.update π d a,
        Function.update (fun b => Classical.arbitrary (ChanceProfile (child b))) a ε, ?_⟩
      have hπd : Function.update π d a d = a := Function.update_self ..
      rw [runLeaf_decision, hπd, Function.update_self]
      refine congrArg (Sigma.mk a) ?_
      have hcongr : runLeaf π (child a) ε = runLeaf (Function.update π d a) (child a) ε :=
        runLeaf_congr π (Function.update π d a) (child a) ε fun e he => by
          by_cases hed : e = d
          · subst hed
            exfalso
            have h1 := haf e ⟨a, ℓ⟩
            have h2 : count e (.decision e child) ⟨a, ℓ⟩ = 1 + count e (child a) ℓ := by
              show (if e = e then 1 else 0) + count e (child a) ℓ = 1 + count e (child a) ℓ
              rw [if_pos rfl]
            rw [hε] at he
            omega
          · rw [Function.update_of_ne hed]
      exact hcongr.symm.trans hε

/-- **Strongly fair ⟹ no point with two actions straddles a column-determined `S`.** Two runs
consulting `d` with outcomes on different sides pass `d`-nodes `q₁`, `q₂`; strong fairness
gives a label-matching leaf below `q₂` for the `S`-run's leaf; that leaf is realized by a pure
run (almost-fair) through `q₂`, whose outcome lies in `S` — contradicting Lemma A at `q₂`
(all runs through a `≥ 2`-action node share a cell).
Source: cf-frontier CFF-13(a)/(b) (line 82: "if `d` were consulted below an `S`-exit and a
`¬S`-exit … contradict equal realizable sets"); zoo ZO-12 (line 107: "Strong fairness implies
the hypothesis")
Kind: P
Fidelity: exact
Hyps: none -/
theorem not_straddles_of_stronglyFair [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    {S : Set (Ω × K)} (hsf : StronglyFair B) (hcd : ColumnDetermined (Fr B) S) (d : ι)
    (h2 : 2 ≤ Fintype.card (acts d)) : ¬ Straddles B S d := by
  rintro ⟨⟨π₁, ε₁, hc₁, hS₁⟩, ⟨π₂, ε₂, hc₂, hS₂⟩⟩
  obtain ⟨q₁, hq₁, he₁⟩ := exists_dNode_of_count_pos d B _ hc₁
  obtain ⟨q₂, hq₂, he₂⟩ := exists_dNode_of_count_pos d B _ hc₂
  have hiso := hsf d q₁ ((mem_fiber B d q₁).mpr hq₁) q₂ ((mem_fiber B d q₂).mpr hq₂)
  obtain ⟨e, he⟩ := hiso.exists_leafEquiv
  obtain ⟨ℓ₁', hℓ₁'⟩ := exists_embedLeaf_of_edge B q₁ _ he₁
  have hread : readout B (embedLeaf B q₂ (e ℓ₁')) = readout B (runLeaf π₁ B ε₁) := by
    rw [← hℓ₁']
    unfold readout
    rw [world_embedLeaf, world_embedLeaf, payoff_embedLeaf, payoff_embedLeaf, (he ℓ₁').1,
      (he ℓ₁').2.1]
  obtain ⟨π₃, ε₃, hrun₃⟩ :=
    exists_run_of_almostFair B (StronglyFair.almostFair B hsf) (embedLeaf B q₂ (e ℓ₁'))
  have hm₃ : runLeaf π₃ B ε₃ ∈ leavesBelow B q₂ := by
    rw [hrun₃, mem_leavesBelow]; exact edgeOf_embedLeaf B q₂ _
  have hm₂ : runLeaf π₂ B ε₂ ∈ leavesBelow B q₂ := (mem_leavesBelow _ _ _).mpr he₂
  have hcell := cell_eq_of_mem_leavesBelow hcd q₂ (by rw [hq₂]; exact h2) π₃ ε₃ π₂ ε₂ hm₃ hm₂
  exact hS₂ (hcell.mp (by rw [hrun₃, hread]; exact hS₁))

/-- **CFF-13(a) — the surviving forward direction of open problem 1** (headline 3): a strongly
fair tree makes every column-determined two-cell partition observable in its lazy frame.
Composition: strongly fair ⟹ no straddle ⟹ observable. Neither subtree-veridicality nor
coverage is used; the seeding is lazy (the identified re-reading is false, CFF-15, see
`Reloc.lean`).
Source: cf-frontier CFF-13(a) (line 82); zoo ZO-12 (line 107); mandate T6(c)
Kind: C
Fidelity: exact
Hyps: none -/
theorem observable2_fr_of_stronglyFair [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    {S : Set (Ω × K)} (hsf : StronglyFair B) (hcd : ColumnDetermined (Fr B) S) :
    Observable2 (Fr B) S :=
  observable2_fr_of_not_straddles B S fun d h2 => not_straddles_of_stronglyFair hsf hcd d h2

end fair

end Cleanroom.Decision.DpCartesianFrames

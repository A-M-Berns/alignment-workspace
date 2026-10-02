import Cleanroom.Decision.DpReferentsCdt.Rows

/-!
# `dp-referents-cdt` · audit r1 (adversarial) probe: Definition 7 for *every* procedure does not
give `refR2Real = refR1State` — the counter-tree findings F3 says was not built

Not imported by the library.

Findings F3 claims that dp-sl-2-061(i)'s `refR2Real` clause needs F3′ for `C`, not Definition 7
recording alone, because a node-action-veridical `d`-node whose leaves all lie outside `O_d`
enters `realFiber` and moves `refR2Real` without touching Definition 7 — and says "no counter-tree
was built". This probe builds it. `sepTree`: a fair coin, index `0` = the observed branch
(`c = true`), and a `d`-node on *each* branch; payoffs `(a, true) 1`, `(b, true) 0`,
`(a, false) 100`, `(b, false) 0`; `O_d = {c = true}`; `actEv a = {act = a}`.

* Definition 7 recording holds **for every procedure** (`RecordsForAll`): the positive `O_d`-runs
  are exactly the `c = true` runs, each passes the one `d`-node of that branch, which is
  subtree-veridical and records the act.
* F3′ fails for every procedure (`¬ ActRecording`): the `c = false` node is node-action-veridical
  but not subtree-veridical, so `ActRecording`'s first (structural) clause fails.
* `refR1State a = 1 = refR3 a` (the `O_d`-conditioned referents only see the `c = true` branch,
  the second through the package's own `refR3_eq_refR1State_of_recordsForAll`), while
  `refR2Real a = 101/2`: reading 1 averages the off-`O_d` node in.

So the ledger's T5(iv) row is right to say "weaker: the `refR2Real` clause needs F3′ for `C`", and
that weakening is forced, not a proof shortfall: the mandate's T5(iv) sentence (`refR2Real` under
Definition 7 alone) is false. This is the first Lean separation of "Definition 7 for every
procedure" from "F3′" in the direction the package did not ship.
-/

namespace Cleanroom.Decision.DpReferentsCdt.AuditR1Adversarial

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt
open Cleanroom.Decision.DpReferentsCdt
open Finset

/-- Worlds `(act, c)`. -/
abbrev SepW : Type := Act2 × Bool

/-- The separating tree: fair coin, then a `d`-node on each branch. -/
def sepTree : Tree SepW Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i =>
    .decision () fun act =>
      .leaf (act, decide (i = 0))
        (if i = 0 then (if act = .a then 1 else 0) else (if act = .a then 100 else 0))

/-- `O_d = {c = true}`. -/
def sepObs : Unit → Finset SepW := fun _ => Finset.univ.filter fun w => w.2 = true

/-- `actEv a = {act = a}`. -/
def sepActEv : (d : Unit) → Act2 → Finset SepW := fun _ a => Finset.univ.filter fun w => w.1 = a

/-- Leaf sums on `sepTree`. -/
theorem sep_sum (f : sepTree.Leaves → ℚ) : ∑ ℓ, f ℓ = ∑ i, ∑ act, f ⟨i, ⟨act, ()⟩⟩ := by
  unfold sepTree at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun act _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- Every `d`-node of `sepTree` is node-action-veridical (the act coordinate is written by the
draw at that node). -/
theorem sep_nav (q : sepTree.DecNode) : NodeActionVeridical sepActEv sepTree q := by
  rcases q with ⟨j, _ | ⟨act', e⟩⟩
  · intro ℓ a ha
    rcases ℓ with ⟨i, act, _⟩
    by_cases hij : i = j
    · subst hij
      simp only [sepTree, edgeOf_chance, dite_true, edgeOf_decision_none, Option.some.injEq] at ha
      subst ha
      simp [sepActEv, sepTree, world]
    · simp [sepTree, edgeOf_chance, hij] at ha
  · exact e.elim

/-- **Definition 7 recording for every procedure.** -/
theorem sep_recordsForAll : RecordsForAll sepObs sepActEv sepTree () := by
  intro C ℓ _ hobs
  rcases ℓ with ⟨i, act, _⟩
  have hi : i = 0 := by
    by_contra h
    simp [sepObs, sepTree, world, h] at hobs
  subst hi
  refine ⟨by simp [sepTree], ?_⟩
  rintro (⟨j, _ | ⟨act', e⟩⟩) - a ha
  · by_cases hj : (0 : Fin 2) = j
    · subst hj
      simp only [sepTree, edgeOf_chance, dite_true, edgeOf_decision_none, Option.some.injEq] at ha
      subst ha
      refine ⟨?_, ?_, ?_⟩
      · intro ℓ' hℓ'
        rcases ℓ' with ⟨i', act'', _⟩
        rw [mem_leavesBelow] at hℓ'
        by_cases hi' : i' = 0
        · subst hi'
          simp [sepObs, sepTree, world]
        · simp [sepTree, edgeOf_chance, hi'] at hℓ'
      · simp [sepActEv, sepTree, world]
      · intro a' ha'
        simp [sepActEv, sepTree, world] at ha'
        exact ha'.symm
    · simp [sepTree, edgeOf_chance, hj] at ha
  · exact e.elim

/-- **Not F3′ for any procedure**: the `c = false` node is node-action-veridical but not
subtree-veridical. -/
theorem sep_not_actRecording (C : Proc Unit (fun _ => Act2) ℚ) :
    ¬ ActRecording sepObs sepActEv C sepTree () := by
  intro h
  have := h.1 ⟨1, none⟩ rfl (sep_nav _) ⟨1, ⟨.a, ()⟩⟩
    ((mem_leavesBelow sepTree _ _).mpr (by simp [sepTree, edgeOf_chance, edgeOf_decision_none]))
  simp [sepObs, sepTree, world] at this

/-- The real fiber is the whole fiber (every `d`-node is node-action-veridical). -/
theorem sep_realFiber : realFiber sepActEv sepTree () = Finset.univ :=
  Finset.eq_univ_iff_forall.mpr fun q =>
    (mem_realFiber sepActEv sepTree () q).mpr ⟨Subsingleton.elim _ _, sep_nav q⟩

/-- The fiber of `()` is every node. -/
theorem sep_fiber : fiber sepTree () = Finset.univ := by
  unfold fiber
  exact Finset.filter_true_of_mem fun q _ => Subsingleton.elim _ _

/-- **R2-real (reading 1) on `sepTree`**: `(101/2, 0)` — the off-`O_d` node is averaged in. -/
theorem sep_refR2Real (C : Proc Unit (fun _ => Act2) ℚ) :
    refR2Real sepActEv C sepTree () .a = 101 / 2 ∧ refR2Real sepActEv C sepTree () .b = 0 := by
  have hforced : ∀ a, realForced sepActEv C sepTree () a = siaSum C sepTree () a := by
    intro a
    unfold realForced
    rw [sep_realFiber, siaSum_eq_sum_fiber_forcedBelow]
  have hreach : realReach sepActEv C sepTree () = expCount C sepTree () := by
    unfold realReach
    rw [sep_realFiber, ← sum_reach_fiber_eq_expCount, sep_fiber]
  have hE : expCount C sepTree () = 1 := by
    unfold sepTree
    rw [expCount_chance]
    simp only [expCount_decision_self]
    have hleaf : ∀ (w : SepW) (r : ℚ), expCount C (leaf w r : Tree SepW Unit (fun _ => Act2) ℚ) () = 0 := by
      intro w r
      unfold expCount
      simp
    simp [hleaf, Fin.sum_univ_two, FinDistr.fair, FinDistr.coin]
  constructor <;>
  · unfold refR2Real
    rw [hforced, hreach, hE]
    unfold sepTree
    simp [siaSum_chance, siaSum_decision_self, value_leaf, FinDistr.fair, FinDistr.coin,
      Fin.sum_univ_two] <;> norm_num

/-- **R1-state on `sepTree`**: `(1, 0)` — only the `c = true` branch is seen. -/
theorem sep_refR1State (C : Proc Unit (fun _ => Act2) ℚ) :
    refR1State sepObs C sepTree () .a = 1 ∧ refR1State sepObs C sepTree () .b = 0 := by
  unfold refR1State condExp
  constructor <;>
  · rw [nu_eq_sum, paySum_eq_sum_ite, sep_sum, sep_sum]
    simp [sepTree, sepObs, world, leafLaw, payoff, FinDistr.fair, FinDistr.coin,
      Proc.deviatePure, Proc.deviate_same]

/-- `ν_{C[d↦a]}(O_d) = 1/2 > 0` for every `C` (the guard of `refR1State`). -/
theorem sep_nu_dev_obs_pos (C : Proc Unit (fun _ => Act2) ℚ) (a : Act2) :
    0 < nu (C.deviatePure () a) sepTree (sepObs ()) := by
  rw [nu_eq_sum, sep_sum]
  cases a <;> simp [sepTree, sepObs, world, leafLaw, FinDistr.fair, FinDistr.coin,
    Proc.deviatePure, Proc.deviate_same]

/-- **The separation**: Definition 7 recording for every procedure, not F3′, and
`refR3 a = refR1State a = 1 ≠ 101/2 = refR2Real a`. The `refR3` identity is the package's own
FA-20′(ii) (`refR3_eq_refR1State_of_recordsForAll`), so the `O_d`-conditioned referents agree
here exactly as the recording theorem says, and reading-1 R2-real is the odd one out. -/
theorem defSeven_not_fThreePrime (C : Proc Unit (fun _ => Act2) ℚ) :
    RecordsForAll sepObs sepActEv sepTree () ∧
    (¬ ActRecording sepObs sepActEv C sepTree ()) ∧
    refR3 sepObs sepActEv C sepTree () .a = 1 ∧
    refR1State sepObs C sepTree () .a = 1 ∧
    refR2Real sepActEv C sepTree () .a = 101 / 2 := by
  refine ⟨sep_recordsForAll, sep_not_actRecording C, ?_, (sep_refR1State C).1, (sep_refR2Real C).1⟩
  rw [refR3_eq_refR1State_of_recordsForAll sepObs sepActEv C sepTree sep_recordsForAll .a
    (sep_nu_dev_obs_pos C .a)]
  exact (sep_refR1State C).1

end Cleanroom.Decision.DpReferentsCdt.AuditR1Adversarial

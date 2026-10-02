import Cleanroom.Decision.DpReferentsCdt.C2A
import Cleanroom.Decision.DpCalibration.Selection
import Cleanroom.Found.DpCoreTree.Witnesses

/-!
# Separating witnesses: the post-act coin tree, tree J, the AMD and the selection tree

* **T1(b)** — the post-act coin tree (`faithful.md` line 22, the reviewer's counterexample to
  FA-20(i)): root `d`, then a fair coin `c`, `O_d = {c = 1}`, leaves `(a,1) 2`, `(a,0) 10`,
  `(b,1) 4`, `(b,0) 4`. The root is node-action-veridical but not subtree-veridical, so F3′ fails;
  reading 1 of R2-real gives `(6, 4) → a`, reading 2 gives `(2, 4) → b`, and R3 = R1-state = `(2, 4)`.
  This is the tree that decides dp-sl-2-058's ill-posedness (findings F1).
* **T6, the refutation row** — tree J at `δ_a`: Definition 7 recording holds *for `C`*, yet
  `refR3 b = refR2Real b = 4 ≠ 0 = refR1State b`; at a mixed label the evidential values are
  `(1, 4q)`, the R3-extended `T_EDT` approves exactly the label `q = 1/4` (a forced mixed label), and
  `δ_a` is not approved (`4 > 1`).
* **T4, the necessity battery for F3′** — the AMD under last-draw act events (`evStrict a =
  4(1−q)/(2−q) ≠ 4 = refR2Real a`, `¬ ActRecording`) and the selection tree `S_sel` (act values
  `(10−20q)/(1+q)`, `(20q−15)/(2−q)`, tie at `7/11`, value `−5/3`; `¬ ActRecording`;
  `refR2Real = (−20, −20)`): each lies outside C2-A′'s hypotheses.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpReferentsCdt

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt
open Finset

/-! ## Sums over a one-node real fiber -/

/-- A leaf tree has one leaf. Source: none: infrastructure. Kind: L -/
@[simp] theorem card_leaves_leaf {Ω ι : Type} {acts : ι → Type} [∀ d, Fintype (acts d)] (ω : Ω)
    (r : ℚ) : Fintype.card (leaf ω r : Tree Ω ι acts ℚ).Leaves = 1 := rfl

section uniqueFiber

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {acts : Unit → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)]
  (actEv : (d : Unit) → acts d → Finset Ω) (C : Proc Unit acts ℚ) (B : Tree Ω Unit acts ℚ)

/-- A sum over a real fiber with exactly one member. Source: none: infrastructure. Kind: L -/
theorem sum_realFiber_eq_of_unique (q₀ : B.DecNode)
    (hq : ∀ q, q ∈ realFiber actEv B () ↔ q = q₀) (f : B.DecNode → ℚ) :
    ∑ q ∈ realFiber actEv B (), f q = f q₀ := by
  rw [Finset.sum_eq_single q₀]
  · intro b hb hne; exact absurd ((hq b).mp hb) hne
  · intro h; exact absurd ((hq q₀).mpr rfl) h

/-- `refR2Real` on a `Unit`-point tree with a one-node real fiber `q₀` is
`forcedBelow q₀ / reach q₀`. Source: none: infrastructure. Kind: L -/
theorem refR2Real_eq_of_unique (q₀ : B.DecNode)
    (hq : ∀ q, q ∈ realFiber actEv B () ↔ q = q₀) (a : acts ()) :
    refR2Real actEv C B () a =
      forcedBelow B (NodePolicy.ofProc C B) q₀ a / reach C B q₀ := by
  unfold refR2Real realForced realReach
  rw [sum_realFiber_eq_of_unique actEv B q₀ hq, sum_realFiber_eq_of_unique actEv B q₀ hq,
    dif_pos rfl]

/-- `refR2RealObs` on a `Unit`-point tree with a one-node real fiber `q₀`.
Source: none: infrastructure. Kind: L -/
theorem refR2RealObs_eq_of_unique (obs : Unit → Finset Ω) (q₀ : B.DecNode)
    (hq : ∀ q, q ∈ realFiber actEv B () ↔ q = q₀) (a : acts ()) :
    refR2RealObs obs actEv C B () a =
      (∑ ℓ, if (edgeOf B q₀ ℓ).isSome ∧ world B ℓ ∈ obs () then
          leafLawNode B ((NodePolicy.ofProc C B).update q₀ (FinDistr.pure a)) ℓ * payoff B ℓ else 0) /
      (∑ ℓ, if (edgeOf B q₀ ℓ).isSome ∧ world B ℓ ∈ obs () then leafLaw C B ℓ else 0) := by
  unfold refR2RealObs realForcedObs realReachObs
  rw [sum_realFiber_eq_of_unique actEv B q₀ hq, sum_realFiber_eq_of_unique actEv B q₀ hq,
    dif_pos rfl, Finset.sum_filter, Finset.sum_filter]
  unfold leavesBelow
  rw [Finset.sum_filter, Finset.sum_filter]
  congr 1 <;> refine Finset.sum_congr rfl fun ℓ _ => ?_ <;> split_ifs <;> simp_all

end uniqueFiber

/-! ## T1(b): the post-act coin tree -/

section postAct

/-- Post-act-coin worlds `(act, coin)`. Source: `faithful.md` line 22. Kind: D -/
abbrev PostW : Type := Act2 × Bool

/-- **The post-act coin tree**: root `d`, then a fair coin (index `0` = `c = 1`); leaves `(a,1) 2`,
`(a,0) 10`, `(b,1) 4`, `(b,0) 4`.
Source: `cf-workflow/phase2-notes/repair/faithful.md` line 22 (the reviewer's post-act coin tree,
`repair_checks.out` §D); dp-sl-2-058; mandate T1(b)
Kind: D -/
def postAct : Tree PostW Unit (fun _ => Act2) ℚ :=
  .decision () fun act => .chance 2 FinDistr.fair fun i =>
    .leaf (act, decide (i = 0)) (if i = 0 then (if act = .a then 2 else 4) else (if act = .a then 10 else 4))

/-- `O_d = {c = 1}`. Source: `faithful.md` line 22. Kind: D -/
def postObs : Unit → Finset PostW := fun _ => Finset.univ.filter fun w => w.2 = true

/-- The action events `{act = a}`. Source: `faithful.md` line 22. Kind: D -/
def postActEv : (d : Unit) → Act2 → Finset PostW := fun _ a => Finset.univ.filter fun w => w.1 = a

/-- Sums over the leaves of the post-act coin tree. Source: none: infrastructure. Kind: L -/
theorem postAct_sum (f : postAct.Leaves → ℚ) : ∑ ℓ, f ℓ = ∑ act, ∑ i, f ⟨act, ⟨i, ()⟩⟩ := by
  unfold postAct at f ⊢
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun act _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- The root is node-action-veridical. Source: `faithful.md` line 40 (F3′ classification). Kind: L -/
theorem postAct_root_nav : NodeActionVeridical postActEv postAct none := by
  intro ℓ a ha
  rcases ℓ with ⟨act, i, _⟩
  simp only [postAct, edgeOf_decision_none, Option.some.injEq] at ha
  subst ha
  simp [postActEv, postAct, world]

/-- The real fiber is the root alone. Source: none: infrastructure. Kind: L -/
theorem postAct_mem_realFiber (q : postAct.DecNode) :
    q ∈ realFiber postActEv postAct () ↔ q = none := by
  rw [mem_realFiber]
  constructor
  · rintro ⟨-, -⟩
    rcases q with _ | ⟨act, i, e⟩
    · rfl
    · exact e.elim
  · rintro rfl
    exact ⟨rfl, postAct_root_nav⟩

/-- **The post-act coin tree is not F3′**: the root is node-action-veridical but not
subtree-veridical (the leaf `(a, 0)` lies below it with `c = 0 ∉ O_d`).
Source: `faithful.md` line 40 ("node-action-veridical root that is not subtree-veridical: F3
(node-level, without (i)) but not F3′"); mandate T1(b)
Kind: N+ -/
theorem postAct_not_actRecording (C : Proc Unit (fun _ => Act2) ℚ) :
    ¬ ActRecording postObs postActEv C postAct () := by
  intro h
  have := h.1 none rfl postAct_root_nav ⟨.a, ⟨1, ()⟩⟩
    ((mem_leavesBelow postAct none _).mpr (by simp [postAct, edgeOf_decision_none]))
  simp [postObs, postAct, world] at this

/-- **Reading 1 of R2-real on the post-act coin tree is `(6, 4)`** — unconditioned on `O_d`, it
averages the `c = 0` leaves in; it prefers `a`.
Source: `faithful.md` line 22 ("R2-real `= (6,4) → a`"); dp-sl-2-058 reading 1; mandate T1(b)
Kind: N+ -/
theorem postAct_refR2Real (C : Proc Unit (fun _ => Act2) ℚ) :
    refR2Real postActEv C postAct () .a = 6 ∧ refR2Real postActEv C postAct () .b = 4 := by
  rw [refR2Real_eq_of_unique postActEv C postAct none postAct_mem_realFiber,
    refR2Real_eq_of_unique postActEv C postAct none postAct_mem_realFiber]
  unfold postAct
  rw [forcedBelow_decision_none, forcedBelow_decision_none, reach_decision_none]
  unfold valueNode
  rw [sum_leaves_chance, sum_leaves_chance]
  simp [leafLawNode, Fin.sum_univ_two, FinDistr.fair, FinDistr.coin]
  norm_num

/-- **Reading 2 of R2-real on the post-act coin tree is `(2, 4)`** — conditioned on `O_d`, it sees
only the `c = 1` leaves; it prefers `b`. The two readings of dp-sl-2-058 differ here.
Source: `faithful.md` line 22 ("R3 = R1-state `= (2,4) → b`"); dp-sl-2-058 reading 2; mandate T1(b)
Kind: N+ -/
theorem postAct_refR2RealObs (C : Proc Unit (fun _ => Act2) ℚ) :
    refR2RealObs postObs postActEv C postAct () .a = 2 ∧
      refR2RealObs postObs postActEv C postAct () .b = 4 := by
  have hb : (C ()).w .b = 1 - (C ()).w .a := by
    have := (C ()).sum_one; rw [Act2.sum_univ] at this; linarith
  constructor <;>
  · rw [refR2RealObs_eq_of_unique postActEv C postAct postObs none postAct_mem_realFiber,
      postAct_sum, postAct_sum]
    simp [postAct, postObs, world, leafLaw, leafLawNode, NodePolicy.ofProc, NodePolicy.update,
      Fin.sum_univ_two, Act2.sum_univ, FinDistr.fair, FinDistr.coin, edgeOf_decision_none, hb]
    have h2 : (C ()).w Act2.a * 2⁻¹ + (1 - (C ()).w Act2.a) * 2⁻¹ = (2⁻¹ : ℚ) := by ring
    rw [h2]
    norm_num

/-- **R1-state on the post-act coin tree is `(2, 4)`**. Source: `faithful.md` line 22. Kind: N+ -/
theorem postAct_refR1State (C : Proc Unit (fun _ => Act2) ℚ) :
    refR1State postObs C postAct () .a = 2 ∧ refR1State postObs C postAct () .b = 4 := by
  unfold refR1State condExp
  constructor <;>
  · rw [nu_eq_sum, paySum_eq_sum_ite, postAct_sum, postAct_sum]
    simp [postAct, postObs, world, leafLaw, payoff, Fin.sum_univ_two, Act2.sum_univ,
      FinDistr.fair, FinDistr.coin, Proc.deviatePure, Proc.deviate_same] <;> norm_num

/-- **R3 on the post-act coin tree is `(2, 4)`** at every label with both acts positive (the
tremble limit is the strict conditional at positive acts).
Source: `faithful.md` line 22 ("R3 = R1-state `= (2,4)`"); FA-20′(i) ("Under the notes' F3 alone this
is false: post-act coin tree, R2-real `(6,4)` vs R3 `(2,4)`"); mandate T1(b), T5(i)
Kind: N+ -/
theorem postAct_refR3 (q : ℚ) (h0 : 0 < q) (h1 : q < 1) :
    refR3 postObs postActEv (procQ q h0.le h1.le) postAct () .a = 2 ∧
      refR3 postObs postActEv (procQ q h0.le h1.le) postAct () .b = 4 := by
  have hν : ∀ a, nu (procQ q h0.le h1.le) postAct (postActEv () a ∩ postObs ()) =
      (procQ q h0.le h1.le ()).w a / 2 := by
    intro a
    rw [nu_eq_sum, postAct_sum]
    cases a <;> simp [postAct, postObs, postActEv, world, leafLaw, Fin.sum_univ_two, Act2.sum_univ,
      FinDistr.fair, FinDistr.coin, procQ] <;> ring
  have hpay : ∀ a, paySum (procQ q h0.le h1.le) postAct (postActEv () a ∩ postObs ()) =
      (procQ q h0.le h1.le ()).w a / 2 * (if a = .a then 2 else 4) := by
    intro a
    rw [paySum_eq_sum_ite, postAct_sum]
    cases a <;> simp [postAct, postObs, postActEv, world, leafLaw, payoff, Fin.sum_univ_two,
      Act2.sum_univ, FinDistr.fair, FinDistr.coin, procQ] <;> ring
  have hpos : ∀ a, 0 < nu (procQ q h0.le h1.le) postAct (postActEv () a ∩ postObs ()) := by
    intro a; rw [hν]; cases a <;> simp [procQ] <;> linarith
  have hw : ∀ a, (procQ q h0.le h1.le ()).w a / 2 ≠ 0 := fun a => by
    rw [← hν]; exact (hpos a).ne'
  constructor <;>
  · rw [refR3_eq_condExp_of_pos _ _ _ _ (hpos _)]
    unfold condExp
    rw [hν, hpay, mul_div_cancel_left₀ _ (hw _)]
    simp

end postAct

/-! ## T6: tree J, the refutation of "recording for `C`" -/

section treeJ

/-- The root of tree J is node-action-veridical (the leaf-world is the first draw).
Source: `sl-synthesis.md` line 121; `C2.md` line 56 (tree J)
Kind: L -/
theorem treeJ_root_nav : NodeActionVeridical jActEv treeJ none := by
  intro ℓ a ha
  rcases ℓ with ⟨_ | _, ℓ⟩
  · simp only [treeJ, edgeOf_decision_none, Option.some.injEq] at ha
    subst ha
    simp [jActEv, treeJ, world]
  · rcases ℓ with ⟨_ | _, _⟩ <;> simp only [treeJ, edgeOf_decision_none, Option.some.injEq] at ha <;>
      subst ha <;> simp [jActEv, treeJ, world]

/-- Tree J is F3′-structural: the root records the act at every leaf below it, `q₂` is not
node-action-veridical (its `a`-edge leads to `act = b`), and every run passes the root exactly once.
Source: `sl-synthesis.md` line 121; `C2.md` line 56 (tree J)
Kind: L -/
theorem treeJ_actRecordingStructural : ActRecordingStructural jObs jActEv treeJ () := by
  intro C _
  refine ⟨fun q _ _ ℓ _ => by simp [jObs], ?_⟩
  intro ℓ _ _
  refine ⟨none, ⟨?_, treeJ_root_nav⟩, ?_⟩
  · rw [mem_dNodesOn]
    refine ⟨rfl, ?_⟩
    rcases ℓ with ⟨x, ℓ⟩
    simp [treeJ, edgeOf_decision_none]
  · rintro (_ | ⟨_ | _, q⟩) ⟨-, hnav⟩
    · rfl
    · exact q.elim
    · rcases q with _ | ⟨_ | _, q⟩
      · exfalso
        have := hnav ⟨.b, ⟨.a, ()⟩⟩ .a (by simp [treeJ, edgeOf_decision_some, edgeOf_decision_none])
        simp [jActEv, treeJ, world] at this
      · exact q.elim
      · exact q.elim

/-- The action events of tree J are disjoint. Source: none: infrastructure. Kind: L -/
theorem treeJ_actEvDisjoint : ActEvDisjoint jActEv () := by
  intro a b hab
  cases a <;> cases b <;> simp [jActEv] at hab ⊢

/-- The real fiber of tree J is the root. Source: none: infrastructure. Kind: L -/
theorem treeJ_mem_realFiber (q : treeJ.DecNode) : q ∈ realFiber jActEv treeJ () ↔ q = none := by
  rw [mem_realFiber]
  constructor
  · rintro ⟨-, hnav⟩
    rcases q with _ | ⟨_ | _, q⟩
    · rfl
    · exact q.elim
    · rcases q with _ | ⟨_ | _, q⟩
      · exfalso
        have := hnav ⟨.b, ⟨.a, ()⟩⟩ .a (by simp [treeJ, edgeOf_decision_some, edgeOf_decision_none])
        simp [jActEv, treeJ, world] at this
      · exact q.elim
      · exact q.elim
  · rintro rfl
    exact ⟨rfl, treeJ_root_nav⟩

/-- **R2-real on tree J is `(1, 4q)` at label `q`**: forcing at the root leaves `q₂` drawing from
the label.
Source: `C2.md` line 56 ("at a mixed label the common value is `(1, 4q)` — label-dependent");
mandate T6
Kind: N+ -/
theorem treeJ_refR2Real (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    refR2Real jActEv (procQ q h0 h1) treeJ () .a = 1 ∧
      refR2Real jActEv (procQ q h0 h1) treeJ () .b = 4 * q := by
  rw [refR2Real_eq_of_unique jActEv (procQ q h0 h1) treeJ none treeJ_mem_realFiber,
    refR2Real_eq_of_unique jActEv (procQ q h0 h1) treeJ none treeJ_mem_realFiber]
  unfold treeJ
  rw [forcedBelow_decision_none, forcedBelow_decision_none, reach_decision_none]
  simp [valueNode, leafLawNode, NodePolicy.ofProc_restrictDecision, NodePolicy.ofProc_none,
    sum_leaves_decision, Act2.sum_univ, procQ] <;> ring

/-- **R3 on tree J is `(1, 4q)`** (Lemma C2-L3). Source: `C2.md` line 56 ("R3(b) = 4"). Kind: N+ -/
theorem treeJ_refR3 (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    refR3 jObs jActEv (procQ q h0 h1) treeJ () .a = 1 ∧
      refR3 jObs jActEv (procQ q h0 h1) treeJ () .b = 4 * q := by
  have hpos : 0 < nu (procQ q h0 h1) treeJ (jObs ()) := by
    unfold jObs; rw [nu_univ]; exact one_pos
  obtain ⟨e1, e2⟩ := treeJ_refR2Real q h0 h1
  constructor <;> rw [refR3_eq_refR2Real_of_structural jObs jActEv _ _ treeJ_actRecordingStructural
    treeJ_actEvDisjoint hpos]
  · exact e1
  · exact e2

/-- **R1-state on tree J is `(1, 0)`**: the deviation to `b` opens `q₂`, which then draws `b`.
Source: `C2.md` line 56 ("R1-state(b) = 0"); mandate T6
Kind: N+ -/
theorem treeJ_refR1State (C : Proc Unit (fun _ => Act2) ℚ) :
    refR1State jObs C treeJ () .a = 1 ∧ refR1State jObs C treeJ () .b = 0 := by
  unfold refR1State condExp
  constructor <;>
  · rw [nu_eq_sum, paySum_eq_sum_ite]
    unfold treeJ
    simp [sum_leaves_decision, Act2.sum_univ, leafLaw, payoff, world, jObs, Proc.deviatePure,
      Proc.deviate_same]

/-- **Theorem C2-B′ ("recording for `C`" form) is refuted by tree J**. Quoted (`C2.md` line 56):
"under `C[d ↦ a]` the `O_d`-runs are unchanged except for the draw at the recorded node". Reading:
Definition 7 recording for the procedure in play, `δ_a`, gives R1-state = R2-real = R3. Refuted:
tree J at `δ_a` records at `d` for `δ_a` (`dp-core-tree`'s `treeJ_recordsFor_a`) and is F3′-structural,
yet `refR3 b = refR2Real b = 4 ≠ 0 = refR1State b`. Surviving neighbour: the "for every label" form
(`refR1State_eq_refR2Real_of_recordsForAll`, `C2A.lean`), and tree J is not recorded for the
deviation `δ_b` (`treeJ_recordsFor_not_recordsForDeviations`).
Source: `C2.md` line 56 (Theorem C2-B′, WOUNDED form; "Dead 1"); dp-sl-026; dp-sl-073; mandate T6
Kind: N+
Fidelity: exact -/
theorem treeJ_c2B_refuted :
    RecordsFor jObs jActEv (procQ 1 (by norm_num) (by norm_num)) treeJ () ∧
    ActRecordingStructural jObs jActEv treeJ () ∧
    refR3 jObs jActEv (procQ 1 (by norm_num) (by norm_num)) treeJ () .b = 4 ∧
    refR2Real jActEv (procQ 1 (by norm_num) (by norm_num)) treeJ () .b = 4 ∧
    refR1State jObs (procQ 1 (by norm_num) (by norm_num)) treeJ () .b = 0 := by
  refine ⟨treeJ_recordsFor_a, treeJ_actRecordingStructural, ?_, ?_,
    (treeJ_refR1State _).2⟩
  · rw [(treeJ_refR3 1 (by norm_num) (by norm_num)).2]; norm_num
  · rw [(treeJ_refR2Real 1 (by norm_num) (by norm_num)).2]; norm_num

/-- **The forced mixed label on tree J**: with the strict state of `procQ q`, `T_EDT`(R3-extended)
approves `procQ q` iff `q = 1/4` — the unique calibrated-and-approved label is properly mixed, and
`δ_a` is not approved (`refR3 b = 4 > 1 = evStrict a`).
Source: `C2.md` line 56 ("MSR = {q = 1/4}, a forced mixed label, with `δ_a` not approved (`4 > 1`)");
mandate T6
Kind: N+ -/
theorem treeJ_forced_mixed_label (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    let s : Unit → State JW ℚ := fun _ =>
      calibratedState (procQ q h0 h1) treeJ (jObs ()) (by unfold jObs; rw [nu_univ]; exact one_pos)
    TEdtExtAt s jObs jActEv (procQ q h0 h1) treeJ () ↔ q = 1/4 := by
  intro s
  have hpos : 0 < nu (procQ q h0 h1) treeJ (jObs ()) := by
    unfold jObs; rw [nu_univ]; exact one_pos
  have hs : StrictOCAt s jObs (procQ q h0 h1) treeJ () :=
    strictOCAt_calibratedState jObs _ treeJ s () hpos rfl
  obtain ⟨e1, e2⟩ := treeJ_refR2Real q h0 h1
  unfold TEdtExtAt
  simp only [evExt_eq_refR2Real s jObs jActEv _ treeJ treeJ_actRecordingStructural
    treeJ_actEvDisjoint hpos hs]
  constructor
  · intro h
    by_cases hq : 0 < q
    · have := h .a (by simp [procQ, hq]) .b
      rw [e1, e2] at this
      by_cases hq1 : q < 1
      · have := h .b (by simp [procQ]; linarith) .a
        rw [e1, e2] at this
        linarith
      · have : q = 1 := le_antisymm h1 (not_lt.mp hq1)
        subst this
        norm_num at *
    · have : q = 0 := le_antisymm (not_lt.mp hq) h0
      subst this
      have := h .b (by simp [procQ]) .a
      rw [e1, e2] at this
      norm_num at this
  · rintro rfl a _ b
    cases a <;> cases b <;> simp [e1, e2] <;> norm_num

end treeJ

/-! ## T4: the AMD under last-draw act events, and the selection tree -/

section amdLast

/-- Sums over the leaves of the AMD. Source: none: infrastructure. Kind: L -/
theorem amd_sum' (f : amd.Leaves → ℚ) :
    ∑ ℓ, f ℓ = f ⟨.a, ()⟩ + (f ⟨.b, ⟨.a, ()⟩⟩ + f ⟨.b, ⟨.b, ()⟩⟩) := by
  unfold amd at f ⊢
  rw [sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, sum_leaves_decision, Act2.sum_univ,
    Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]

/-- **The AMD is not F3′ under last-draw act events** for any label with `C(d)(a) > 0`: the leaf
`sa` (first draw `a`) is a positive `O_d`-run whose only `d`-node, the root, is not
node-action-veridical (`sba` lies below its `b`-edge with `seq ∈ {a, ba}`).
Source: `C2.md` C2-4′ ("F3′ for EV = R2-real: AMD last-draw"); dp-sl-032; mandate T4
Kind: N+ -/
theorem amdLast_not_actRecording (q : ℚ) (h0 : 0 < q) (h1 : q ≤ 1) :
    ¬ ActRecording amdObs amdActEvLast (procQ q h0.le h1) amd () := by
  intro h
  obtain ⟨q₀, ⟨hq₀, hnav⟩, -⟩ := h.2 ⟨.a, ()⟩ (by simp [amd, leafLaw, procQ, h0]) (by simp [amdObs])
  rw [mem_dNodesOn] at hq₀
  rcases q₀ with _ | ⟨_ | _, q₀⟩
  · have := hnav ⟨.b, ⟨.a, ()⟩⟩ .b (by simp [amd, edgeOf_decision_none])
    simp [amdActEvLast, amd, world] at this
  · exact q₀.elim
  · rcases q₀ with _ | ⟨_ | _, q₀⟩
    · simp [amd, edgeOf_decision_some] at hq₀
    · exact q₀.elim
    · exact q₀.elim

/-- The second `d`-node of the AMD is node-action-veridical under last-draw events, and the real
fiber is that node alone.
Source: `C2.md` C2-4′; mandate T4
Kind: L -/
theorem amdLast_mem_realFiber (q : amd.DecNode) :
    q ∈ realFiber amdActEvLast amd () ↔ q = some ⟨.b, none⟩ := by
  rw [mem_realFiber]
  constructor
  · rintro ⟨-, hnav⟩
    rcases q with _ | ⟨_ | _, q⟩
    · exfalso
      have := hnav ⟨.b, ⟨.a, ()⟩⟩ .b (by simp [amd, edgeOf_decision_none])
      simp [amdActEvLast, amd, world] at this
    · exact q.elim
    · rcases q with _ | ⟨_ | _, q⟩
      · rfl
      · exact q.elim
      · exact q.elim
  · rintro rfl
    refine ⟨rfl, fun ℓ a ha => ?_⟩
    rcases ℓ with ⟨_ | _, ℓ⟩
    · simp [amd, edgeOf_decision_some] at ha
    · rcases ℓ with ⟨_ | _, ℓ⟩ <;> simp [amd, edgeOf_decision_some, edgeOf_decision_none] at ha <;>
        subst ha <;> simp [amdActEvLast, amd, world]

/-- **R2-real on the AMD under last-draw events is `(4, 1)`** at every label `q < 1` (forcing at the
second node).
Source: `C2.md` C2-4′ ("AMD last-draw: `4(1−q)/(2−q)` vs `4`"); mandate T4
Kind: N+ -/
theorem amdLast_refR2Real (q : ℚ) (h0 : 0 ≤ q) (h1 : q < 1) :
    refR2Real amdActEvLast (procQ q h0 h1.le) amd () .a = 4 ∧
      refR2Real amdActEvLast (procQ q h0 h1.le) amd () .b = 1 := by
  rw [refR2Real_eq_of_unique amdActEvLast (procQ q h0 h1.le) amd _ amdLast_mem_realFiber,
    refR2Real_eq_of_unique amdActEvLast (procQ q h0 h1.le) amd _ amdLast_mem_realFiber]
  unfold amd
  rw [forcedBelow_decision_some, forcedBelow_decision_some, reach_decision_some,
    NodePolicy.ofProc_none, NodePolicy.ofProc_restrictDecision, forcedBelow_decision_none,
    forcedBelow_decision_none, reach_decision_none]
  simp [valueNode, leafLawNode, procQ]
  have : (1 - q) ≠ 0 := by linarith
  constructor <;> field_simp <;> exact this

/-- **The strict evidential value of `a` on the AMD under last-draw events is `4(1−q)/(2−q)`**, which
differs from `refR2Real a = 4` at every `0 < q < 1`: F3′ is necessary for C2-A′ (i).
Source: `C2.md` C2-4′ ("AMD last-draw: `4(1−q)/(2−q)` vs `4`"); dp-sl-032; dp-sl-2-067; mandate T4
Kind: N+ -/
theorem amdLast_evStrict_ne (q : ℚ) (h0 : 0 < q) (h1 : q < 1) :
    let s : Unit → State AmdW ℚ := fun _ =>
      calibratedState (procQ q h0.le h1.le) amd (amdObs ()) (by unfold amdObs; rw [nu_univ]; exact one_pos)
    evStrict s amdActEvLast () .a = 4 * (1 - q) / (2 - q) ∧
      evStrict s amdActEvLast () .a ≠ refR2Real amdActEvLast (procQ q h0.le h1.le) amd () .a := by
  intro s
  have hν : nu (procQ q h0.le h1.le) amd (amdActEvLast () .a) = q * (2 - q) := by
    rw [nu_eq_sum, amd_sum']
    simp [amd, leafLaw, world, amdActEvLast, procQ]
    ring
  have hp : paySum (procQ q h0.le h1.le) amd (amdActEvLast () .a) = 4 * (1 - q) * q := by
    rw [paySum_eq_sum_ite, amd_sum']
    simp [amd, leafLaw, payoff, world, amdActEvLast, procQ]
    ring
  have h2 : (2 - q) ≠ 0 := by linarith
  have hV : evStrict s amdActEvLast () .a = 4 * (1 - q) / (2 - q) := by
    unfold evStrict
    simp only [s, calibratedState_V, amdObs, Finset.inter_univ, hν, hp]
    rw [div_eq_div_iff (by positivity) h2]
    ring
  refine ⟨hV, ?_⟩
  rw [hV, (amdLast_refR2Real q h0.le h1).1]
  intro h
  rw [div_eq_iff h2] at h
  linarith

end amdLast

section selection

/-- **The selection tree is not F3′**: the fake-`a` leaf is a positive `O_d`-run passing no `d`-node.
Source: `C2.md` C2-4′ ("`S_sel`: `7/11` vs indifference"); P05-13′ ("`S_sel` lies outside its
hypotheses"); mandate T4
Kind: N+ -/
theorem sel_not_actRecording (C : Proc Unit (fun _ => Act2) ℚ) :
    ¬ ActRecording selObs selActEv C selTree () := by
  intro h
  obtain ⟨q₀, ⟨hq₀, -⟩, -⟩ := h.2 ⟨1, ()⟩ (by simp [selTree, selectionForcing, leafLaw,
    FinDistr.third]) (by simp [selObs])
  rw [mem_dNodesOn] at hq₀
  rcases q₀ with ⟨i, q₀⟩
  fin_cases i
  · rcases q₀ with _ | ⟨_ | _, q₀⟩
    · simp [selTree, selectionForcing, edgeOf_chance] at hq₀
    · exact q₀.elim
    · exact q₀.elim
  · exact q₀.elim
  · exact q₀.elim

/-- The real fiber of the selection tree is its one real node.
Source: none: infrastructure. Kind: L -/
theorem sel_mem_realFiber (q : selTree.DecNode) :
    q ∈ realFiber selActEv selTree () ↔ q = ⟨0, none⟩ := by
  rw [mem_realFiber]
  constructor
  · rintro ⟨-, -⟩
    rcases q with ⟨i, q⟩
    fin_cases i
    · rcases q with _ | ⟨_ | _, q⟩
      · rfl
      · exact q.elim
      · exact q.elim
    · exact q.elim
    · exact q.elim
  · rintro rfl
    refine ⟨rfl, fun ℓ a ha => ?_⟩
    rcases ℓ with ⟨i, ℓ⟩
    fin_cases i
    · rcases ℓ with ⟨_ | _, ℓ⟩ <;>
        simp [selTree, selectionForcing, edgeOf_chance, edgeOf_decision_none] at ha <;>
        subst ha <;> simp [selActEv, selTree, selectionForcing, world]
    · simp [selTree, selectionForcing, edgeOf_chance] at ha
    · simp [selTree, selectionForcing, edgeOf_chance] at ha

/-- **R2-real on the selection tree is `(−20, −20)`** — indifference, against the strict values'
tie at `7/11`.
Source: `C2.md` C2-4′ ("`S_sel`: `7/11` vs indifference"); mandate T4
Kind: N+ -/
theorem sel_refR2Real (C : Proc Unit (fun _ => Act2) ℚ) :
    refR2Real selActEv C selTree () .a = -20 ∧ refR2Real selActEv C selTree () .b = -20 := by
  rw [refR2Real_eq_of_unique selActEv C selTree _ sel_mem_realFiber,
    refR2Real_eq_of_unique selActEv C selTree _ sel_mem_realFiber]
  unfold selTree selectionForcing
  rw [forcedBelow_chance, forcedBelow_chance, reach_chance, NodePolicy.ofProc_restrictChance]
  simp [forcedBelow_decision_none, reach_decision_none, valueNode, leafLawNode, FinDistr.third] <;>
    norm_num

/-- **`S_sel`'s strict values tie at `q = 7/11` with common value `−5/3`**: a witness *outside*
C2-A′'s hypotheses (a selection node is not F3′), not a refutation of P05's Theorem 1.
Source: `C2.md` C2-4′; P05-13′ (the retraction); `dp-calibration`'s `selState_V`; mandate T4
Kind: N+ -/
theorem sel_tie :
    (selState (7/11) (by norm_num) (by norm_num)).V (selActEv () .a) = -5/3 ∧
      (selState (7/11) (by norm_num) (by norm_num)).V (selActEv () .b) = -5/3 := by
  obtain ⟨ha, hb⟩ := selState_V (7/11) (by norm_num) (by norm_num)
  rw [ha, hb]; norm_num

end selection

end Cleanroom.Decision.DpReferentsCdt

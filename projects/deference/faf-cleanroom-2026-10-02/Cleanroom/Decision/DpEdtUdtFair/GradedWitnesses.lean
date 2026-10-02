import Cleanroom.Decision.DpEdtUdtFair.Graded
import Cleanroom.Decision.DpEdtUdtFair.Trees
import Cleanroom.Decision.DpCalibration.Mugging
import Cleanroom.Decision.DpCalibration.Chain
import Cleanroom.Decision.DpCalibration.MiniDevices
import Cleanroom.Decision.DpFairnessReloc.TopRepair

/-!
# The graded theorem's witnesses (T9): the mugging (`D = x + y`) and the reviewer tree

* **Counterfactual Mugging `mug1 x y` with `refuse`** (N+, `D > 0`): almost fair, `FRec`
  (`mug1_recordsForAll`, for every procedure), pruned, realized, fiber value-disagreement exactly
  `x + y` (live `pay → −x`, predictor `pay → y`), `refuse` D2-consistent (`𝔼_ε[r ∣ pay ∧ O_T] = −x ≤
  0 = 𝔼_ε[r ∣ refuse ∧ O_T]`); the graded bound gives every procedure at most
  `V(refuse) + 2 · 1 · (x + y)`, while the actual loss is `(y − x)/2`.
* **T16(b)** (`frec_not_subtreeVeridical_refuted`): `B₁` records for every procedure while its
  `H`-node is not subtree-veridical — "FRec ⟹ subtree-veridicality of every node" is false (A.2).
* **The reviewer tree `revTree 1 (1/10)`** (refutation of the constant-1 single-fiber
  sharpening, T9(c)): `δ_a` is D2-consistent, the fiber disagreement is `11/10`, the loss is
  `19/20`, and `19/20 > (∑_{sim} R_q) · D_V = ½ · 11/10 = 11/20` — the sharpening with constant `1`
  fails; the constant-2 form (`11/10 ≥ 19/20`) and the graded bound `2 · 1 · 11/10` hold.
-/

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace Cleanroom.Decision.DpEdtUdtFair

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt
open Cleanroom.Decision.DpCalibration

/-! ### The mugging -/

section mugging

variable (x y : ℚ)

/-- `B₁` records at its point for **every** procedure (the proof of `dp-core-tree`'s
`mug1_recordsFor`, which never read the procedure).
Source: [[decision-problems-v2]] Proposition 6; `adversary-repair.md` A.2 ("records at its only
point for *every* procedure")
Kind: N+ -/
theorem mug1_recordsForAll : RecordsForAll mugObs mugActEv (mug1 x y) () := by
  intro C ℓ _ hobs
  unfold mug1 at ℓ hobs ⊢
  rcases ℓ with ⟨i, act, _⟩
  refine ⟨rfl, ?_⟩
  rintro ⟨i', (_ | ⟨b, q⟩)⟩ hq a ha
  · by_cases hi : i = i'
    · subst hi
      simp only [edgeOf_chance, dite_true, edgeOf_decision_none, Option.some.injEq] at ha
      subst ha
      fin_cases i
      · refine ⟨?_, ?_, ?_⟩
        · rintro ⟨j, b, _⟩ hj
          rw [mem_leavesBelow] at hj
          by_cases hj0 : j = 0
          · subst hj0; cases b <;> simp [mugObs, mugWorld1]
          · simp [edgeOf_chance, hj0] at hj
        · cases act <;> simp [mugActEv, mugWorld1]
        · intro a' ha'; cases act <;> cases a' <;> simp_all [mugActEv, mugWorld1, mugObs]
      · exfalso
        cases act <;> simp [mugObs, mugWorld1] at hobs
    · simp [edgeOf_chance, hi] at ha
  · exact q.elim

/-- `B₁` is pruned and `O_T` is realized: with `FRec`, the three non-fairness clauses.
Source: [[decision-problems-v2]] Proposition 6
Kind: L -/
theorem mug1_frecPR : FRecPR mugObs mugActEv (mug1 x y) where
  frec := fun d _ => by cases d; exact mug1_recordsForAll x y
  pruned := by
    rintro ⟨i, act, _⟩
    unfold Positive mug1
    fin_cases i <;> simp [chanceWeight_chance, chanceWeight_decision, chanceWeight_leaf,
      FinDistr.fair, FinDistr.coin] <;> norm_num
  realized := fun d _ => by
    cases d
    exact ⟨⟨0, .a, ()⟩, by simp [Positive, mug1, chanceWeight_chance, chanceWeight_decision,
      chanceWeight_leaf, FinDistr.fair, FinDistr.coin], by simp [mugObs, mug1, mugWorld1]⟩

/-- Every decision node of `B₁` is the `i`-th copy, `i ∈ {T, H}`.
Source: none: infrastructure
Kind: L -/
theorem mug1_subtree (q : (mug1 x y).DecNode) :
    ∃ i : Fin 2, subtreeAt (mug1 x y) q =
      .decision () fun act => .leaf (mugWorld1 i act) (mugPay x y (mugWorld1 i act)) := by
  obtain ⟨i, q⟩ := q
  rcases q with _ | ⟨b, q'⟩
  · exact ⟨i, rfl⟩
  · exact q'.elim

/-- **The fiber value-disagreement of `B₁` is at most `x + y`** for every procedure (the two
members' children are leaves: `pay → −x` at `T`, `pay → y` at `H`, `refuse → 0` at both).
Source: `grounding.md` GR-10 (the mugging's `D_V`); mandate T9 ("`FiberValueBound = x + y`")
Kind: N+ -/
theorem mug1_fiberValueBound (hx : 0 ≤ x) (hy : 0 ≤ y) (C : Proc Unit (fun _ => Act2) ℚ) :
    FiberValueBound C (mug1 x y) (x + y) := by
  intro d q q' c c' hc hc' a
  obtain ⟨i, hi⟩ := mug1_subtree x y q
  obtain ⟨i', hi'⟩ := mug1_subtree x y q'
  cases d
  rw [hi] at hc; rw [hi'] at hc'
  simp only [Tree.decision.injEq, heq_eq_eq, true_and] at hc hc'
  subst hc; subst hc'
  fin_cases i <;> fin_cases i' <;> cases a <;>
    simp [mugWorld1, mugPay, DpLocalOpt.value_leaf] <;>
    first | (rw [abs_le]; constructor <;> linarith) | linarith | norm_num

/-- `refuse` is `procQ 0`. Source: none: infrastructure. Kind: L -/
theorem refuse_eq_procQ :
    (Proc.ofFun fun _ => Act2.b : Proc Unit (fun _ => Act2) ℚ) = procQ 0 le_rfl zero_le_one := by
  funext d; apply FinDistr.ext'; intro a; cases a <;> simp [Proc.ofFun, procQ, FinDistr.act2]

/-- **`refuse` is event-tremble-EDT-consistent on `B₁`** for `x ≥ 0`: under `C^ε`,
`𝔼_ε[r ∣ pay ∧ O_T] = −x ≤ 0 = 𝔼_ε[r ∣ refuse ∧ O_T]`.
Source: `calibration.md` CA-20′ (the mugging column: D2 refuses); mandate T9
Kind: N+ -/
theorem mug1_refuse_eventTremble (hx : 0 ≤ x) :
    EventTrembleEdtConsistent mugObs mugActEv (Proc.ofFun fun _ => Act2.b) (mug1 x y) := by
  refine ⟨1, one_pos, fun ε h0 h1 _ d _ _ _ a ha => ?_⟩
  cases d
  rw [refuse_eq_procQ, tremble_procQ]
  cases a <;> simp [Proc.ofFun_w] at ha
  set q := (1 - ε) * 0 + ε / 2 with hq
  have hq0 : 0 < q := by rw [hq]; linarith
  have hq1 : q < 1 := by rw [hq]; linarith
  refine ⟨?_, fun b _ => ?_⟩
  · rw [mug1_nu]; simp [mugObs, mugActEv, procQ]; linarith
  · cases b
    · unfold condExp
      rw [mug1_nu, mug1_nu, mug1_paySum, mug1_paySum]
      simp [mugObs, mugActEv, procQ]
      first
        | (rw [zero_div]; apply div_nonpos_of_nonpos_of_nonneg <;> nlinarith)
        | (apply div_nonpos_of_nonpos_of_nonneg <;> nlinarith)
        | nlinarith
    · exact le_rfl

/-- `decDepth (mug1 x y) = 1`. Source: none: infrastructure. Kind: L -/
theorem mug1_decDepth : decDepth (mug1 x y) = 1 := by
  simp only [mug1, decDepth_chance, decDepth_decision, decDepth_leaf]
  rw [Finset.sup_const Finset.univ_nonempty, Finset.sup_const Finset.univ_nonempty]

/-- **T9's N+ witness with `D > 0`**: on the mugging with `0 ≤ x ≤ y`, every hypothesis of the
graded theorem holds for `refuse` with `D = x + y` (almost fair, `FRec`, pruned, realized, fiber
disagreement `x + y` at every tremble, D2-consistent), so `V(C') ≤ V(refuse) + 2 · 1 · (x + y)`
for every `C'`; the actual loss is `V(pay) − V(refuse) = (y − x)/2` (and `V(refuse) = 0`).
Source: `grounding.md` GR-10 ("the mugging: `D_V = x + y`"); mandate T9 ("loss `½(y − x) ≤ 2(x + y)`")
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem mug1_graded_witness (hx : 0 ≤ x) (hy : 0 ≤ y) :
    AlmostFair (mug1 x y) ∧ FRecPR mugObs mugActEv (mug1 x y) ∧
    EventTrembleEdtConsistent mugObs mugActEv (Proc.ofFun fun _ => Act2.b) (mug1 x y) ∧
    (∀ C', value C' (mug1 x y) ≤
      value (Proc.ofFun fun _ => Act2.b) (mug1 x y) + 2 * (decDepth (mug1 x y) : ℚ) * (x + y)) ∧
    value (Proc.ofFun fun _ => Act2.b) (mug1 x y) = 0 ∧
    value (Proc.ofFun fun _ => Act2.a) (mug1 x y) = (y - x) / 2 := by
  refine ⟨mug1_almostFair x y, mug1_frecPR x y, mug1_refuse_eventTremble x y hx, ?_,
    mug1_value_refuse x y, mug1_value_pay x y⟩
  exact graded_fr11 (mug1_almostFair x y) (mug1_frecPR x y) (by linarith) one_pos
    (fun ε h0 h1 _ => mug1_fiberValueBound x y hx hy _) (mug1_refuse_eventTremble x y hx)

/-- **T9's witness pinned at `(x, y) = (1, 3)`** so that the N+ grade is a theorem and not a
property of a family: `D = 4 > 0`, `V(refuse) = 0`, `V(pay) = 1`, `refuse` is D2-consistent and
**not** optimal — the graded bound `V(C') ≤ 0 + 2 · 1 · 4` holds with the real loss `1`. (On this
depth-1 tree the bound's slack `8` exceeds the payoff range `[−½, 3/2]`, so the bound does not bite
here; see the ledger.)
Source: `grounding.md` GR-10; audit round 1 (N6/NB1)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem mug1_graded_witness_13 :
    AlmostFair (mug1 1 3) ∧ FRecPR mugObs mugActEv (mug1 1 3) ∧
    EventTrembleEdtConsistent mugObs mugActEv (Proc.ofFun fun _ => Act2.b) (mug1 1 3) ∧
    (∀ C', value C' (mug1 1 3) ≤
      value (Proc.ofFun fun _ => Act2.b) (mug1 1 3) + 2 * (decDepth (mug1 1 3) : ℚ) * (1 + 3)) ∧
    value (Proc.ofFun fun _ => Act2.b) (mug1 1 3) = 0 ∧
    value (Proc.ofFun fun _ => Act2.a) (mug1 1 3) = 1 ∧
    ¬ IsOptimal (Proc.ofFun fun _ => Act2.b) (mug1 1 3) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := mug1_graded_witness 1 3 (by norm_num) (by norm_num)
  refine ⟨h1, h2, h3, h4, h5, by rw [h6]; norm_num, fun h => ?_⟩
  have := h (Proc.ofFun fun _ => Act2.a)
  rw [h5, h6] at this
  norm_num at this

/-! ### T16(b): `FRec` does not make every decision node subtree-veridical -/

/-- **The `H`-node of `B₁` is not subtree-veridical**: its leaves carry the worlds `hOne`, `hZero`,
outside `O_T = {tPay, tRefuse}`.
Source: `adversary-repair.md` A.2 ("the `H`-node is not subtree-veridical")
Kind: N+ -/
theorem mug1_H_not_subtreeVeridical : ¬ SubtreeVeridical mugObs (mug1 x y) ⟨1, none⟩ := by
  intro h
  have := h ⟨1, .a, ()⟩ ((mem_leavesBelow _ _ _).mpr
    (by simp [mug1, edgeOf_chance, edgeOf_decision_none]))
  simp [mug1, mugObs, mugWorld1, world_chance, world_decision, world_leaf] at this

/-- **"FRec ⟹ subtree-veridicality of every decision node" is false (T16(b), refuted row)**.
Quoted (`fair-repair.md` §1.1, struck by A.2): recording at `d` was taken to make *every*
`d`-node subtree-veridical. Reading: `RecordsForAll` at `d` implies `SubtreeVeridical` at every
`d`-node. Witness: `B₁` records at its only point for **every** procedure
(`mug1_recordsForAll`) while its `H`-node is not subtree-veridical. Surviving neighbour:
`FairClass.subtreeVeridical` — on `𝔉` the fiber isomorphism (not recording alone) carries
subtree-veridicality from the recorded node to the whole fiber.
Source: `fair-repair.md` §1.1 via `adversary-repair.md` A.2; dp-cf-2-062 (N3); mandate T16(b)
Kind: N+ (refutation instance)
Fidelity: exact
Hyps: (a) all -/
theorem frec_not_subtreeVeridical_refuted :
    RecordsForAll mugObs mugActEv (mug1 x y) () ∧
    ∃ q : (mug1 x y).DecNode, pt (mug1 x y) q = () ∧ ¬ SubtreeVeridical mugObs (mug1 x y) q :=
  ⟨mug1_recordsForAll x y, ⟨1, none⟩, rfl, mug1_H_not_subtreeVeridical x y⟩

end mugging

end Cleanroom.Decision.DpEdtUdtFair

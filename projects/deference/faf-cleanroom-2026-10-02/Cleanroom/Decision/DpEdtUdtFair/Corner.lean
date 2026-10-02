import Cleanroom.Decision.DpEdtUdtFair.Graded
import Cleanroom.Decision.DpEdtUdtFair.Trees
import Cleanroom.Decision.DpCalibration.MiniDevices

/-!
# GR-11's corner is strictly larger than `𝔉` (T1(c)), and the corner corollary is inhabited

`cornerTree` (GR-9's example (2) with act-recording, evented worlds): value-fair, almost fair,
`FRec` (`O = ⊤`), pruned, realized — in the corner — and **not strongly fair** (its two `d`-nodes
have non-isomorphic subtrees: one has a chance node under `a`). On it `δ_a` is event-tremble-EDT-
consistent (`𝔼_ε[r ∣ act = a] = 2 > 0 = 𝔼_ε[r ∣ act = b]`) and, by the corner corollary
(`corner_eventTrembleEdt_isOptimal`, the graded theorem at `D = 0`), optimal (`V = 2`).
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

/-- Every decision node of `cornerTree` has subtree `cornerL` or `cornerR`.
Source: none: infrastructure
Kind: L -/
theorem cornerTree_subtree (q : cornerTree.DecNode) :
    subtreeAt cornerTree q = cornerL ∨ subtreeAt cornerTree q = cornerR := by
  obtain ⟨i, q⟩ := q
  fin_cases i
  · left
    change subtreeAt cornerL q = cornerL
    rcases q with _ | ⟨x, q'⟩
    · rfl
    · cases x
      · obtain ⟨j, q''⟩ := q'; exact q''.elim
      · exact q'.elim
  · right
    change subtreeAt cornerR q = cornerR
    rcases q with _ | ⟨x, q'⟩
    · rfl
    · cases x <;> exact q'.elim

/-- The two members' act values agree: `2` under `a`, `0` under `b`, for every procedure.
Source: `grounding.md` GR-9 example (2) ("`D_V = 0`")
Kind: L -/
theorem cornerL_value_eq (C : Proc Unit (fun _ => Act2) ℚ) (a : Act2) :
    value (C.deviatePure () a) cornerL = value (C.deviatePure () a) cornerR := by
  cases a <;>
    simp [cornerL, cornerR, value_decision, value_chance, value_leaf, Fin.sum_univ_two,
      Act2.sum_univ, Proc.deviatePure, Proc.deviate_same, FinDistr.pure_w, FinDistr.fair,
      FinDistr.coin] <;> norm_num

/-- `cornerTree` is value-fair.
Source: `grounding.md` GR-9 example (2) ("`is_strongly_fair` False, laws differ, `D_V = 0`")
Kind: N+ -/
theorem cornerTree_valueFair : ValueFair cornerTree := by
  intro d q _ q' _ C a
  cases d
  rcases cornerTree_subtree q with h | h <;> rcases cornerTree_subtree q' with h' | h' <;> rw [h, h']
  · exact cornerL_value_eq C a
  · exact (cornerL_value_eq C a).symm

/-- `cornerTree` is not strongly fair: `cornerL ≇ cornerR` (a chance node against a leaf under
`a`).
Source: `grounding.md` GR-9 example (2), GR-11
Kind: N+ -/
theorem cornerTree_not_stronglyFair : ¬ StronglyFair cornerTree := by
  intro h
  have := h () ⟨0, none⟩ ((mem_fiber _ _ _).mpr rfl) ⟨1, none⟩ ((mem_fiber _ _ _).mpr rfl)
  change LabIso cornerL cornerR at this
  unfold cornerL cornerR at this
  cases this with
  | decision _ _ _ hchild =>
    have h' := hchild .a
    exact absurd h' (fun h'' => by cases h'')

/-- `cornerTree` is almost fair (each path meets `d` once).
Source: none: infrastructure
Kind: L -/
theorem cornerTree_almostFair : AlmostFair cornerTree := by
  rintro d ⟨i, ℓ⟩
  fin_cases i
  · change count d cornerL ℓ ≤ 1
    rcases ℓ with ⟨x, ℓ⟩
    cases x
    · obtain ⟨j, _⟩ := ℓ; simp [cornerL, count_decision, count_chance, count_leaf]
    · simp [cornerL, count_decision, count_leaf]
  · change count d cornerR ℓ ≤ 1
    rcases ℓ with ⟨x, _⟩
    cases x <;> simp [cornerR, count_decision, count_leaf]

/-- `cornerTree` records at its point for every procedure (`O = ⊤`; the world records the act).
Source: `grounding.md` GR-11 (the corner's `FRec` clause)
Kind: N+ -/
theorem cornerTree_recordsForAll : RecordsForAll cornerObs cornerActEv cornerTree () := by
  intro C ℓ _ _
  obtain ⟨i, ℓ⟩ := ℓ
  refine ⟨?_, ?_⟩
  · fin_cases i
    · change count () cornerL ℓ = 1
      rcases ℓ with ⟨x, ℓ⟩
      cases x
      · obtain ⟨j, _⟩ := ℓ; simp [cornerL, count_decision, count_chance, count_leaf]
      · simp [cornerL, count_decision, count_leaf]
    · change count () cornerR ℓ = 1
      rcases ℓ with ⟨x, _⟩
      cases x <;> simp [cornerR, count_decision, count_leaf]
  · rintro ⟨i', q⟩ hq a ha
    fin_cases i <;> fin_cases i'
    · rcases q with _ | ⟨x, q'⟩
      · change edgeOf cornerL none ℓ = some a at ha
        rcases ℓ with ⟨x, ℓ⟩
        simp only [cornerL, edgeOf_decision_none, Option.some.injEq] at ha
        subst ha
        refine ⟨fun _ _ => by simp [cornerObs], ?_, ?_⟩
        · cases x
          · obtain ⟨j, _⟩ := ℓ
            fin_cases j <;> simp [cornerActEv, cornerTree, cornerL, world_chance, world_decision, world_leaf]
          · simp [cornerActEv, cornerTree, cornerL, world_chance, world_decision, world_leaf]
        · intro a' ha'
          cases x
          · obtain ⟨j, _⟩ := ℓ
            fin_cases j <;> cases a' <;>
              simp [cornerActEv, cornerTree, cornerL, world_chance, world_decision, world_leaf] at ha' ⊢
          · cases a' <;> simp [cornerActEv, cornerTree, cornerL, world_chance, world_decision, world_leaf] at ha' ⊢
      · cases x
        · obtain ⟨j, q''⟩ := q'; exact q''.elim
        · exact q'.elim
    · change edgeOf cornerTree ⟨1, q⟩ ⟨0, ℓ⟩ = some a at ha
      unfold cornerTree at ha
      simp [edgeOf_chance] at ha
    · change edgeOf cornerTree ⟨0, q⟩ ⟨1, ℓ⟩ = some a at ha
      unfold cornerTree at ha
      simp [edgeOf_chance] at ha
    · rcases q with _ | ⟨x, q'⟩
      · change edgeOf cornerR none ℓ = some a at ha
        rcases ℓ with ⟨x, _⟩
        simp only [cornerR, edgeOf_decision_none, Option.some.injEq] at ha
        subst ha
        refine ⟨fun _ _ => by simp [cornerObs], ?_, ?_⟩
        · cases x
          · change (false, Act2.a) ∈ cornerActEv () Act2.a; simp [cornerActEv]
          · change (false, Act2.b) ∈ cornerActEv () Act2.b; simp [cornerActEv]
        · intro a' ha'
          cases x
          · change (false, Act2.a) ∈ cornerActEv () a' at ha'
            cases a' <;> simp [cornerActEv] at ha' ⊢
          · change (false, Act2.b) ∈ cornerActEv () a' at ha'
            cases a' <;> simp [cornerActEv] at ha' ⊢
      · cases x <;> exact q'.elim

/-- `cornerTree` is pruned and its observation is realized.
Source: none: infrastructure
Kind: L -/
theorem cornerTree_pruned_realized :
    Pruned cornerTree ∧ ∀ d ∈ queried cornerTree, Realized cornerObs cornerTree d := by
  refine ⟨?_, fun d _ => ?_⟩
  · rintro ⟨i, ℓ⟩
    fin_cases i
    · change 0 < FinDistr.fair.w 0 * chanceWeight cornerL ℓ
      rcases ℓ with ⟨x, ℓ⟩
      cases x
      · obtain ⟨j, _⟩ := ℓ
        fin_cases j <;> simp [cornerL, chanceWeight_decision, chanceWeight_chance, chanceWeight_leaf,
          FinDistr.fair, FinDistr.coin] <;> norm_num
      · simp [cornerL, chanceWeight_decision, chanceWeight_leaf, FinDistr.fair, FinDistr.coin]
    · change 0 < FinDistr.fair.w 1 * chanceWeight cornerR ℓ
      rcases ℓ with ⟨x, _⟩
      cases x <;> simp [cornerR, chanceWeight_decision, chanceWeight_leaf, FinDistr.fair,
        FinDistr.coin] <;> norm_num
  · refine ⟨⟨1, .a, ()⟩, ?_, by simp [cornerObs]⟩
    change 0 < FinDistr.fair.w 1 * chanceWeight cornerR ⟨.a, ()⟩
    simp [cornerR, chanceWeight_decision, chanceWeight_leaf, FinDistr.fair, FinDistr.coin]; norm_num

/-- **GR-11 (a), the strict inclusion**: `cornerTree` is in the corner and not strongly fair.
Source: `grounding.md` GR-11 ("example (2) lies in the corner and outside phase 1's class")
Kind: N+
Fidelity: exact (act-recording worlds added so that `FRec` holds; GR-9 (2)'s worlds are `Unit`)
Hyps: (a) all -/
theorem cornerTree_corner_not_fairClass :
    Corner cornerObs cornerActEv cornerTree ∧ ¬ StronglyFair cornerTree :=
  ⟨⟨cornerTree_valueFair, cornerTree_almostFair, fun d _ => by cases d; exact cornerTree_recordsForAll,
    cornerTree_pruned_realized.1, cornerTree_pruned_realized.2⟩, cornerTree_not_stronglyFair⟩

/-- The five leaves of `cornerTree`: worlds, laws under `procQ q`, payoffs.
Source: none: infrastructure
Kind: L -/
theorem cornerTree_leaf_facts (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    world cornerTree ⟨0, .a, 0, ()⟩ = (true, .a) ∧ world cornerTree ⟨0, .a, 1, ()⟩ = (true, .a) ∧
    world cornerTree ⟨0, .b, ()⟩ = (true, .b) ∧ world cornerTree ⟨1, .a, ()⟩ = (false, .a) ∧
    world cornerTree ⟨1, .b, ()⟩ = (false, .b) ∧
    leafLaw (procQ q h0 h1) cornerTree ⟨0, .a, 0, ()⟩ = 1 / 2 * (q * (1 / 2)) ∧
    leafLaw (procQ q h0 h1) cornerTree ⟨0, .a, 1, ()⟩ = 1 / 2 * (q * (1 / 2)) ∧
    leafLaw (procQ q h0 h1) cornerTree ⟨0, .b, ()⟩ = 1 / 2 * (1 - q) ∧
    leafLaw (procQ q h0 h1) cornerTree ⟨1, .a, ()⟩ = 1 / 2 * q ∧
    leafLaw (procQ q h0 h1) cornerTree ⟨1, .b, ()⟩ = 1 / 2 * (1 - q) ∧
    payoff cornerTree ⟨0, .a, 0, ()⟩ = 1 ∧ payoff cornerTree ⟨0, .a, 1, ()⟩ = 3 ∧
    payoff cornerTree ⟨0, .b, ()⟩ = 0 ∧ payoff cornerTree ⟨1, .a, ()⟩ = 2 ∧
    payoff cornerTree ⟨1, .b, ()⟩ = 0 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · show FinDistr.fair.w 0 * ((procQ q h0 h1 ()).w Act2.a * (FinDistr.fair.w 0 * 1)) = _
    simp [FinDistr.fair, FinDistr.coin, procQ]
  · show FinDistr.fair.w 0 * ((procQ q h0 h1 ()).w Act2.a * (FinDistr.fair.w 1 * 1)) = _
    simp [FinDistr.fair, FinDistr.coin, procQ]; norm_num
  · show FinDistr.fair.w 0 * ((procQ q h0 h1 ()).w Act2.b * 1) = _
    simp [FinDistr.fair, FinDistr.coin, procQ]
  · show FinDistr.fair.w 1 * ((procQ q h0 h1 ()).w Act2.a * 1) = _
    simp [FinDistr.fair, FinDistr.coin, procQ]; norm_num
  · show FinDistr.fair.w 1 * ((procQ q h0 h1 ()).w Act2.b * 1) = _
    simp [FinDistr.fair, FinDistr.coin, procQ]; norm_num

/-- `ν` and `𝔼[r 1_X]` of the act events on `cornerTree` under `procQ q`.
Source: none: infrastructure
Kind: L -/
theorem cornerTree_act_stats (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    nu (procQ q h0 h1) cornerTree (cornerActEv () .a ∩ cornerObs ()) = q ∧
    nu (procQ q h0 h1) cornerTree (cornerActEv () .b ∩ cornerObs ()) = 1 - q ∧
    paySum (procQ q h0 h1) cornerTree (cornerActEv () .a ∩ cornerObs ()) = 2 * q ∧
    paySum (procQ q h0 h1) cornerTree (cornerActEv () .b ∩ cornerObs ()) = 0 := by
  obtain ⟨w1, w2, w3, w4, w5, l1, l2, l3, l4, l5, p1, p2, p3, p4, p5⟩ := cornerTree_leaf_facts q h0 h1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [nu_eq_sum, cornerTree_sum, w1, w2, w3, w4, w5, l1, l2, l3, l4, l5]
    simp [cornerActEv, cornerObs]; ring
  · rw [nu_eq_sum, cornerTree_sum, w1, w2, w3, w4, w5, l1, l2, l3, l4, l5]
    simp [cornerActEv, cornerObs]; ring
  · rw [paySum_eq_sum_ite, cornerTree_sum, w1, w2, w3, w4, w5, l1, l2, l3, l4, l5, p1, p2, p3, p4, p5]
    simp [cornerActEv, cornerObs]; ring
  · rw [paySum_eq_sum_ite, cornerTree_sum, w1, w2, w3, w4, w5, l1, l2, l3, l4, l5, p1, p2, p3, p4, p5]
    simp [cornerActEv, cornerObs]

/-- **The corner corollary inhabited (N+)**: on `cornerTree` (in the corner, not strongly fair),
`δ_a` is event-tremble-EDT-consistent (`𝔼_ε[r ∣ a] = 2 > 0 = 𝔼_ε[r ∣ b]`) and — by
`corner_eventTrembleEdt_isOptimal` — optimal, `V = 2`; `δ_b` (`V = 0`) is not.
Source: `grounding.md` GR-10 ("example (2), where the only tremble-EDT-consistent pure procedure is
the optimum `V = 2`"), GR-11
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem cornerTree_corner_witness :
    EventTrembleEdtConsistent cornerObs cornerActEv (Proc.ofFun fun _ => Act2.a) cornerTree ∧
    IsOptimal (Proc.ofFun fun _ => Act2.a) cornerTree ∧
    value (Proc.ofFun fun _ => Act2.a) cornerTree = 2 ∧
    ¬ IsOptimal (Proc.ofFun fun _ => Act2.b) cornerTree := by
  have hpa : (Proc.ofFun fun _ => Act2.a : Proc Unit (fun _ => Act2) ℚ) = procQ 1 zero_le_one le_rfl := by
    funext d; apply FinDistr.ext'; intro x; cases x <;> simp [Proc.ofFun, procQ, FinDistr.act2]
  have hpb : (Proc.ofFun fun _ => Act2.b : Proc Unit (fun _ => Act2) ℚ) = procQ 0 le_rfl zero_le_one := by
    funext d; apply FinDistr.ext'; intro x; cases x <;> simp [Proc.ofFun, procQ, FinDistr.act2]
  have hD2 : EventTrembleEdtConsistent cornerObs cornerActEv (Proc.ofFun fun _ => Act2.a)
      cornerTree := by
    refine ⟨1, one_pos, fun ε h0 h1 _ d _ _ _ a ha => ?_⟩
    cases d
    rw [hpa, tremble_procQ]
    obtain ⟨n1, n2, s1, s2⟩ := cornerTree_act_stats ((1 - ε) * 1 + ε / 2)
      (qeps_mem 1 ε zero_le_one le_rfl h0.le h1).1 (qeps_mem 1 ε zero_le_one le_rfl h0.le h1).2
    cases a <;> simp [Proc.ofFun_w] at ha
    refine ⟨by rw [n1]; linarith, fun b _ => ?_⟩
    cases b
    · exact le_rfl
    · unfold condExp
      rw [n1, n2, s1, s2, zero_div]
      exact div_nonneg (by linarith) (by linarith)
  refine ⟨hD2, corner_eventTrembleEdt_isOptimal cornerTree_corner_not_fairClass.1 hD2, ?_, fun h => ?_⟩
  · rw [hpa, cornerTree_value]; norm_num
  · have := h (Proc.ofFun fun _ => Act2.a)
    rw [hpa, hpb, cornerTree_value, cornerTree_value] at this
    norm_num at this

end Cleanroom.Decision.DpEdtUdtFair

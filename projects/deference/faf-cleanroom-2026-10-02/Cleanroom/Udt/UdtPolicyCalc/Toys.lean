import Cleanroom.Udt.UdtPolicyCalc.Update
import Mathlib.Tactic.FinCases

/-!
# Depth-two environments: the toy problems and the T14 witnesses

* Depth-two machinery: `root2`, `node2`, `mkEnv2` (an environment from a root law and a
  depth-one law), `mkActEnv2` (an action environment), `runLaw_two`, `V_two`, and the filtered
  sums `pH_two`, `contVal_two`, `offMass_two` at a depth-one node.
* udt-rep-2-020, Post 1's toy problems as policy-selection environments, with the source's
  numbers: Counterfactual Mugging (`cm_pay_sub_refuse : V pay − V refuse = 45`), Parfit's
  Hitchhiker (`parfit_pay_sub_refuse : = L − 10000`), XOR Blackmail (`xor_V_pay = −199`,
  `xor_V_refuse = −100`).
* T14 N+ witness (`t14_witness`: an action environment, a node, two continuations agreeing off
  it with different values, and the identity holding) and the **policy-dependent failure**
  (`cm_score_ne_V`: in counterfactual mugging with reference policy `pay` and `h = tails`,
  `S_h refuse = 50 ≠ 0 = V refuse` while `S_h pay = 45 = V pay` — the updated agent refuses, the
  ex-ante agent pays; this is where UDT's acausal term enters).

Package `udt-policy-calc` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Udt.UdtPolicyCalc

noncomputable section

namespace Tree

open Finset

section Two

variable {O A : Type} [Fintype O] [DecidableEq O]

/-- The root of a depth-two tree.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def root2 : Node O 2 := ⟨0, Fin.elim0⟩

/-- The depth-one node after observation `o`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def node2 (o : O) : Node O 2 := ⟨1, ![o]⟩

/-- Supporting lemma `node2_cases` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem node2_cases (m : Node O 2) : m = root2 ∨ ∃ o, m = node2 o := by
  rcases m with ⟨⟨k, hk⟩, f⟩
  rcases k with _ | _ | k
  · left
    exact Sigma.ext rfl (heq_of_eq (Subsingleton.elim _ _))
  · right
    exact ⟨f 0, Sigma.ext rfl (heq_of_eq (funext fun i => by fin_cases i; rfl))⟩
  · omega

/-- Supporting lemma `node2_injective` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem node2_injective {o o' : O} (h : node2 o = node2 o') : o = o' := by
  have h2 := (Sigma.mk.inj_iff.mp h).2
  exact congrFun (eq_of_heq h2) 0

/-- A depth-two policy-selection environment from a root law and a depth-one law.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def mkEnv2 (r : Pol O A 2 → FinDist O) (s : Pol O A 2 → O → FinDist O) : Env O A 2 :=
  fun π m => if h : m.1.val = 0 then r π else s π (m.2 ⟨0, Nat.pos_of_ne_zero h⟩)

/-- Supporting lemma `mkEnv2_root` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem mkEnv2_root (r : Pol O A 2 → FinDist O) (s : Pol O A 2 → O → FinDist O)
    (π : Pol O A 2) : mkEnv2 r s π root2 = r π := rfl

/-- Supporting lemma `mkEnv2_node2` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem mkEnv2_node2 (r : Pol O A 2 → FinDist O) (s : Pol O A 2 → O → FinDist O)
    (π : Pol O A 2) (o : O) : mkEnv2 r s π (node2 o) = s π o := rfl

/-- A depth-two action environment from a root law and a depth-one law reading the action.
Source: none: infrastructure (mandate T14 witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def mkActEnv2 (r : FinDist O) (s : O → A → FinDist O) : ActionEnv O A 2 :=
  fun m a => if h : m.1.val = 0 then r else s (m.2 ⟨0, Nat.pos_of_ne_zero h⟩) a

/-- Supporting lemma `liftEnv_mkActEnv2` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem liftEnv_mkActEnv2 (r : FinDist O) (s : O → A → FinDist O) :
    liftEnv (mkActEnv2 r s) = mkEnv2 (fun _ => r) (fun π o => s o (π (node2 o))) := by
  funext π m
  rcases node2_cases m with rfl | ⟨o, rfl⟩ <;> rfl

/-- Supporting lemma `prefixOf_two_zero` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem prefixOf_two_zero (l : Leaf O 2) : prefixOf l 0 = root2 :=
  Sigma.ext rfl (heq_of_eq (funext fun i => Fin.elim0 i))

/-- Supporting lemma `prefixOf_two_one` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem prefixOf_two_one (l : Leaf O 2) : prefixOf l 1 = node2 (l 0) :=
  Sigma.ext rfl (heq_of_eq (funext fun i => by fin_cases i; rfl))

/-- Supporting lemma `sum_leaf2` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_leaf2 {M : Type} [AddCommMonoid M] (g : Leaf O 2 → M) :
    ∑ l, g l = ∑ o₁, ∑ o₂, g ![o₁, o₂] := by
  rw [← (piFinTwoEquiv fun _ => O).symm.sum_comp g, Fintype.sum_prod_type]
  simp only [piFinTwoEquiv_symm_eq]

/-- Supporting lemma `runLaw_two` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem runLaw_two (r : Pol O A 2 → FinDist O) (s : Pol O A 2 → O → FinDist O) (π : Pol O A 2)
    (l : Leaf O 2) : runLaw (mkEnv2 r s) π l = (r π).w (l 0) * (s π (l 0)).w (l 1) := by
  simp only [runLaw, pathLaw, envKernel, Fin.prod_univ_two, prefixOf_two_zero, prefixOf_two_one,
    mkEnv2_root, mkEnv2_node2]

/-- The value of a depth-two environment, expanded.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem V_two (r : Pol O A 2 → FinDist O) (s : Pol O A 2 → O → FinDist O) (U : Leaf O 2 → ℝ)
    (π : Pol O A 2) :
    V (mkEnv2 r s) U π = ∑ o₁, ∑ o₂, (r π).w o₁ * (s π o₁).w o₂ * U ![o₁, o₂] := by
  unfold V
  rw [sum_leaf2]
  simp only [runLaw_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- Supporting lemma `leafExt_node2_iff` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem leafExt_node2_iff (o : O) (l : Leaf O 2) : LeafExt (node2 o) l ↔ l 0 = o := by
  constructor
  · intro h
    have := congrFun h ⟨0, Nat.one_pos⟩
    exact this
  · intro h
    funext i
    have hi : i.val = 0 := Nat.lt_one_iff.mp i.isLt
    have : i = ⟨0, Nat.one_pos⟩ := Fin.ext hi
    subst this
    exact h

/-- Supporting lemma `sum_filter_leafExt_node2` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_filter_leafExt_node2 (o : O) (g : Leaf O 2 → ℝ) :
    ∑ l ∈ univ.filter (LeafExt (node2 o)), g l = ∑ o₂, g ![o, o₂] := by
  rw [Finset.sum_filter, sum_leaf2]
  simp only [leafExt_node2_iff, Matrix.cons_val_zero]
  rw [Finset.sum_congr rfl (fun o₁ _ =>
    show (∑ o₂, if o₁ = o then g ![o₁, o₂] else 0) = if o₁ = o then ∑ o₂, g ![o₁, o₂] else 0 by
      split_ifs <;> simp)]
  rw [Finset.sum_ite_eq']
  simp

/-- Supporting lemma `sum_filter_not_leafExt_node2` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_filter_not_leafExt_node2 (o : O) (g : Leaf O 2 → ℝ) :
    ∑ l ∈ univ.filter (fun l => ¬ LeafExt (node2 o) l), g l =
      ∑ o₁, ∑ o₂, if o₁ = o then 0 else g ![o₁, o₂] := by
  rw [Finset.sum_filter, sum_leaf2]
  simp only [leafExt_node2_iff, Matrix.cons_val_zero, ite_not]

/-- Supporting lemma `suffixLaw_two_one` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem suffixLaw_two_one (F : Node O 2 → O → ℝ) (l : Leaf O 2) :
    suffixLaw F 1 l = F (node2 (l 0)) (l 1) := by
  unfold suffixLaw
  rw [show (univ.filter fun k : Fin 2 => 1 ≤ k.val) = {1} by decide, Finset.prod_singleton,
    prefixOf_two_one]

/-- Supporting lemma `pH_two` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pH_two (r : Pol O A 2 → FinDist O) (s : Pol O A 2 → O → FinDist O) (π : Pol O A 2)
    (o : O) : pH (mkEnv2 r s) π (node2 o) = ∑ o₂, (r π).w o * (s π o).w o₂ := by
  unfold pH
  rw [sum_filter_leafExt_node2]
  simp only [runLaw_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- Supporting lemma `contVal_two` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem contVal_two (r : Pol O A 2 → FinDist O) (s : Pol O A 2 → O → FinDist O)
    (U : Leaf O 2 → ℝ) (o : O) (π' : Pol O A 2) :
    contVal (mkEnv2 r s) U (node2 o) π' = ∑ o₂, (s π' o).w o₂ * U ![o, o₂] := by
  unfold contVal
  rw [sum_filter_leafExt_node2]
  refine Finset.sum_congr rfl fun o₂ _ => ?_
  rw [show ((node2 o : Node O 2).1 : ℕ) = 1 from rfl, suffixLaw_two_one]
  simp only [envKernel, mkEnv2_node2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- Supporting lemma `offMass_two` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem offMass_two (r : Pol O A 2 → FinDist O) (s : Pol O A 2 → O → FinDist O)
    (U : Leaf O 2 → ℝ) (π : Pol O A 2) (o : O) :
    offMass (mkEnv2 r s) U π (node2 o) =
      ∑ o₁, ∑ o₂, if o₁ = o then 0 else (r π).w o₁ * (s π o₁).w o₂ * U ![o₁, o₂] := by
  unfold offMass
  rw [sum_filter_not_leafExt_node2]
  simp only [runLaw_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- The fair coin.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def fairCoin : FinDist Bool := FinDist.bern (1 / 2) (by norm_num) (by norm_num) true false

/-- Supporting lemma `fairCoin_w` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem fairCoin_w (b : Bool) : fairCoin.w b = 1 / 2 := by
  cases b <;> norm_num [fairCoin]

end Two

/-! ### Counterfactual mugging (udt-rep-2-020; T14's failure witness) -/

section CM

/-- The tails node: the coin came up tails (`false`) and the agent is asked to pay.
Source: `references/udt101/01-story-so-far.md` line 55 (udt-rep-2-020)
Kind: D
Fidelity: exact
Hyps: n/a -/
def cmTails : Node Bool 2 := node2 false

/-- **Counterfactual mugging as a policy-selection environment.** The root flips a fair coin; on
tails (`false`) the second observation is whether the agent pays *here*; on heads (`true`) it is
whether the **policy** pays on tails — the environment reads `π` at `cmTails` from the heads
branch (an acausal effect).
Source: `references/udt101/01-story-so-far.md` line 55 (udt-rep-2-020)
Kind: D
Fidelity: exact
Hyps: n/a -/
def cmEnv : Env Bool Bool 2 := mkEnv2 (fun _ => fairCoin) (fun π _ => FinDist.delta (π cmTails))

/-- Payoffs: heads and rewarded `100`; tails and paid `−10`; else `0`.
Source: `references/udt101/01-story-so-far.md` line 55 (udt-rep-2-020)
Kind: D
Fidelity: exact
Hyps: n/a -/
def cmU : Leaf Bool 2 → ℝ := fun l =>
  if l 0 then (if l 1 then 100 else 0) else (if l 1 then -10 else 0)

/-- The always-pay policy.
Source: udt-rep-2-020
Kind: D
Fidelity: exact
Hyps: n/a -/
def cmPay : Pol Bool Bool 2 := fun _ => true

/-- The never-pay policy.
Source: udt-rep-2-020
Kind: D
Fidelity: exact
Hyps: n/a -/
def cmRefuse : Pol Bool Bool 2 := fun _ => false

/-- Supporting lemma `cm_V_pay` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cm_V_pay : V cmEnv cmU cmPay = 45 := by
  rw [cmEnv, V_two]
  simp only [Fintype.sum_bool, fairCoin_w, FinDist.delta_w, cmPay, cmU]
  norm_num

/-- Supporting lemma `cm_V_refuse` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cm_V_refuse : V cmEnv cmU cmRefuse = 0 := by
  rw [cmEnv, V_two]
  simp only [Fintype.sum_bool, fairCoin_w, FinDist.delta_w, cmRefuse, cmU]
  norm_num

/-- **udt-rep-2-020, Counterfactual Mugging.** "Policies which pay up in this specific situation
get 45 more dollars (in expectation) than policies which don't."
Source: `references/udt101/01-story-so-far.md` line 55 (udt-rep-2-020)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem cm_pay_sub_refuse : V cmEnv cmU cmPay - V cmEnv cmU cmRefuse = 45 := by
  rw [cm_V_pay, cm_V_refuse]
  norm_num

/-- The continuation that refuses at tails only.
Source: mandate T14 (failure witness)
Kind: D
Fidelity: exact
Hyps: n/a -/
def cmRefuseAtTails : Pol Bool Bool 2 := Function.update cmPay cmTails false

/-- Supporting lemma `cmRefuseAtTails_tails` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cmRefuseAtTails_tails : cmRefuseAtTails cmTails = false := Function.update_self _ _ _

/-- Supporting lemma `cmRefuseAtTails_node2_false` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cmRefuseAtTails_node2_false : cmRefuseAtTails (node2 false) = false :=
  cmRefuseAtTails_tails

/-- Supporting lemma `cmRefuseAtTails_node2_true` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cmRefuseAtTails_node2_true : cmRefuseAtTails (node2 true) = true := by
  rw [cmRefuseAtTails, Function.update_of_ne]
  · rfl
  · intro h
    exact absurd (node2_injective h) (by decide)

/-- Supporting lemma `cm_V_refuseAtTails` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cm_V_refuseAtTails : V cmEnv cmU cmRefuseAtTails = 0 := by
  rw [cmEnv, V_two]
  simp only [Fintype.sum_bool, fairCoin_w, FinDist.delta_w, cmRefuseAtTails_tails, cmU]
  norm_num

/-- Supporting lemma `cm_score_refuseAtTails` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cm_score_refuseAtTails : score cmEnv cmU cmPay cmTails cmRefuseAtTails = 50 := by
  rw [score, cmEnv, show cmTails = node2 false from rfl, pH_two, contVal_two, offMass_two]
  simp only [Fintype.sum_bool, fairCoin_w, FinDist.delta_w, cmRefuseAtTails_node2_false, cmPay,
    cmU]
  norm_num

/-- Supporting lemma `cm_score_pay` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cm_score_pay : score cmEnv cmU cmPay cmTails cmPay = 45 := by
  rw [score, cmEnv, show cmTails = node2 false from rfl, pH_two, contVal_two, offMass_two]
  simp only [Fintype.sum_bool, fairCoin_w, FinDist.delta_w, cmPay, cmU]
  norm_num

/-- **T14, the policy-dependent failure (udt-rep-2-023's extension).** In counterfactual mugging
(a policy-selection environment: the heads branch reads the policy's tails action) with reference
policy `pay` and `h = tails`: the continuation `refuse-at-tails` agrees with `pay` off `h`, but
`S_h refuse = ½·0 + ½·100 = 50 ≠ 0 = V refuse`, while `S_h pay = ½·(−10) + ½·100 = 45 = V pay`.
The updated agent refuses; the ex-ante agent pays. The identity of `score_eq_V` fails exactly
because `e` at a node off `h` (heads) depends on the policy's behaviour on `h`: this is where
UDT's acausal term enters.
Source: `references/udt101/04-essential-miscellanea.md` lines 74–106; `01-story-so-far.md` line 55 (udt-rep-2-023 extension, 2-020)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem cm_score_ne_V :
    AgreesOff cmPay cmRefuseAtTails cmTails ∧
      score cmEnv cmU cmPay cmTails cmRefuseAtTails ≠ V cmEnv cmU cmRefuseAtTails ∧
        score cmEnv cmU cmPay cmTails cmRefuseAtTails > score cmEnv cmU cmPay cmTails cmPay ∧
          V cmEnv cmU cmPay > V cmEnv cmU cmRefuseAtTails := by
  refine ⟨AgreesOff.update cmPay cmTails false, ?_, ?_, ?_⟩
  · rw [cm_score_refuseAtTails, cm_V_refuseAtTails]
    norm_num
  · rw [cm_score_refuseAtTails, cm_score_pay]
    norm_num
  · rw [cm_V_pay, cm_V_refuseAtTails]
    norm_num

end CM

/-! ### T14's N+ witness: an action environment -/

section T14Witness

/-- The action environment: fair coin at the root, then the observation *is* the action taken at
the depth-one node.
Source: mandate T14 witness
Kind: D
Fidelity: n/a
Hyps: n/a -/
def coinActEnv : ActionEnv Bool Bool 2 := mkActEnv2 fairCoin (fun _ a => FinDist.delta a)

/-- Supporting lemma `liftEnv_coinActEnv` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem liftEnv_coinActEnv :
    liftEnv coinActEnv = mkEnv2 (fun _ => fairCoin) (fun π o => FinDist.delta (π (node2 o))) :=
  liftEnv_mkActEnv2 _ _

/-- Supporting lemma `coinAct_V_pay` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem coinAct_V_pay : V (liftEnv coinActEnv) cmU cmPay = 45 := by
  rw [liftEnv_coinActEnv, V_two]
  simp only [Fintype.sum_bool, fairCoin_w, FinDist.delta_w, cmPay, cmU]
  norm_num

/-- Supporting lemma `coinAct_V_refuseAtTails` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem coinAct_V_refuseAtTails : V (liftEnv coinActEnv) cmU cmRefuseAtTails = 50 := by
  rw [liftEnv_coinActEnv, V_two]
  simp only [Fintype.sum_bool, fairCoin_w, FinDist.delta_w, cmU, cmRefuseAtTails_node2_false,
    cmRefuseAtTails_node2_true]
  norm_num

/-- **T14, N+ witness.** In the coin-then-act environment (an action environment, depth two,
non-constant `U`), the node `h = tails`, the reference policy `pay` and the continuation
`refuse-at-tails` inhabit the hypothesis package of `score_eq_V` non-degenerately: the two
policies differ, their values differ (`45` vs `50`), and the updated score of the continuation
equals its ex-ante value.
Source: mandate T14 witness
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem t14_witness :
    AgreesOff cmPay cmRefuseAtTails cmTails ∧ cmPay ≠ cmRefuseAtTails ∧
      V (liftEnv coinActEnv) cmU cmRefuseAtTails ≠ V (liftEnv coinActEnv) cmU cmPay ∧
        score (liftEnv coinActEnv) cmU cmPay cmTails cmRefuseAtTails =
          V (liftEnv coinActEnv) cmU cmRefuseAtTails := by
  refine ⟨AgreesOff.update cmPay cmTails false, ?_, ?_,
    score_eq_V coinActEnv cmU cmPay cmRefuseAtTails cmTails (AgreesOff.update cmPay cmTails false)⟩
  · intro h
    have := congrFun h cmTails
    rw [cmRefuseAtTails_tails] at this
    exact absurd this (by decide)
  · rw [coinAct_V_pay, coinAct_V_refuseAtTails]
    norm_num

end T14Witness

/-! ### Parfit's Hitchhiker (udt-rep-2-020) -/

section Parfit

/-- The node "rescued, in civilization", where the agent decides whether to pay.
Source: `references/udt101/01-story-so-far.md` line 57 (udt-rep-2-020)
Kind: D
Fidelity: exact
Hyps: n/a -/
def parfitCiv : Node Bool 2 := node2 true

/-- **Parfit's Hitchhiker as a policy-selection environment.** The perfect predictor rescues
(`true`) iff the policy pays in civilization; if rescued, the second observation is the payment.
Source: `references/udt101/01-story-so-far.md` line 57 (udt-rep-2-020)
Kind: D
Fidelity: exact
Hyps: n/a -/
def parfitEnv : Env Bool Bool 2 :=
  mkEnv2 (fun π => FinDist.delta (π parfitCiv))
    (fun π o => if o then FinDist.delta (π parfitCiv) else FinDist.delta false)

/-- Payoffs: rescued is worth `L`, paying costs `10000`, dying is `0`.
Source: `references/udt101/01-story-so-far.md` line 57 (udt-rep-2-020)
Kind: D
Fidelity: exact (`L` the value of a life, a variable)
Hyps: n/a -/
def parfitU (L : ℝ) : Leaf Bool 2 → ℝ := fun l =>
  if l 0 then L - (if l 1 then 10000 else 0) else 0

/-- Supporting lemma `parfit_V_pay` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem parfit_V_pay (L : ℝ) : V parfitEnv (parfitU L) cmPay = L - 10000 := by
  rw [parfitEnv, V_two]
  simp only [Fintype.sum_bool, FinDist.delta_w, cmPay, parfitU]
  norm_num

/-- Supporting lemma `parfit_V_refuse` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem parfit_V_refuse (L : ℝ) : V parfitEnv (parfitU L) cmRefuse = 0 := by
  rw [parfitEnv, V_two]
  simp only [Fintype.sum_bool, FinDist.delta_w, cmRefuse, parfitU]
  norm_num

/-- **udt-rep-2-020, Parfit's Hitchhiker.** "Policies which pay up in this specific situation get
(value of a life − 10,000 dollars) more than policies which don't pay …, which just die."
Source: `references/udt101/01-story-so-far.md` line 57 (udt-rep-2-020)
Kind: N+
Fidelity: exact
Hyps: (a) none (`L` a variable) -/
theorem parfit_pay_sub_refuse (L : ℝ) :
    V parfitEnv (parfitU L) cmPay - V parfitEnv (parfitU L) cmRefuse = L - 10000 := by
  rw [parfit_V_pay, parfit_V_refuse]
  ring

end Parfit

/-! ### XOR Blackmail (udt-rep-2-020) -/

section Xor

/-- Observations: a pair of bits. At depth one only the first bit (the letter) is meaningful; at
depth two the pair is (termites, paid).
Source: `references/udt101/01-story-so-far.md` line 59 (udt-rep-2-020)
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev XObs := Bool × Bool

/-- The node "letter received", where the agent decides whether to pay.
Source: `references/udt101/01-story-so-far.md` line 59
Kind: D
Fidelity: exact
Hyps: n/a -/
def xorLetter : Node XObs 2 := node2 (true, false)

/-- Termites given the letter bit and the policy's pay bit: the letter says "termites XOR pay".
Source: `references/udt101/01-story-so-far.md` line 59
Kind: D
Fidelity: exact
Hyps: n/a -/
def termitesOf : Bool → Bool → Bool
  | true, true => false
  | true, false => true
  | false, true => true
  | false, false => false

/-- **XOR Blackmail as a policy-selection environment.** Termites with probability `1/100`; the
letter arrives iff termites XOR the policy pays on receiving it (so with probability `99/100` for
payers, `1/100` for refusers); the second observation records (termites, paid).
Source: `references/udt101/01-story-so-far.md` line 59 (udt-rep-2-020)
Kind: D
Fidelity: exact
Hyps: n/a -/
def xorEnv : Env XObs Bool 2 :=
  mkEnv2
    (fun π => FinDist.bern (if π xorLetter then 99 / 100 else 1 / 100)
      (by split_ifs <;> norm_num) (by split_ifs <;> norm_num) (true, false) (false, false))
    (fun π o => FinDist.delta (termitesOf o.1 (π xorLetter), o.1 && π xorLetter))

/-- The always-pay and never-pay policies over `XObs`.
Source: udt-rep-2-020
Kind: D
Fidelity: exact
Hyps: n/a -/
def xorPay : Pol XObs Bool 2 := fun _ => true

/-- Supporting definition `xorRefuse` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: none -/
def xorRefuse : Pol XObs Bool 2 := fun _ => false

/-- Payoffs: `−10000` for termites, `−100` for paying.
Source: `references/udt101/01-story-so-far.md` line 59
Kind: D
Fidelity: exact
Hyps: n/a -/
def xorU : Leaf XObs 2 → ℝ := fun l =>
  (if (l 1).1 then -10000 else 0) + (if (l 1).2 then -100 else 0)

/-- **udt-rep-2-020, XOR Blackmail, payers.** "Policies which pay up … will receive the letter
with 99 percent probability, for −199 dollars in expectation."
Source: `references/udt101/01-story-so-far.md` line 59 (udt-rep-2-020)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem xor_V_pay : V xorEnv xorU xorPay = -199 := by
  rw [xorEnv, V_two]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, FinDist.bern_w, FinDist.delta_w, xorPay, xorU,
    termitesOf]
  norm_num

/-- **udt-rep-2-020, XOR Blackmail, refusers.** "Policies which don't pay up … will receive the
letter with 1 percent probability, for −100 dollars in expectation. So don't pay."
Source: `references/udt101/01-story-so-far.md` line 59 (udt-rep-2-020)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem xor_V_refuse : V xorEnv xorU xorRefuse = -100 := by
  rw [xorEnv, V_two]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, FinDist.bern_w, FinDist.delta_w, xorRefuse,
    xorU, termitesOf]
  norm_num

/-- Supporting lemma `xor_refuse_beats_pay` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem xor_refuse_beats_pay : V xorEnv xorU xorPay < V xorEnv xorU xorRefuse := by
  rw [xor_V_pay, xor_V_refuse]
  norm_num

end Xor

end Tree

end

end Cleanroom.Udt.UdtPolicyCalc

import Cleanroom.Decision.DpCalibLimits.Family
import Cleanroom.Decision.DpCalibLimits.TwoRoute

/-!
# Probe (audit round 3, fidelity): the sources' unguarded `MSR ⊆ MSR¹⁷` fails without recording

`msr17At_of_msrAt_recorded` proves S10 / SL-21's last inclusion `MSR ⊆ MSR¹⁷` under Definition-7
recording at `d` (the mandate's T4(d) scope). F11 records that no separation was found on the
routing root. This probe exhibits the separation on a four-point tree where *coverage* of `d`
fails: a fair coin; heads → a dummy point `f1` (both acts → a dummy point `f2`, both acts → the
forced-crossing world `bot`, payoff `−10`); tails → the point `e`, whose act `a` leads to the
`d`-node (`cross ↦ topCross, 10`; `not ↦ topNot, 0`) and whose act `b` leads to `off`, payoff `0`.
`O_d = ⊤`; the `d`-events are `cross = {bot, topCross}` and `not = {topNot}`. Under
`C = (d ↦ δ_not, e ↦ δ_b, f1, f2 ↦ δ_a)` the `d`-node is reached with probability `0` (behind
`e`'s zero-weight act), while the forced crossing has mass `½`.

* `gC` is MSR at every queried point (`g_msr`): at `d` the supported `not` is tremble-realizable
  (order `1`) with `limitVal not = 0 ≥ −10 = limitVal cross` (the `cross` event is realized, with
  the forced `−10`); at `e` the supported `b` has `limitVal = 0 ≥ 0`; the dummy points tie.
* At the strict state of `C` at `d` (`O_d = ⊤`, `ν(⊤) = 1`), `P_s(cross) = ½ > 0` and
  `P_s(not) = 0`, so `A_d^+ = {cross}` and `T_EDT` rejects `δ_not` (`g_not_tEdtAt`): MSR¹⁷ fails.
* The tree does not record at `d` for `C` (`g_not_recordsFor`): the forced leaf has positive law,
  its world satisfies `O_d`, and it meets no `d`-node.

So `MSR ⊄ MSR¹⁷` in general; the inclusion S10 asserts holds only under a hypothesis (recording),
exactly as the second inclusion `TS ⊆ MSR` does (`TsMsr.lean`). Evidence for the round-3 fidelity
audit's N1; not imported by the library.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-- Points: two dummies on the forced branch, `e` and `d`. -/
inductive GPt : Type
  | f1
  | f2
  | e
  | d
  deriving DecidableEq, Fintype

instance : Nonempty GPt := ⟨.d⟩

/-- Worlds. -/
inductive GW : Type
  | bot
  | off
  | topCross
  | topNot
  deriving DecidableEq, Fintype

def gPt (i : Fin 2) : GPt := if i = 0 then .f1 else .e
def gPt' (i : Fin 2) : GPt := if i = 0 then .f2 else .d
def gW (i : Fin 2) (y : Act2) : GW :=
  if i = 0 then .bot else (if y = .a then .topCross else .topNot)
def gPay (i : Fin 2) (y : Act2) : ℚ := if i = 0 then -10 else (if y = .a then 10 else 0)
def gOff (i : Fin 2) : GW := if i = 0 then .bot else .off
def gOffPay (i : Fin 2) : ℚ := if i = 0 then -10 else 0

/-- The tree. -/
def gTree : Tree GW GPt (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i =>
    .decision (gPt i) fun
      | .a => .decision (gPt' i) fun y => .leaf (gW i y) (gPay i y)
      | .b => .leaf (gOff i) (gOffPay i)

def gObs : GPt → Finset GW := fun _ => Finset.univ

def gActEv : (p : GPt) → Act2 → Finset GW
  | .d, .a => {.bot, .topCross}
  | .d, .b => {.topNot}
  | .e, .a => {.topCross, .topNot}
  | .e, .b => {.off}
  | _, _ => {.bot}

def gC : Proc GPt (fun _ => Act2) ℚ
  | .d => FinDistr.pure .b
  | .e => FinDistr.pure .b
  | _ => FinDistr.pure .a

theorem gTree_sum {M : Type} [AddCommMonoid M] (f : gTree.Leaves → M) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ((∑ y : Act2, f ⟨i, .a, y, ()⟩) + f ⟨i, .b, ()⟩) := by
  unfold gTree at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision, Act2.sum_univ, sum_leaves_decision]
  simp only [Tree.sum_leaves_leaf]

local macro "g_eval" : tactic =>
  `(tactic| (simp [gTree, leafLaw, leafLawPoly, trembleW, gW, gPt, gPt', gOff, gOffPay, gPay, gC,
      gActEv, gObs, Fin.sum_univ_two, Act2.sum_univ, FinDistr.fair, FinDistr.coin, act2_card_rat,
      FinDistr.pure_w]; try norm_num))

/-- Masses under `gC`: the `cross` event has mass `½` (the forced leaf), the `not` event `0`,
`off` has mass `½`. -/
theorem g_nu :
    nu gC gTree (gActEv .d .a ∩ gObs .d) = 1 / 2 ∧
    paySum gC gTree (gActEv .d .a ∩ gObs .d) = -5 ∧
    nu gC gTree (gActEv .d .b ∩ gObs .d) = 0 ∧
    nu gC gTree (gActEv .e .b ∩ gObs .e) = 1 / 2 ∧
    paySum gC gTree (gActEv .e .b ∩ gObs .e) = 0 ∧
    nu gC gTree (gActEv .f1 .a ∩ gObs .f1) = 1 / 2 ∧
    nu gC gTree (gActEv .f2 .a ∩ gObs .f2) = 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [nu_eq_sum, gTree_sum]; g_eval
  · rw [paySum_eq_sum_ite, gTree_sum]; g_eval
  · rw [nu_eq_sum, gTree_sum]; g_eval
  · rw [nu_eq_sum, gTree_sum]; g_eval
  · rw [paySum_eq_sum_ite, gTree_sum]; g_eval
  · rw [nu_eq_sum, gTree_sum]; g_eval
  · rw [nu_eq_sum, gTree_sum]; g_eval

/-- Uniform-ray coefficients: the `not` event at `d` and the `a` event at `e` have order `1`
(coefficient `¼`) with vanishing order-1 payoff mass. -/
theorem g_coeffs :
    (nuPoly gC gTree (gActEv .d .b ∩ gObs .d)).coeff 0 = 0 ∧
    (nuPoly gC gTree (gActEv .d .b ∩ gObs .d)).coeff 1 = 1 / 4 ∧
    (payPoly gC gTree (gActEv .d .b ∩ gObs .d)).coeff 1 = 0 ∧
    (nuPoly gC gTree (gActEv .e .a ∩ gObs .e)).coeff 0 = 0 ∧
    (nuPoly gC gTree (gActEv .e .a ∩ gObs .e)).coeff 1 = 1 / 4 ∧
    (payPoly gC gTree (gActEv .e .a ∩ gObs .e)).coeff 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Polynomial.coeff_zero_eq_eval_zero, nuPoly_eq_sum, gTree_sum]; g_eval
  · rw [coeff_one_eq_eval_zero_derivative, nuPoly_eq_sum, gTree_sum]; g_eval
  · rw [coeff_one_eq_eval_zero_derivative, payPoly_eq_sum, gTree_sum]; g_eval
  · rw [Polynomial.coeff_zero_eq_eval_zero, nuPoly_eq_sum, gTree_sum]; g_eval
  · rw [coeff_one_eq_eval_zero_derivative, nuPoly_eq_sum, gTree_sum]; g_eval
  · rw [coeff_one_eq_eval_zero_derivative, payPoly_eq_sum, gTree_sum]; g_eval

theorem nuPoly_ne_zero_of_coeff {X : Finset GW} {k : ℕ} {c : ℚ}
    (h : (nuPoly gC gTree X).coeff k = c) (hc : c ≠ 0) : nuPoly gC gTree X ≠ 0 := fun hz => by
  rw [hz, Polynomial.coeff_zero] at h; exact hc h.symm

/-- `gC` is MSR at `d`: `limitVal not = 0 ≥ −10 = limitVal cross`. -/
theorem g_msrAt_d : MSRAt gObs gActEv gC gTree .d := by
  intro x hx
  have hxb : x = .b := by cases x <;> simp [gC] at hx ⊢
  subst hxb
  obtain ⟨hcross, hcpay, _, _, _, _, _⟩ := g_nu
  obtain ⟨n0, n1, np1, _, _, _⟩ := g_coeffs
  have hnot : limitVal gC gTree (gActEv .d .b ∩ gObs .d) = 0 := by
    rw [limitVal_of_coeff_one _ _ _ n0 (by rw [n1]; norm_num), np1, zero_div]
  have hcr : limitVal gC gTree (gActEv .d .a ∩ gObs .d) = -10 := by
    rw [limitVal_eq_of_pos _ _ _ (by rw [hcross]; norm_num)]
    unfold condExp; rw [hcpay, hcross]; norm_num
  refine ⟨nuPoly_ne_zero_of_coeff n1 (by norm_num), fun b' _ => ?_⟩
  cases b'
  · rw [hnot, hcr]; norm_num
  · exact le_refl _

/-- `gC` is MSR at `e`: `limitVal (e.b) = 0 ≥ 0 = limitVal (e.a)`. -/
theorem g_msrAt_e : MSRAt gObs gActEv gC gTree .e := by
  intro x hx
  have hxb : x = .b := by cases x <;> simp [gC] at hx ⊢
  subst hxb
  obtain ⟨_, _, _, hoff, hoffpay, _, _⟩ := g_nu
  obtain ⟨_, _, _, e0, e1, ep1⟩ := g_coeffs
  have hb : limitVal gC gTree (gActEv .e .b ∩ gObs .e) = 0 := by
    rw [limitVal_eq_of_pos _ _ _ (by rw [hoff]; norm_num)]
    unfold condExp; rw [hoffpay, zero_div]
  have ha : limitVal gC gTree (gActEv .e .a ∩ gObs .e) = 0 := by
    rw [limitVal_of_coeff_one _ _ _ e0 (by rw [e1]; norm_num), ep1, zero_div]
  have hbne : nuPoly gC gTree (gActEv .e .b ∩ gObs .e) ≠ 0 := fun hz => by
    have := coeff_zero_nuPoly gC gTree (gActEv .e .b ∩ gObs .e)
    rw [hz, Polynomial.coeff_zero, hoff] at this; norm_num at this
  refine ⟨hbne, fun b' _ => ?_⟩
  cases b'
  · rw [ha, hb]
  · exact le_refl _

/-- The dummy points tie (both events are `{bot}`). -/
theorem g_msrAt_f1 : MSRAt gObs gActEv gC gTree .f1 := by
  intro x hx
  have hxa : x = .a := by cases x <;> simp [gC] at hx ⊢
  subst hxa
  obtain ⟨_, _, _, _, _, hf1, _⟩ := g_nu
  have hne : nuPoly gC gTree (gActEv .f1 .a ∩ gObs .f1) ≠ 0 := fun hz => by
    have := coeff_zero_nuPoly gC gTree (gActEv .f1 .a ∩ gObs .f1)
    rw [hz, Polynomial.coeff_zero, hf1] at this; norm_num at this
  refine ⟨hne, fun b' _ => ?_⟩
  cases b' <;> exact le_refl _

theorem g_msrAt_f2 : MSRAt gObs gActEv gC gTree .f2 := by
  intro x hx
  have hxa : x = .a := by cases x <;> simp [gC] at hx ⊢
  subst hxa
  obtain ⟨_, _, _, _, _, _, hf2⟩ := g_nu
  have hne : nuPoly gC gTree (gActEv .f2 .a ∩ gObs .f2) ≠ 0 := fun hz => by
    have := coeff_zero_nuPoly gC gTree (gActEv .f2 .a ∩ gObs .f2)
    rw [hz, Polynomial.coeff_zero, hf2] at this; norm_num at this
  refine ⟨hne, fun b' _ => ?_⟩
  cases b' <;> exact le_refl _

/-- **`gC` is MSR** (Definition 18′ at every queried point). -/
theorem g_msr : MSR gObs gActEv gC gTree := by
  intro p _
  cases p
  · exact g_msrAt_f1
  · exact g_msrAt_f2
  · exact g_msrAt_e
  · exact g_msrAt_d

/-- The strict state of `gC` (at `O_d = ⊤`). -/
noncomputable def gS : State GW ℚ := calibratedState gC gTree Finset.univ (nu_univ_pos _ _)

theorem g_strict : StrictOCAt (fun _ => gS) gObs gC gTree .d :=
  strictOCAt_calibratedState gObs gC gTree (fun _ => gS) .d (nu_univ_pos _ _) rfl

/-- **MSR¹⁷ fails at `d`**: `A_d^+ = {cross}` and the supported `not` is not in it. -/
theorem g_not_tEdtAt : ¬ TEdtAt (fun _ => gS) gActEv gC .d := by
  intro h
  obtain ⟨hcross, _, hnot, _, _, _, _⟩ := g_nu
  have hpa : (gS).pr (gActEv .d .a) = 1 / 2 := by
    show (calibratedState gC gTree Finset.univ _).pr _ = _
    rw [calibratedState_pr, nu_univ, div_one]; exact hcross
  have hpb : (gS).pr (gActEv .d .b) = 0 := by
    show (calibratedState gC gTree Finset.univ _).pr _ = _
    rw [calibratedState_pr, nu_univ, div_one]; exact hnot
  have hne : (APlus (fun _ => gS) gActEv .d).Nonempty :=
    ⟨.a, by simp [APlus, hpa]⟩
  have hb : Act2.b ∈ argmaxPlus (fun _ => gS) gActEv .d := h hne .b (by simp [gC])
  have hb' := argmaxPlus_subset (fun _ => gS) gActEv .d hb
  simp [APlus, hpb] at hb'

/-- **The tree does not record at `d` for `gC`**: the forced leaf has law `½`, its world is in
`O_d = ⊤`, and it meets no `d`-node. -/
theorem g_not_recordsFor : ¬ RecordsFor gObs gActEv gC gTree .d := by
  intro h
  have hlaw : 0 < leafLaw gC gTree ⟨0, .a, .a, ()⟩ := by g_eval
  have hcount := (h ⟨0, .a, .a, ()⟩ hlaw (by simp [gObs])).1
  simp [gTree, count, gPt, gPt'] at hcount

/-- The separation, assembled. -/
theorem msr_not_msr17_unrecorded :
    MSR gObs gActEv gC gTree ∧
    StrictOCAt (fun _ => gS) gObs gC gTree .d ∧
    0 < nu gC gTree (gObs .d) ∧
    ¬ RecordsFor gObs gActEv gC gTree .d ∧
    ¬ MSR17At gActEv gC (fun _ => gS) .d :=
  ⟨g_msr, g_strict, nu_univ_pos _ _, g_not_recordsFor, g_not_tEdtAt⟩

end Cleanroom.Decision.DpCalibLimits

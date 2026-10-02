import Cleanroom.Decision.DpCalibration.LimitTie

/-!
# dp-calibration — audit round 3, lens `fidelity`: probe `LimitTieLabels`

Not imported by the library. Two claims about `LimitTie.lean` (T3(d), repair round 2):

1. **The separation is concrete at the labels the ledger names.** With `δ_{a'}` at `d'`, the
   pure `δ_b` and the mixed `½/½` label at `d` are D1-approved (`limitTie_limitStateEdt`) and
   D2-rejected (`limitTie_eventTremble_b_zero`), while `(δ_a; δ_{a'})` is approved by both.
   These are one-line corollaries; elaborating them checks that the statements compose into the
   separation `limitTie_routes_differ` claims.

2. **The qualifier "`(m; δ_{a'})`" is load-bearing.** The root module's summary says D1
   "approves every label" on the limit-tie tree; the ledger and docstrings say "every label
   `(m; δ_{a'})`". With `½/½` at `d'` as well (`procLTmix`), the untrembled value of `b` is `5`,
   not `10`, and D1 rejects the mixed label at `d` for **every** state assignment — so the
   precise wording is the ledger's, and the root summary is loose (non-blocking, presentation).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibration

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Finset

/-- The mixed label `½/½` on `Act2`. -/
def ltHalf : FinDistr ℚ Act2 := FinDistr.act2 (1/2) (by norm_num) (by norm_num)

/-- `(δ_b; δ_{a'})` is D1-approved (with its limit = strict state). -/
theorem probe_deltaB_D1 :
    LimitStateEdt ltObs ltActEv (procLT (FinDistr.pure .b)) limitTie
      (fun _ => ltState (FinDistr.pure .b)) :=
  limitTie_limitStateEdt _

/-- `(δ_b; δ_{a'})` is D2-rejected. -/
theorem probe_deltaB_notD2 :
    ¬ EventTrembleEdtConsistent ltObs ltActEv (procLT (FinDistr.pure .b)) limitTie := by
  intro h
  have := (limitTie_eventTremble_b_zero _ h).1
  simp [procLT] at this

/-- `(½/½; δ_{a'})` is D1-approved. -/
theorem probe_half_D1 :
    LimitStateEdt ltObs ltActEv (procLT ltHalf) limitTie (fun _ => ltState ltHalf) :=
  limitTie_limitStateEdt _

/-- `(½/½; δ_{a'})` is D2-rejected. -/
theorem probe_half_notD2 :
    ¬ EventTrembleEdtConsistent ltObs ltActEv (procLT ltHalf) limitTie := by
  intro h
  have := (limitTie_eventTremble_b_zero _ h).1
  norm_num [procLT, ltHalf] at this

/-- `(δ_a; δ_{a'})` is approved by both devices. -/
theorem probe_deltaA_both :
    LimitStateEdt ltObs ltActEv (procLT (FinDistr.pure .a)) limitTie
      (fun _ => ltState (FinDistr.pure .a)) ∧
    EventTrembleEdtConsistent ltObs ltActEv (procLT (FinDistr.pure .a)) limitTie :=
  ⟨limitTie_limitStateEdt _, limitTie_pureA_eventTremble⟩

/-- The procedure `(½/½; ½/½)`: the delegated node is mixed too, so the untrembled value of `b`
at `d` is `10 · ½ = 5`, no tie. -/
def procLTmix : Proc LtPt (fun _ => Act2) ℚ := fun _ => ltHalf

/-- **The `(m; δ_{a'})` qualifier is load-bearing**: with `½/½` at `d'`, D1 rejects the mixed
label at `d` for every state assignment. -/
theorem probe_mixed_dprime_notD1 (s : LtPt → State LtW ℚ) :
    ¬ LimitStateEdt ltObs ltActEv procLTmix limitTie s := by
  rintro ⟨hlim, hedt⟩
  have hd := limitTie_queried.1
  have hs : StrictOCAt s ltObs procLTmix limitTie .d :=
    limitOCAt_imp_strictOCAt s ltObs procLTmix limitTie .d (hlim .d hd)
  have hpos : 0 < nu procLTmix limitTie (ltObs .d) := by
    unfold ltObs; exact nu_univ_pos _ _
  obtain ⟨h1, h2⟩ := hs hpos
  -- the beliefs about the action events are `ν`
  have hpr : ∀ act, (s .d).pr (ltActEv .d act) = nu procLTmix limitTie (ltActEv .d act) := by
    intro act
    have := h1 (ltActEv .d act)
    rwa [ltObs, Finset.inter_univ, nu_univ, mul_one] at this
  have hnua : nu procLTmix limitTie (ltActEv .d .a) = 1/2 := by
    rw [limitTie_nu]; simp [ltActEv, procLTmix, ltHalf]
  have hnub : nu procLTmix limitTie (ltActEv .d .b) = 1/2 := by
    rw [limitTie_nu]; simp [ltActEv, procLTmix, ltHalf]; norm_num
  have hpa : 0 < (s .d).pr (ltActEv .d .a) := by rw [hpr, hnua]; norm_num
  have hpb : 0 < (s .d).pr (ltActEv .d .b) := by rw [hpr, hnub]; norm_num
  -- the act values: `V(a) = 10`, `V(b) = 5`
  have hVa : (s .d).V (ltActEv .d .a) = 10 := by
    have := h2 (ltActEv .d .a) hpa (by rw [ltObs, Finset.inter_univ, hnua]; norm_num)
    rw [ltObs, Finset.inter_univ, hnua, limitTie_paySum] at this
    simp [ltActEv, procLTmix, ltHalf] at this
    simp only [ltActEv]
    linarith
  have hVb : (s .d).V (ltActEv .d .b) = 5 := by
    have := h2 (ltActEv .d .b) hpb (by rw [ltObs, Finset.inter_univ, hnub]; norm_num)
    rw [ltObs, Finset.inter_univ, hnub, limitTie_paySum] at this
    simp [ltActEv, procLTmix, ltHalf] at this
    simp only [ltActEv]
    linarith
  -- `T_EDT` at `d`: `b` is supported, so `b ∈ argmax`, so `V(a) ≤ V(b)`: `10 ≤ 5`
  have hmemA : Act2.a ∈ APlus s ltActEv .d := by
    simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and]; exact hpa
  have hne : (APlus s ltActEv .d).Nonempty := ⟨.a, hmemA⟩
  have hbsupp : 0 < (procLTmix .d).w .b := by norm_num [procLTmix, ltHalf]
  have hb := (mem_argmaxPlus s ltActEv .d .b).mp (hedt .d hd hne .b hbsupp)
  have := hb.2 .a hmemA
  rw [hVa, hVb] at this
  norm_num at this

end Cleanroom.Decision.DpCalibration

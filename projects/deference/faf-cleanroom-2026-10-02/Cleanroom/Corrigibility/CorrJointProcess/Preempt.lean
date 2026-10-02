import Cleanroom.Corrigibility.CorrJointProcess.Buttons

/-!
# T18 — outcome-reach preemption: `V(FAST) − V(SLOW) = −Δ₋`; the caution proposition

* **(a)** On Setting S, the hurried plan completes before a press can land: `fastValue` pays the
  continuation on the press branch and the best response on silence, while the hard button
  (`hardButtonValue`, the SLOW plan with interruption value `V(s)` on the press branch) stops.
  `fastValue − hardButtonValue = E[X_Pr 1_Pr] = −Δ₋` (`fastValue_sub_hardButtonValue`); the gain
  from *choosing* to hurry is `max(0, −Δ₋)` (`hurry_gain`) — 2-013(D)'s identity, the same lemma.
* **(b) Caution (P8).** On `twoState` with `α ≤ β`, `0 < α`, `h ≥ 0`: `Δ₋ < 0 ⟹ 0 < (1−ε)c − εh` —
  an agent that hurries under a right-signed sensor with a correct model never hurries a plan
  that is negative in expectation (`twoState_caution`).
* **(c)** R5's parameters (`ε = 1/10`, `α = 1/20`, `β = 9/10`, `c = 1`, `h = 5`): the hurry family
  `hurryFamily v` (Pattern C; `true` = SLOW with interruption value `v`, `false` = FAST):
  `FAST − SLOW = −81/200` (`2/5` vs `161/200`) at `v = 0`, and the argmax moves with `v`
  (`−5`: FAST; `0, +5`: SLOW) (`hurry_witness`).

Carey–Everitt's four predicates by tense (Statement 10) are `recorded only` (findings; the two
"coded, not computed" cells).

Sources: anticipatory-final.md Statements 9, 10; anticipatory.md P8; d1-special-case-adversary.md A31.
-/

namespace Cleanroom.Corrigibility.CorrJointProcess

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

set_option linter.unusedSectionVars false

section Fast

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂] (S : ThreeStep Ω A₁ A₂)

/-- **The hurried plan's value**: the plan completes before any press lands, so the press branch
pays the continuation `V(c)` and silence pays the best response on `{c, s}`.
Source: [[corr-wf14b-inventory]] 024 / anticipatory-final.md Statement 9; anticipatory.md P8 ("FAST — completes before any push")
Kind: D
Fidelity: exact -/
noncomputable def fastValue (a : A₁) (c s : A₂) : ℝ :=
  S.obsExpect a .press (S.V a .press c) +
    max (S.obsExpect a .silent (S.V a .silent c)) (S.obsExpect a .silent (S.V a .silent s))

/-- **T18(a): `V(FAST) − V(SLOW) = E[X_Pr 1_Pr] = −Δ₋`**, with SLOW the hard button (the press
forces `s`, whose press-branch value is the interruption value).
Source: [[corr-wf14b-inventory]] 024, 2-013 / anticipatory-final.md Statement 9 ("`V(FAST) − V(SLOW) = −Δ₋(∅)`"); d1-special-case-adversary.md A31
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem fastValue_sub_hardButtonValue (a : A₁) (c s : A₂) :
    fastValue S a c s - S.hardButtonValue a c s = -(S.deltaMinus a c s) := by
  unfold fastValue hardButtonValue deltaMinus
  rw [S.obsExpect_Xo]; ring

/-- **T18(a), the gain from choosing to hurry**: `max(FAST, SLOW) − SLOW = max(0, −Δ₋)` —
2-013(D)'s "the gain from costlessly preventing the press is `max(0, −margin)`".
Source: [[corr-wf14b-2-inventory]] 2-013(D) / d1-special-case-adversary.md A31
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem hurry_gain (a : A₁) (c s : A₂) :
    max (fastValue S a c s) (S.hardButtonValue a c s) - S.hardButtonValue a c s =
      max 0 (-(S.deltaMinus a c s)) := by
  rw [max_eq_add_max_sub, fastValue_sub_hardButtonValue, max_comm]; ring

end Fast

/-! ## (b) Caution -/

/-- **T18(b), the caution proposition (P8).** On `twoState` with a right-signed live sensor
(`0 < α ≤ β`) and `h ≥ 0`: if the agent strictly prefers to hurry (`Δ₋ < 0`), the plan is
positive in expectation, `0 < (1 − ε)c − εh`. From `(1−ε)αc > εβh ≥ εαh`.
Source: [[corr-wf14b-inventory]] 024 / anticipatory-final.md Statement 10 ("Caution proposition"); anticipatory.md P8
Kind: P (small)
Fidelity: exact (on the closed intervals; `h ≥ 0`, no sign on `c`)
Hyps: (a) only -/
theorem twoState_caution (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hh : 0 ≤ h) (hα0 : 0 < α) (hαβ : α ≤ β)
    (hover : (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop < 0) :
    0 < (1 - ε) * c - ε * h := by
  rw [twoState_deltaMinus] at hover
  have hkey : 0 < α * ((1 - ε) * c - ε * h) := by
    nlinarith [mul_nonneg hε.1 hh, hαβ]
  by_contra hcon
  have hcon' := not_lt.mp hcon
  nlinarith

/-! ## (c) The hurry family and R5's numbers -/

/-- **The hurry family** (Pattern C): `true` = SLOW (a press lands between the two halves and
forces `stop` at interruption value `v`; silence completes with the two-state payoffs), `false`
= FAST (the deed is done whatever is observed: `X` on both branches and both actions). One prior
and sensor.
Source: [[corr-wf14b-inventory]] 024 / anticipatory.md P8 (script D)
Kind: D
Fidelity: exact (A1 fails for SLOW when `v ≠ 0`: the interruption value is a press-branch payoff) -/
noncomputable def hurryFamily (ε α β c h v : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) : ThreeStep World Bool TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => twoPoint ε hε
  press := fun _ => twoPress α β
  press_nonneg := fun _ ω => match ω with
    | .right => hα.1
    | .wrong => hβ.1
  press_le_one := fun _ ω => match ω with
    | .right => hα.2
    | .wrong => hβ.2
  V := fun a o act ω =>
    if a then (if o = .press then (if act = .stop then v else twoValue c h .cont ω) else twoValue c h act ω)
    else twoValue c h .cont ω

variable (ε α β c h v : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- SLOW's value is `P(Pr)·v + max(v_silent, 0)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma hurryFamily_slow :
    (hurryFamily ε α β c h v hε hα hβ).hardButtonValue true .cont .stop =
      ((1 - ε) * α + ε * β) * v + max (vSilent ε α β c h) 0 := by
  simp only [hardButtonValue, obsExpect, obsWeight_press, obsWeight_silent, hurryFamily, World.sum_eq,
    twoPoint_right, twoPoint_wrong, twoPress, twoValue, vSilent, if_true]
  simp
  ring_nf

/-- FAST's value is `E[X]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma hurryFamily_fast :
    fastValue (hurryFamily ε α β c h v hε hα hβ) false .cont .stop = (1 - ε) * c - ε * h := by
  simp only [fastValue, obsExpect, obsWeight_press, obsWeight_silent, hurryFamily, World.sum_eq,
    twoPoint_right, twoPoint_wrong, twoPress, twoValue, Bool.false_eq_true, if_false, max_self]
  ring

/-- **T18(c) witness (R5, script D).** `ε = 1/10`, `α = 1/20`, `β = 9/10`, `c = 1`, `h = 5`:
`FAST = 2/5`; `SLOW = 13/100, 161/200, 37/25` at `v = −5, 0, 5`; `FAST − SLOW = −81/200` at
`v = 0`; FAST is chosen at `v = −5` and SLOW at `v = 0, 5`.
Source: [[corr-wf14b-inventory]] 024 / anticipatory.md P8; anticipatory-final.md Statement 9
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem hurry_witness :
    fastValue (hurryFamily (1 / 10) (1 / 20) (9 / 10) 1 5 0 mem_Icc_1_10 ⟨by norm_num, by norm_num⟩
        ⟨by norm_num, by norm_num⟩) false .cont .stop = 2 / 5 ∧
    (hurryFamily (1 / 10) (1 / 20) (9 / 10) 1 5 0 mem_Icc_1_10 ⟨by norm_num, by norm_num⟩
        ⟨by norm_num, by norm_num⟩).hardButtonValue true .cont .stop = 161 / 200 ∧
    (hurryFamily (1 / 10) (1 / 20) (9 / 10) 1 5 (-5) mem_Icc_1_10 ⟨by norm_num, by norm_num⟩
        ⟨by norm_num, by norm_num⟩).hardButtonValue true .cont .stop = 13 / 100 ∧
    (hurryFamily (1 / 10) (1 / 20) (9 / 10) 1 5 5 mem_Icc_1_10 ⟨by norm_num, by norm_num⟩
        ⟨by norm_num, by norm_num⟩).hardButtonValue true .cont .stop = 37 / 25 ∧
    (2 / 5 : ℝ) - 161 / 200 = -(81 / 200) ∧ (13 / 100 : ℝ) < 2 / 5 ∧ (2 / 5 : ℝ) < 161 / 200 ∧
      (2 / 5 : ℝ) < 37 / 25 := by
  refine ⟨?_, ?_, ?_, ?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · rw [hurryFamily_fast]; norm_num
  all_goals (rw [hurryFamily_slow]; unfold vSilent; norm_num)

end Cleanroom.Corrigibility.CorrJointProcess

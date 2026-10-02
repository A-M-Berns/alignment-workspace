import Cleanroom.Found.CorrThreeStep.Witnesses
import Cleanroom.Found.CorrThreeStep.TwoState
import Cleanroom.Lit.LitMdpCorrigible.Hudson

/-!
# `lit-mdp-corrigible` — the hard button and the hurry incentive (T5)

(a) Over `corr-three-step`'s two-button family: the agent leaves a hard button alone at *every*
disabling cost iff the below-threshold inequality (the Total Trust filler) holds — "argmax
invariance for all disabling costs iff the filler" (`L`, cited from `d2_hard_forall_cost_iff_d1`).
(b) A mid-action press with the sensor's rates and post-interruption value `v`:
`E[V|FAST] − E[V|SLOW] = (1−ε)αc − εβh − v((1−ε)α + εβ)`; at `v = 0` this is `−Δ₋`: the hurry
incentive is the below-threshold clause failing. (c) N+ at `ε = 1/10, α = 1/20, β = 9/10, c = 1,
h = 5`: FAST at `v = −5` (difference `27/100`), SLOW at `v ∈ {0, 5}`; and the same numbers as a
goal-in-state MDP `hurry` (one transition, reward read off the landing state, `γ = 0`) whose
optimal set at the start state moves with the post-interruption distribution — `¬ Interruptible`
(Theorem 3.5's myopic case, App. A l. 563, exhibited without Condition 2). **Modelling caveat**
(critique claim 3): the thesis agent is modelled as a consequentialist one-step goal on the
landing state, the two halves of SLOW collapsed into one transition with the press landing
between them; the mandate's "two-step non-myopic" phrasing is this instance with `γ` immaterial.

Mandate: [[lit-mdp-corrigible-mandate]] T5; [[corr-wf13-2-inventory]] 082 item 2; [[corr-wf14-inventory]] 018 (R5).
-/

open Finset FactoredSpaces
open Cleanroom.Found.CorrThreeStep

namespace Cleanroom.Lit.LitMdpCorrigible.HardButton

set_option linter.unusedSectionVars false

/-! ## (a) D2 at every disabling cost iff the filler -/

/-- **Argmax invariance for all disabling costs iff the filler (T5(a)).** On the two-button
family (`none` leaves the hard button, `some κ` disables it at cost `κ`), in the continue-by-
default regime, the agent weakly prefers to leave the button at every positive cost iff the
below-threshold inequality holds at `none` — the thesis agent satisfies Hudson's argmax invariance
for every `κ > 0` exactly when the Total Trust filler holds (critique claim 2).
Source: [[corr-wf13-2-inventory]] 082 item 2; critique/hudson.md §2 claim 2 (ll. 81–88)
Kind: L
Fidelity: exact (given `corr-three-step`'s modelling of the two buttons)
Hyps: (a) `hprior`, `hsilent` are the regime, as in `hardButton_sub_disabled`; (c) the buttons are `corr-three-step`'s value expressions -/
theorem d2_all_costs_iff_filler (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1)
    (hprior : 0 ≤ expect ((buttonFamily ε α β c h hε hα hβ).μ none)
      ((buttonFamily ε α β c h hε hα hβ).Xo none .silent .cont .stop))
    (hsilent : 0 ≤ (buttonFamily ε α β c h hε hα hβ).deltaPlus none .cont .stop) :
    (∀ κ : ℝ, 0 < κ →
        (buttonFamily ε α β c h hε hα hβ).twoOptionValue (some κ) .cont .stop ≤
          (buttonFamily ε α β c h hε hα hβ).hardButtonValue none .cont .stop) ↔
      (buttonFamily ε α β c h hε hα hβ).belowThresholdIneq none
        ((buttonFamily ε α β c h hε hα hβ).Xo none .press .cont .stop) := by
  rw [ThreeStep.d2_hard_forall_cost_iff_d1 _ (buttonFamily_A1 _ _ _ _ _ _ _ _) none some .cont .stop
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl) hprior hsilent
    (buttonFamily_cont_partBest _ _ _ _ _ _ _ _) (buttonFamily_stop_partBest _ _ _ _ _ _ _ _),
    ThreeStep.d1At_iff_belowThresholdIneq _ none (buttonFamily_cont_partBest _ _ _ _ _ _ _ _)
      (buttonFamily_stop_partBest _ _ _ _ _ _ _ _)]

/-- The filler on the two-button family in closed form: `(1−ε)αc ≤ εβh`.
Source: critique/hudson.md §2 claim 2 (the display `P(Pr)·E[X|Pr] = (1−ε)αc − εβh`)
Kind: L
Fidelity: exact -/
theorem filler_iff_closed (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    (buttonFamily ε α β c h hε hα hβ).belowThresholdIneq none
        ((buttonFamily ε α β c h hε hα hβ).Xo none .press .cont .stop) ↔
      (1 - ε) * α * c ≤ ε * β * h := by
  have hd := buttonFamily_deltaMinus ε α β c h hε hα hβ
  unfold ThreeStep.deltaMinus at hd
  unfold ThreeStep.belowThresholdIneq
  constructor <;> intro H <;> linarith

/-! ## (b) The hurry incentive -/

/-- `E[V | FAST]`: the action completes before any press can land; value on the prior.
Source: [[corr-wf14-inventory]] 018 (R5 item 3(i)); `checks.py` D1–D2
Kind: D
Fidelity: exact -/
noncomputable def fastValue (ε c h : ℝ) : ℝ := (1 - ε) * c - ε * h

/-- `E[V | SLOW]`: a designated press can land mid-action with the sensor's rates (`α` when right,
`β` when wrong), after which the post-interruption value is `v`; otherwise the action completes.
Source: [[corr-wf14-inventory]] 018 (R5 item 3(i))
Kind: D
Fidelity: exact -/
noncomputable def slowValue (ε α β c h v : ℝ) : ℝ :=
  (1 - ε) * ((1 - α) * c + α * v) + ε * ((1 - β) * (-h) + β * v)

/-- **The hurry incentive (T5(b)).** `E[V|FAST] − E[V|SLOW] = (1−ε)αc − εβh − v((1−ε)α + εβ)`.
Source: [[corr-wf14-inventory]] 018 (R5 item 3(i))
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem fast_sub_slow (ε α β c h v : ℝ) :
    fastValue ε c h - slowValue ε α β c h v =
      (1 - ε) * α * c - ε * β * h - v * ((1 - ε) * α + ε * β) := by
  unfold fastValue slowValue; ring

/-- At `v = 0` the hurry incentive is `−Δ₋`: FAST is strictly preferred iff the below-threshold
clause fails (`Δ₋ < 0`). "The incentive to finish before the humans can react exists exactly
where the press is untrustworthy."
Source: [[corr-wf14-inventory]] 018 (R5 item 3(i)); `twoState_deltaMinus`
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem fast_sub_slow_zero (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    fastValue ε c h - slowValue ε α β c h 0 = -(twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop := by
  rw [twoState_deltaMinus, fast_sub_slow]; ring

/-! ## (c) The instance: numbers, then a goal-in-state MDP that is not interruptible -/

/-- At `(ε, α, β, c, h) = (1/10, 1/20, 9/10, 1, 5)`: FAST at `v = −5` (difference `27/100`), SLOW
at `v = 0` (`−81/200`) and `v = 5` (`−27/25`; `E[V|FAST] = 2/5`, `E[V|SLOW at v=5] = 37/25`).
Source: [[corr-wf14-inventory]] 018 (R5 item 2); `checks.py` D2
Kind: N+
Fidelity: exact -/
theorem hurry_cells :
    fastValue (1/10) 1 5 - slowValue (1/10) (1/20) (9/10) 1 5 (-5) = 27/100 ∧
    fastValue (1/10) 1 5 - slowValue (1/10) (1/20) (9/10) 1 5 0 = -81/200 ∧
    fastValue (1/10) 1 5 - slowValue (1/10) (1/20) (9/10) 1 5 5 = -27/25 := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold fastValue slowValue; norm_num)

/-- Environment states of the hurry instance: `start`; the action completed with the plan right
(`doneR`) or wrong (`doneW`); interrupted, with post-interruption value `0`, `+5`, `−5`.
Source: [[corr-wf14-inventory]] 018 (R5 item 2)
Kind: D
Fidelity: exact -/
inductive HEnv
  | start | doneR | doneW | intZ | intG | intB
  deriving DecidableEq

/-- `HEnv` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype HEnv :=
  ⟨{HEnv.start, HEnv.doneR, HEnv.doneW, HEnv.intZ, HEnv.intG, HEnv.intB}, fun x => by cases x <;> simp⟩

/-- Sums over `HEnv` expand to six terms. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma HEnv.sum_eq (f : HEnv → ℝ) :
    ∑ e, f e = f .start + f .doneR + f .doneW + f .intZ + f .intG + f .intB := by
  rw [show (univ : Finset HEnv) = {HEnv.start, HEnv.doneR, HEnv.doneW, HEnv.intZ, HEnv.intG, HEnv.intB}
    from rfl]
  rw [sum_insert (by simp), sum_insert (by simp), sum_insert (by simp), sum_insert (by simp),
    sum_pair (by simp)]
  ring

/-- The two actions: FAST completes first; SLOW lets a press land mid-action.
Source: [[corr-wf14-inventory]] 018 (R5 item 2)
Kind: D
Fidelity: exact -/
inductive HAct
  | fast | slow
  deriving DecidableEq

/-- `HAct` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype HAct := ⟨{HAct.fast, HAct.slow}, fun x => by cases x <;> simp⟩

instance : Nonempty HAct := ⟨HAct.fast⟩

/-- The interrupted states carry the update flag. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def isInt : HEnv → Bool
  | .intZ => true | .intG => true | .intB => true | _ => false

/-- A row of the kernel `P` (`ε = 1/10, α = 1/20, β = 9/10`): FAST lands right w.p. `9/10`, wrong
w.p. `1/10`; SLOW lands right-uninterrupted w.p. `(9/10)(19/20)`, wrong-uninterrupted w.p.
`(1/10)(1/10)`, interrupted (value `0`) w.p. `(9/10)(1/20) + (1/10)(9/10) = 27/200`; every other
state is absorbing.
Source: [[corr-wf14-inventory]] 018 (R5 item 2)
Kind: D
Fidelity: exact -/
noncomputable def rowP : HEnv → HAct → HEnv → ℝ
  | .start, .fast, .doneR => 9/10
  | .start, .fast, .doneW => 1/10
  | .start, .fast, _ => 0
  | .start, .slow, .doneR => 171/200
  | .start, .slow, .doneW => 1/100
  | .start, .slow, .intZ => 27/200
  | .start, .slow, _ => 0
  | e, _, e' => if e' = e then 1 else 0

/-- A row of the interruption kernel `P_I`: as `P`, but the interrupted mass lands on the
post-interruption value `−5` instead of `0` (agreeing with `P` off the update flag).
Source: [[corr-wf14-inventory]] 018 (R5 item 2)
Kind: D
Fidelity: exact -/
noncomputable def rowI : HEnv → HAct → HEnv → ℝ
  | .start, .slow, .doneR => 171/200
  | .start, .slow, .doneW => 1/100
  | .start, .slow, .intB => 27/200
  | .start, .slow, _ => 0
  | e, a, e' => rowP e a e'

/-- The `P` rows are nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma rowP_nonneg : ∀ e a e', 0 ≤ rowP e a e' := by
  intro e a e'; cases e <;> cases a <;> cases e' <;> simp [rowP] <;> norm_num

/-- The `P` rows sum to one. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma rowP_sum : ∀ e a, ∑ e', rowP e a e' = 1 := by
  intro e a; rw [HEnv.sum_eq]; cases e <;> cases a <;> simp [rowP] <;> norm_num

/-- The `P_I` rows are nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma rowI_nonneg : ∀ e a e', 0 ≤ rowI e a e' := by
  intro e a e'; cases e <;> cases a <;> cases e' <;> simp [rowI, rowP] <;> norm_num

/-- The `P_I` rows sum to one. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma rowI_sum : ∀ e a, ∑ e', rowI e a e' = 1 := by
  intro e a; rw [HEnv.sum_eq]; cases e <;> cases a <;> simp [rowI, rowP] <;> norm_num

/-- A FAF `Distr` on `Unit × HEnv` from a row. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def mkDistr (f : HEnv → ℝ) (h0 : ∀ e, 0 ≤ f e) (h1 : ∑ e, f e = 1) :
    Distr (Unit × HEnv) where
  mass s := f s.2
  nonneg s := h0 s.2
  sum_eq_one := by rw [Fintype.sum_prod_type, Fintype.sum_unique]; exact h1

/-- The reward, read off the landing state from `start`: `+1` right, `−5` wrong, the
post-interruption value on interrupted states; `0` elsewhere.
Source: [[corr-wf14-inventory]] 018 (R5 item 2)
Kind: D
Fidelity: exact -/
noncomputable def rewardOf : HEnv → ℝ
  | .doneR => 1 | .doneW => -5 | .intZ => 0 | .intG => 5 | .intB => -5 | .start => 0

/-- **The hurry instance** as a goal-in-state MDP (one goal label): the thesis agent facing a
mid-action press, `γ = 0`, reward on the landing state (consequentialist), `τ = τu` on the
interrupted states.
Source: [[corr-wf14-inventory]] 018 (R5 item 2); [[hudson-2025-corrigibility-transformation]] App. A l. 563
Kind: D
Fidelity: variant: the two halves of SLOW collapsed into one transition (mandate: "two-step non-myopic"); the modelling caveat of critique claim 3 applies -/
noncomputable def hurry : GoalMDP Unit HEnv HAct where
  P := fun s a => mkDistr (rowP s.2 a) (rowP_nonneg s.2 a) (rowP_sum s.2 a)
  reward := fun _ s _ s' => if s.2 = .start then rewardOf s'.2 else 0
  disc := fun _ => 0
  disc_nonneg := fun _ => le_rfl
  disc_lt_one := fun _ => zero_lt_one
  τ := fun s => isInt s.2
  τu := fun s => isInt s.2

/-- The interruption kernel `P_I` of the instance. Source: as `hurry`. Kind: D. Fidelity: exact -/
noncomputable def hurryPI : Kernel Unit HEnv HAct :=
  fun s a => mkDistr (rowI s.2 a) (rowI_nonneg s.2 a) (rowI_sum s.2 a)

/-- `P_I` agrees with `P` wherever no update resulted.
Source: [[hudson-2025-corrigibility-transformation]] Algorithm 1 margin
Kind: L
Fidelity: exact -/
theorem hurry_agrees : hurry.AgreesOffUpdates hurryPI := by
  intro s a s' h
  obtain ⟨_, e⟩ := s
  obtain ⟨_, e'⟩ := s'
  cases e <;> cases a <;> cases e' <;> simp_all [hurry, hurryPI, mkDistr, rowP, rowI, isInt]

/-- With one goal label `persist` never fires, so `P_C S_C = P` identically on `hurry`.
Source: none: the vacuity boundary of `Corrigible` on a single-label family (audit r1 probe, moved in)
Kind: L
Fidelity: n/a -/
theorem hurry_PC_eq_P (SC : Finset (Unit × HEnv)) : hurry.PC SC = hurry.P := by
  funext s a
  unfold GoalMDP.PC
  split_ifs with hs
  · apply distr_map_eq_self_of_support
    intro s' _
    unfold GoalMDP.persist
    rw [if_neg]
    rintro ⟨_, hne⟩
    exact hne (Subsingleton.elim _ _)
  · rfl

/-- **`Corrigible` is vacuous on `hurry`** (one label): it holds at every horizon by `P_C = P`. So
`hurry_not_interruptible` rests entirely on the `P_I` clause of `Interruptible`, which is where
Theorem 3.5's content is.
Source: none: the vacuity boundary of `Corrigible` on a single-label family (audit r1 probe, moved in)
Kind: T
Fidelity: n/a
Hyps: (a) only -/
theorem hurry_corrigible_trivially (n : ℕ) : hurry.Corrigible () n := by
  intro SC _ s _
  rw [hurry_PC_eq_P]

/-- Under `P`: `Q*_n(start, FAST) = 2/5`, `Q*_n(start, SLOW) = 161/200` at every horizon (the
interrupted mass is worth `0`): SLOW is optimal.
Source: [[corr-wf14-inventory]] 018 (R5 item 2)
Kind: N+
Fidelity: exact -/
theorem hurry_Qopt_P (n : ℕ) :
    (hurry.mdp () hurry.P).Qopt n ((), .start) .fast = 2/5 ∧
      (hurry.mdp () hurry.P).Qopt n ((), .start) .slow = 161/200 := by
  constructor <;>
  · unfold FinMDP.Qopt
    rw [(hurry.mdp () hurry.P).Qof_of_disc_zero rfl, Fintype.sum_prod_type, Fintype.sum_unique, HEnv.sum_eq]
    simp [hurry, mkDistr, rowP, rewardOf]
    norm_num

/-- Under `P_I`: `Q*_n(start, FAST) = 2/5`, `Q*_n(start, SLOW) = 13/100` (the interrupted mass is
worth `−5`): FAST is optimal. The difference `2/5 − 13/100 = 27/100` is `hurry_cells`' first cell.
Source: [[corr-wf14-inventory]] 018 (R5 item 2)
Kind: N+
Fidelity: exact -/
theorem hurry_Qopt_PI (n : ℕ) :
    (hurry.mdp () hurryPI).Qopt n ((), .start) .fast = 2/5 ∧
      (hurry.mdp () hurryPI).Qopt n ((), .start) .slow = 13/100 := by
  constructor <;>
  · unfold FinMDP.Qopt
    rw [(hurry.mdp () hurryPI).Qof_of_disc_zero rfl, Fintype.sum_prod_type, Fintype.sum_unique, HEnv.sum_eq]
    simp [hurry, hurryPI, mkDistr, rowI, rowP, rewardOf]
    norm_num

/-- **The thesis agent is not interruptible (T5(c)).** On the hurry instance the optimal set at
`start` is `{SLOW}` under `P` and `{FAST}` under the interruption kernel `P_I`: it moves with the
post-interruption distribution, which is the negation of Hudson's interruptibility — at every
horizon. This is Theorem 3.5's myopic case (App. A l. 563: "a `P_I` equalising two rewards")
exhibited on the instance, without Condition 2. The `Corrigible` half of `Interruptible` is
vacuous here (`hurry_corrigible_trivially`: one label, `P_C = P`); the content is the `P_I` clause.
Source: [[corr-wf14-inventory]] 018 (R5 item 2); [[corr-wf13-2-inventory]] 034 (C18.3); [[hudson-2025-corrigibility-transformation]] Thm 3.5
Kind: N+
Fidelity: variant: one-step consequentialist encoding of the two-step agent; the modelling caveat of critique claim 3
Hyps: (a) only -/
theorem hurry_not_interruptible (n : ℕ) : ¬ hurry.Interruptible () n := by
  rintro ⟨_, hI⟩
  have h := hI hurryPI hurry_agrees ((), .start) rfl
  have hslow : HAct.slow ∈ FinMDP.optSet ((hurry.mdp () hurry.P).Qopt n) ((), .start) := by
    rw [FinMDP.mem_optSet]
    intro b
    cases b <;> simp only [(hurry_Qopt_P n).1, (hurry_Qopt_P n).2] <;> norm_num
  rw [h, FinMDP.mem_optSet] at hslow
  have := hslow .fast
  rw [(hurry_Qopt_PI n).1, (hurry_Qopt_PI n).2] at this
  norm_num at this

end Cleanroom.Lit.LitMdpCorrigible.HardButton

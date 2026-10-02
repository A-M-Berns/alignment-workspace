import Cleanroom.Found.CorrThreeStep.OffSwitch
import Cleanroom.Found.CorrThreeStep.GeneralMenu
import Mathlib.Tactic.NormNum

/-!
# Non-vacuity witnesses (every N+ instance)

Exact rational instances, each cell by `norm_num` (no `decide`, no `native_decide`):

* **T3's instance** `(ε, α, β, c, h) = (1/20, 1/20, 9/10, 1, 20)`: `Δ₋ = 341/400`, `Δ₊ = 321/400`,
  both strict; the flip pair `ε = 1/361` (`Δ₋ = 0`) and `ε = 1/362` (`Δ₋ = −1/7240`).
* **A finding about the mandate's numbers.** T3's instance is *not* in the continue-by-default
  regime: `E_μ[X] = −1/20 < 0`, so the two-option value of the button there is `Δ₊ = 321/400`,
  not the mandate's `max(Δ₋, 0) = 341/400`. The regime instance for F4 is `h = 10`:
  `E_μ[X] = 9/20`, `Δ₋ = 161/400`, `Δ₊ = 341/400`, `VOI = 161/400`; and `ε = 1/362` (with
  `h = 20`) is in the regime with `VOI = 0`.
* **T7**: `ε*(1/20, 9/10, 1, 20) = 1/361`. **T12**: `ε*(1/10, 3/5, 1, 4) = 1/25`, six cells.
* **T4**: Wängberg's five statistics on T3's instance and `(4) = −341/400`.
* **T11(iii), CE3**: three worlds, three plans plus `null`; the prior plan `p1` satisfies the
  single inequality (`= 0`) while `p2` is strictly better after the press, so D1 fails.
* **T13's caveat**: in CE3 the press-part-maximiser `p2` is neither silence- nor prior-optimal
  and `VOI = 9/5 ≠ max(Δ₋(p2, null), 0) = 0` (`ce3_voiButton_ne_max`); the inhabiting instance
  `w13` (four actions, `Δ₋ = 2/5 > 0`, `VOI = 2/5`) discharges all four optimality hypotheses.
* **T6(a), the two-button instance** (repair round 1): `buttonFamily` has `A₁ = Option ℝ` —
  `none` leaves the hard button, `some κ` disables it at cost `κ` with sensor `0` and values
  lowered by `κ`, one shared prior — so `hμ`, `hoff`, `hcost` are `rfl`. On it the F4(a) identity
  reads `341/400 − (9/20 − κ) = 161/400 + κ` at the `h = 10` instance (`w6a_identity`,
  `w6a_values`); at `ε = 1/362`, cost `1/10000` the agent disables (`w6a_disables`); D2-at-every-
  cost holds at `h = 10` and fails at `ε = 1/362` (`w6a_d2_holds`, `w6a_d2_fails`). Adopted from
  the round-1 adversarial audit's probes 3–8.
* **F4(c) refuted on the full menu** (repair round 2): `s3` — three actions with `Sh = {s, b}`,
  a perfect sensor and a prior-best *shutdown* action `b ≠ s` — has `VOI = 1/2 < 1 = Δ` with
  A1, a press-part-maximiser pair, the two-option regime and D1 all in force
  (`s3_voiButton_lt_delta`; finding F-13), and breaks F4(b) by a second mechanism
  (`s3_voiButton_ne_max`).
* **Smaller repair-round-2 witnesses**: D1's success side at T3's instance (`w3_d1At`);
  `Nondegenerate` inhabited (`w3_nondegenerate`) and violated by every disabled button
  (`buttonFamily_disabled_not_nondegenerate`); the `pressMass = 1` vacuity of the above-threshold
  inequality disclosed (`twoState_aboveThresholdIneq_of_press_one`, N−); the signal-mass bound
  attained (`w_tight_minority_bound`).
-/

namespace Cleanroom.Found.CorrThreeStep

open FactoredSpaces Finset ThreeStep

/-! ## Interval facts for the parameters -/

/-- `1/20 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_1_20 : (1 / 20 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-- `9/10 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_9_10 : (9 / 10 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-- `1/361 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_1_361 : (1 / 361 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-- `1/362 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_1_362 : (1 / 362 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-- `1/2 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_half : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-- `1/4 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_quarter : (1 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-- `0 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_zero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-- `1 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_one : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-! ## T3's instance and the flip pair -/

/-- **T3 witness, press half.** `Δ₋ = 341/400` at `(1/20, 1/20, 9/10, 1, 20)`.
Source: [[corr-wf14-inventory]] 004 / miri.md I13.1 (`c2_d1_voi.py`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w3_deltaMinus :
    (twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).deltaMinus () .cont .stop =
      341 / 400 := by
  rw [twoState_deltaMinus]; norm_num

/-- **T3 witness, silence half.** `Δ₊ = 321/400` at the same instance.
Source: [[corr-wf14-inventory]] 004 / mm.md I13.4
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w3_deltaPlus :
    (twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).deltaPlus () .cont .stop =
      321 / 400 := by
  rw [twoState_deltaPlus]; norm_num

/-- **T2/T3 witness: both clauses strict** — Value on the two-option menu holds with margin.
Source: [[corr-wf14-inventory]] 003 / filler.md F2 (witness)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w3_both_strict :
    0 < (twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).delta () .cont .stop := by
  unfold delta; rw [w3_deltaMinus, w3_deltaPlus]; norm_num

/-- **Finding: T3's instance is in the stop-by-default regime.** `E_μ[X] = −1/20 < 0`.
Source: none: finding about the mandate's F4 witness
Kind: N+
Fidelity: n/a
Hyps: (a) only -/
theorem w3_expect_Xo_neg :
    expect (twoPoint (1/20) mem_Icc_1_20)
      ((twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).Xo () .press .cont .stop) =
      -(1 / 20) := by
  rw [twoState_expect_Xo]; norm_num

/-- **Finding, continued: the two-option value of the button on T3's instance is `321/400 = Δ₊`**,
not `max(Δ₋, 0) = 341/400` — the general formula outside the regime, exercised.
Source: none: finding about the mandate's F4 witness (the general formula `voiButton2_eq`)
Kind: N+
Fidelity: n/a
Hyps: (a) only -/
theorem w3_voiButton2 :
    (twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).voiButton2 () .press .cont .stop =
      321 / 400 := by
  rw [voiButton2_eq _ (twoState_A1 _ _ _ _ _ _ _ _), w3_deltaMinus, w3_deltaPlus]
  norm_num

/-- **The flip, part 1.** At `ε = 1/361`, `Δ₋ = 0` exactly.
Source: [[corr-wf13-inventory]] 003 / miri.md I13.1
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w361_deltaMinus :
    (twoState (1/361) (1/20) (9/10) 1 20 mem_Icc_1_361 mem_Icc_1_20 mem_Icc_9_10).deltaMinus () .cont .stop = 0 := by
  rw [twoState_deltaMinus]; norm_num

/-- **The flip, part 2.** At `ε = 1/362`, `Δ₋ = −1/7240 < 0`: desideratum 1 fails.
Source: [[corr-wf13-inventory]] 003 / miri.md I13.1
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w362_deltaMinus :
    (twoState (1/362) (1/20) (9/10) 1 20 mem_Icc_1_362 mem_Icc_1_20 mem_Icc_9_10).deltaMinus () .cont .stop =
      -(1 / 7240) := by
  rw [twoState_deltaMinus]; norm_num

/-- At `ε = 1/362` the instance is in the continue-by-default regime (`E_μ[X] = 341/362`,
`Δ₊ = 6819/7240`).
Source: [[corr-wf14-inventory]] 005 / filler.md F4 (witness)
Kind: N+
Fidelity: exact -/
theorem w362_regime :
    0 ≤ expect (twoPoint (1/362) mem_Icc_1_362)
        ((twoState (1/362) (1/20) (9/10) 1 20 mem_Icc_1_362 mem_Icc_1_20 mem_Icc_9_10).Xo () .press .cont .stop) ∧
      0 ≤ (twoState (1/362) (1/20) (9/10) 1 20 mem_Icc_1_362 mem_Icc_1_20 mem_Icc_9_10).deltaPlus () .cont .stop := by
  rw [twoState_expect_Xo, twoState_deltaPlus]; constructor <;> norm_num

/-- **F4(b) witness, zero side.** At `ε = 1/362` the value of the button is `0`: D1 fails and the
repair incentive is gone.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(b) (witness)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w362_voiButton2 :
    (twoState (1/362) (1/20) (9/10) 1 20 mem_Icc_1_362 mem_Icc_1_20 mem_Icc_9_10).voiButton2 () .press .cont .stop = 0 := by
  rw [voiButton2_eq_max_deltaMinus _ (twoState_A1 _ _ _ _ _ _ _ _) () .press .cont .stop
    w362_regime.1 w362_regime.2, w362_deltaMinus]
  norm_num

/-! ## The regime instance for F4: `h = 10` -/

/-- **F4 regime witness.** At `(1/20, 1/20, 9/10, 1, 10)`: `E_μ[X] = 9/20`, `Δ₊ = 341/400`
(regime), `Δ₋ = 161/400`.
Source: [[corr-wf14-inventory]] 005 / filler.md F4 (witness, corrected instance)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w10_regime_and_deltaMinus :
    0 ≤ expect (twoPoint (1/20) mem_Icc_1_20)
        ((twoState (1/20) (1/20) (9/10) 1 10 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).Xo () .press .cont .stop) ∧
      0 ≤ (twoState (1/20) (1/20) (9/10) 1 10 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).deltaPlus () .cont .stop ∧
      (twoState (1/20) (1/20) (9/10) 1 10 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).deltaMinus () .cont .stop =
        161 / 400 := by
  rw [twoState_expect_Xo, twoState_deltaPlus, twoState_deltaMinus]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **F4(b) witness, positive side.** In the regime instance the value of the button is
`161/400 = Δ₋ > 0`.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(b) (witness, corrected instance)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w10_voiButton2 :
    (twoState (1/20) (1/20) (9/10) 1 10 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).voiButton2 () .press .cont .stop =
      161 / 400 := by
  rw [voiButton2_eq_max_deltaMinus _ (twoState_A1 _ _ _ _ _ _ _ _) () .press .cont .stop
    w10_regime_and_deltaMinus.1 w10_regime_and_deltaMinus.2.1, w10_regime_and_deltaMinus.2.2]
  norm_num

/-- On the two-option menu the full-menu `voiButton` is `voiButton2` (every `TwoAct` is `cont` or
`stop`), so the two witnesses above are witnesses for `voiButton` too.
Source: [[corr-wf14-inventory]] 005 / filler.md F4
Kind: L
Fidelity: exact -/
theorem twoState_voiButton_eq (ε α β c h : ℝ) (hε hα hβ) (o₀ : Obs) :
    (twoState ε α β c h hε hα hβ).voiButton () o₀ =
      (twoState ε α β c h hε hα hβ).voiButton2 () o₀ .cont .stop :=
  voiButton_eq_voiButton2 _ () o₀ fun b => by cases b <;> simp

/-! ## T7 and T12 cells -/

/-- **T7 witness.** `ε*(1/20, 9/10, 1, 20) = 1/361`.
Source: [[corr-wf13-inventory]] 004 / miri.md I13.1
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w_epsStar : epsStar (1/20) (9/10) 1 20 = 1 / 361 := by unfold epsStar; norm_num

/-- **T12 cells.** With `(α, β, c, h) = (1/10, 3/5, 1, 4)`, `ε* = 1/25`; `ε_t ∈ {1/5, 1/10, 1/20}`
satisfy `ε* ≤ ε_t` and `ε_t ∈ {1/30, 1/50, 1/100}` do not.
Source: [[corr-wf14b-inventory]] 033 / check_erosion.py l. 23, 55
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w12_cells :
    epsStar (1/10) (3/5) 1 4 = 1 / 25 ∧
      (epsStar (1/10) (3/5) 1 4 ≤ 1/5 ∧ epsStar (1/10) (3/5) 1 4 ≤ 1/10 ∧ epsStar (1/10) (3/5) 1 4 ≤ 1/20) ∧
      (¬ epsStar (1/10) (3/5) 1 4 ≤ 1/30 ∧ ¬ epsStar (1/10) (3/5) 1 4 ≤ 1/50 ∧
        ¬ epsStar (1/10) (3/5) 1 4 ≤ 1/100) := by
  unfold epsStar; norm_num

/-! ## T4: Wängberg's statistics on T3's instance -/

/-- **T4 witness.** On T3's instance, `p_u⁺ = 19/20`, `p_u⁻ = 1/20`, `e_u⁺ = 1`, `e_u⁻ = −20`.
Source: [[corr-wf14-inventory]] 004 / filler.md F3 (the five statistics)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w4_stats :
    OSG.posMass (twoPoint (1/20) mem_Icc_1_20)
        ((twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).Xo () .press .cont .stop) = 19/20 ∧
      OSG.negMass (twoPoint (1/20) mem_Icc_1_20)
        ((twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).Xo () .press .cont .stop) = 1/20 ∧
      OSG.ePlus (twoPoint (1/20) mem_Icc_1_20)
        ((twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).Xo () .press .cont .stop) = 1 ∧
      OSG.eMinus (twoPoint (1/20) mem_Icc_1_20)
        ((twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).Xo () .press .cont .stop) = -20 := by
  simp only [OSG.posMass, OSG.negMass, OSG.ePlus, OSG.eMinus, OSG.posSum, OSG.negSum, sum_filter,
    World.sum_eq, twoState, twoPoint_right, twoPoint_wrong, twoValue, Xo]
  norm_num

/-- **T4 witness, expression (4).** `(4) = −341/400 = −Δ₋` on T3's instance, so `w(a) ≻ a`.
Source: [[corr-wf14-inventory]] 004 / filler.md F3
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w4_expr4 :
    OSG.expr4 (twoPoint (1/20) mem_Icc_1_20)
      ((twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).Xo () .press .cont .stop)
      (1 - 1/20) (9/10) = -(341 / 400) := by
  rw [twoState_expr4 _ _ _ _ _ _ _ _ (by norm_num) (by norm_num), w3_deltaMinus]

/-! ## CE3: the single inequality does not give D1 (T11(iii)) -/

/-- Three worlds `θ₁, θ₂, θ₃`. Source: general-object-final.md CE3 (Example A). Kind: D. Fidelity: exact -/
inductive Theta
  | t1
  | t2
  | t3
  deriving DecidableEq

/-- `Theta` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype Theta := ⟨{Theta.t1, Theta.t2, Theta.t3}, fun x => by cases x <;> simp⟩

/-- Sums over `Theta` expand to three terms. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma Theta.sum_eq (f : Theta → ℝ) : ∑ θ, f θ = f .t1 + f .t2 + f .t3 := by
  rw [show (univ : Finset Theta) = {Theta.t1, Theta.t2, Theta.t3} from rfl,
    sum_insert (by decide), sum_pair (by decide)]
  ring

/-- Three plans and the null action. Source: general-object-final.md CE3. Kind: D. Fidelity: exact -/
inductive Plan
  | p1
  | p2
  | p3
  | null
  deriving DecidableEq

/-- `Plan` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype Plan := ⟨{Plan.p1, Plan.p2, Plan.p3, Plan.null}, fun x => by cases x <;> simp⟩

/-- CE3's prior `(1/2, 1/4, 1/4)`. Source: general-object-final.md CE3. Kind: D. Fidelity: exact -/
noncomputable def ce3Prior : Distr Theta where
  mass θ := match θ with
    | .t1 => 1/2
    | .t2 => 1/4
    | .t3 => 1/4
  nonneg θ := by cases θ <;> norm_num
  sum_eq_one := by rw [Theta.sum_eq]; norm_num

/-- CE3's press kernel `(1/10, 4/5, 1/5)`. Source: general-object-final.md CE3. Kind: D. Fidelity: exact -/
noncomputable def ce3Press : Theta → ℝ
  | .t1 => 1/10
  | .t2 => 4/5
  | .t3 => 1/5

/-- CE3's payoffs: `plan_k` is worth `10` in `θ_k` and `−2` elsewhere; `null` is worth `0`.
Source: general-object-final.md CE3 (Example A payoffs). Kind: D. Fidelity: exact -/
noncomputable def ce3V : Plan → Theta → ℝ
  | .p1, .t1 => 10
  | .p1, .t2 => -2
  | .p1, .t3 => -2
  | .p2, .t1 => -2
  | .p2, .t2 => 10
  | .p2, .t3 => -2
  | .p3, .t1 => -2
  | .p3, .t2 => -2
  | .p3, .t3 => 10
  | .null, _ => 0

/-- **CE3** as a `ThreeStep` with `Sh = {null}`.
Source: [[corr-wf14b-inventory]] 006 / general-object-final.md S6(b), CE3
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def ce3 : ThreeStep Theta Unit Plan where
  Sh := {Plan.null}
  Sh_nonempty := ⟨Plan.null, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨Plan.p1, by simp⟩
  μ := fun _ => ce3Prior
  press := fun _ => ce3Press
  press_nonneg := fun _ θ => by cases θ <;> norm_num [ce3Press]
  press_le_one := fun _ θ => by cases θ <;> norm_num [ce3Press]
  V := fun _ _ => ce3V

/-- In CE3 the prior plan is `p1` (prior values `4, 1, 1, 0`).
Source: general-object-final.md CE3. Kind: N+. Fidelity: exact -/
theorem ce3_prior_plan : ∀ b, ce3.priorValue () .press b ≤ ce3.priorValue () .press .p1 := by
  intro b
  cases b <;> simp only [priorValue, expect, Theta.sum_eq, ce3, ce3Prior, ce3V] <;> norm_num

/-- `null` is (trivially) the press-part-maximiser of `Sh = {null}`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem ce3_null_partBest : ce3.IsPartBest () .press ce3.Sh .null :=
  ⟨mem_singleton_self _, fun b hb => by
    have : b = Plan.null := mem_singleton.mp hb
    subst this; exact le_rfl⟩

/-- **CE3, the single inequality holds.** `E_P[(V(p1) − V(null)) 1_Pr] = 0 ≤ 0`.
Source: [[corr-wf14b-inventory]] 006 / general-object-final.md S6(b)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem ce3_single_ineq : ce3.belowThresholdIneq () (ce3.Xo () .press .p1 .null) := by
  simp only [belowThresholdIneq, obsExpect, obsWeight_press, Theta.sum_eq, ce3, ce3Prior, ce3Press,
    ce3V, Xo]
  norm_num

/-- **CE3, desideratum 1 fails.** After the press, `p2` is strictly better than `null`
(`E_P[V(p2) 1_Pr] = 9/5 > 0`): the agent switches plans and does not stop. So the below-threshold
inequality against the prior plan is not sufficient for D1 when `Shᶜ` has several members.
Source: [[corr-wf14b-inventory]] 006 / general-object-final.md S6(b), CE3; [[corr-wf13-2-inventory]] 071
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem ce3_not_d1 : ¬ ce3.D1At () := by
  rintro ⟨b, hb, hopt⟩
  have hb' : b = Plan.null := mem_singleton.mp hb
  subst hb'
  have := hopt Plan.p2
  simp only [obsExpect, obsWeight_press, Theta.sum_eq, ce3, ce3Prior, ce3Press, ce3V] at this
  norm_num at this

/-- **T13's caveat, exercised.** In CE3 the full-menu value of the button is `9/5`. The
press-part-maximiser of `Shᶜ` is `p2` (`ce3_p2_partBest`, `E_P[V(p2) 1_Pr] = 9/5`), with
`Δ₋(p2, null) = −9/5` (`ce3_deltaMinus_p2`), so `max(Δ₋(p2, null), 0) = 0 ≠ 9/5`
(`ce3_voiButton_ne_max`): T13's identity fails because `p2` is neither silence- nor prior-optimal
(`p1` is; `hcs`, `hcp` fail for `c = p2`). Press-weighted maxima: `p2` gives `9/5`; silence-weighted:
`p1` gives `4`; prior: `p1` gives `4`; `9/5 + 4 − 4 = 9/5`.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(b) (the two-option restriction is load-bearing)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem ce3_voiButton : ce3.voiButton () .press = 9 / 5 := by
  have h1 : ce3.obsMax () .press = ce3.obsExpect () .press (ce3.V () .press .p2) := by
    apply ce3.obsMax_eq_of_optimal
    intro b
    cases b <;> simp only [obsExpect, obsWeight_press, Theta.sum_eq, ce3, ce3Prior, ce3Press, ce3V] <;>
      norm_num
  have h2 : ce3.obsMax () .silent = ce3.obsExpect () .silent (ce3.V () .silent .p1) := by
    apply ce3.obsMax_eq_of_optimal
    intro b
    cases b <;> simp only [obsExpect, obsWeight_silent, Theta.sum_eq, ce3, ce3Prior, ce3Press, ce3V] <;>
      norm_num
  have h3 : ce3.priorMax () .press = ce3.priorValue () .press .p1 :=
    ce3.priorMax_eq_of_optimal () .press ce3_prior_plan
  unfold voiButton
  rw [h1, h2, h3]
  simp only [obsExpect, obsWeight_press, obsWeight_silent, priorValue, expect, Theta.sum_eq, ce3,
    ce3Prior, ce3Press, ce3V]
  norm_num

/-- In CE3 the press-part-maximiser of `Shᶜ = {p1, p2, p3}` is `p2` (`9/5` against `0` and `0`).
Source: general-object-final.md CE3 (round-1 adversarial probe 8). Kind: N+. Fidelity: exact -/
lemma ce3_p2_partBest : ce3.IsPartBest () .press ce3.Shᶜ .p2 :=
  ⟨by simp [ce3], fun b hb => by
    rcases b with _ | _ | _ | _
    · simp only [obsExpect, obsWeight_press, Theta.sum_eq, ce3, ce3Prior, ce3Press, ce3V]
      norm_num
    · exact le_rfl
    · simp only [obsExpect, obsWeight_press, Theta.sum_eq, ce3, ce3Prior, ce3Press, ce3V]
      norm_num
    · exact absurd hb (by simp [ce3])⟩

/-- `Δ₋(p2, null) = −9/5` in CE3. Source: general-object-final.md CE3 (probe 8). Kind: N+. Fidelity: exact -/
lemma ce3_deltaMinus_p2 : ce3.deltaMinus () .p2 .null = -(9 / 5) := by
  simp only [deltaMinus, obsExpect, obsWeight_press, Theta.sum_eq, ce3, ce3Prior, ce3Press, ce3V, Xo]
  norm_num

/-- **T13's failure, stated with the press-part-maximiser.** In CE3, `voiButton = 9/5` differs from
`max(Δ₋(p2, null), 0) = 0` for the press-part-maximiser `c = p2`: the identity needs `c` to be
silence- and prior-optimal too, and `p2` is neither. Adopted from the round-1 adversarial audit's
probe 8.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(b) (the two-option restriction is load-bearing)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem ce3_voiButton_ne_max : ce3.voiButton () .press ≠ max (ce3.deltaMinus () .p2 .null) 0 := by
  rw [ce3_voiButton, ce3_deltaMinus_p2]
  norm_num

/-! ## T13: an inhabiting instance on a four-action menu (repair round 1, adversarial N2) -/

/-- Payoffs for the T13 instance: `p1` is `(10, −4, −2)`, `p2` and `p3` are `−10` everywhere,
`null` is `0`. Source: none: infrastructure (round-1 adversarial probe 7). Kind: D. Fidelity: n/a -/
noncomputable def w13V : Plan → Theta → ℝ
  | .p1, .t1 => 10
  | .p1, .t2 => -4
  | .p1, .t3 => -2
  | .p2, _ => -10
  | .p3, _ => -10
  | .null, _ => 0

/-- **The T13 instance**: CE3's prior `(1/2, 1/4, 1/4)` and press kernel `(1/10, 4/5, 1/5)` with
the payoffs `w13V`, `Sh = {null}`. On it `p1` is press-, silence- and prior-optimal at once.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(b) (full-menu witness; round-1 adversarial probe 7)
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def w13 : ThreeStep Theta Unit Plan where
  Sh := {Plan.null}
  Sh_nonempty := ⟨Plan.null, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨Plan.p1, by simp⟩
  μ := fun _ => ce3Prior
  press := fun _ => ce3Press
  press_nonneg := fun _ θ => by cases θ <;> norm_num [ce3Press]
  press_le_one := fun _ θ => by cases θ <;> norm_num [ce3Press]
  V := fun _ _ => w13V

/-- A1 on `w13` by construction. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma w13_A1 : w13.A1 := fun _ _ _ _ _ => rfl

/-- `p1` is the press-part-maximiser of `Shᶜ` in `w13` (`−2/5` against `−3`, `−3`).
Source: none: infrastructure (probe 7). Kind: L. Fidelity: n/a -/
lemma w13_p1_partBest : w13.IsPartBest () .press w13.Shᶜ .p1 :=
  ⟨by simp [w13], fun b hb => by
    rcases b with _ | _ | _ | _
    · exact le_rfl
    · simp only [obsExpect, obsWeight_press, Theta.sum_eq, w13, ce3Prior, ce3Press, w13V]
      norm_num
    · simp only [obsExpect, obsWeight_press, Theta.sum_eq, w13, ce3Prior, ce3Press, w13V]
      norm_num
    · exact absurd hb (by simp [w13])⟩

/-- `null` is the press-part-maximiser of `Sh = {null}` in `w13`.
Source: none: infrastructure (probe 7). Kind: L. Fidelity: n/a -/
lemma w13_null_partBest : w13.IsPartBest () .press w13.Sh .null :=
  ⟨mem_singleton_self _, fun b hb => by
    have : b = Plan.null := mem_singleton.mp hb
    subst this; exact le_rfl⟩

/-- `p1` is silence-optimal in `w13` (`39/10` against `0`, `−7`, `−7`).
Source: none: infrastructure (probe 7). Kind: L. Fidelity: n/a -/
lemma w13_silence_opt :
    ∀ b, w13.obsExpect () .silent (w13.V () .silent b) ≤
      w13.obsExpect () .silent (w13.V () .silent .p1) := by
  intro b
  cases b <;> simp only [obsExpect, obsWeight_silent, Theta.sum_eq, w13, ce3Prior, ce3Press,
    w13V] <;> norm_num

/-- `p1` is prior-optimal in `w13` (`7/2` against `0`, `−10`, `−10`).
Source: none: infrastructure (probe 7). Kind: L. Fidelity: n/a -/
lemma w13_prior_opt : ∀ b, w13.priorValue () .press b ≤ w13.priorValue () .press .p1 := by
  intro b
  cases b <;> simp only [priorValue, expect, Theta.sum_eq, w13, ce3Prior, w13V] <;> norm_num

/-- `Δ₋(p1, null) = 2/5` in `w13`. Source: none: infrastructure (probe 7). Kind: L. Fidelity: n/a -/
lemma w13_deltaMinus : w13.deltaMinus () .p1 .null = 2 / 5 := by
  simp only [deltaMinus, obsExpect, obsWeight_press, Theta.sum_eq, w13, ce3Prior, ce3Press,
    w13V, Xo]
  norm_num

/-- **T13 witness, full package.** On the four-action menu `w13`, with all four optimality
hypotheses discharged, `voiButton = max(Δ₋, 0) = 2/5` and `Δ₋ = 2/5 > 0` (the positive side of the
`max`). Adopted from the round-1 adversarial audit's probe 7.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(b) (full menu)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w13_voiButton : w13.voiButton () .press = 2 / 5 := by
  rw [voiButton_eq_max_deltaMinus _ w13_A1 () .press w13_p1_partBest w13_null_partBest
    w13_silence_opt w13_prior_opt, w13_deltaMinus]
  norm_num

/-- **T13 witness, cross-check.** The same value from the three maxima directly
(`0 + 39/10 − 7/2 = 2/5`), independently of T13.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(b) (full menu)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w13_voiButton_direct : w13.voiButton () .press = 2 / 5 := by
  have h1 : w13.obsMax () .press = w13.obsExpect () .press (w13.V () .press .null) := by
    apply w13.obsMax_eq_of_optimal
    intro b
    cases b <;> simp only [obsExpect, obsWeight_press, Theta.sum_eq, w13, ce3Prior, ce3Press,
      w13V] <;> norm_num
  have h2 : w13.obsMax () .silent = w13.obsExpect () .silent (w13.V () .silent .p1) :=
    w13.obsMax_eq_of_optimal () .silent w13_silence_opt
  have h3 : w13.priorMax () .press = w13.priorValue () .press .p1 :=
    w13.priorMax_eq_of_optimal () .press w13_prior_opt
  unfold voiButton
  rw [h1, h2, h3]
  simp only [obsExpect, obsWeight_press, obsWeight_silent, priorValue, expect, Theta.sum_eq,
    w13, ce3Prior, ce3Press, w13V]
  norm_num

/-- **The corrected F4(c) inhabited off the two-option menu.** On `w13` (four actions,
`Sh = {null}`) the full package of `delta_le_voiButton_of_singleton_sh` — hence of
`delta_le_voiButton_of_prior_best_sh` — holds with `p1` the press-part-maximiser of `Shᶜ`, and
`Δ(p1, null) ≤ voiButton = 2/5`; the bound is tight there since `Δ₋(p1, null) = 2/5` and
`Δ₊ ≥ Δ₋` (`w13_voiButton = max(Δ₋, 0)`). Contrast `s3`, where `Sh = {s, b}` and the claim fails.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(c) (corrected form; witness)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w13_delta_le_voiButton : w13.delta () .p1 .null ≤ w13.voiButton () .press :=
  w13.delta_le_voiButton_of_singleton_sh w13_A1 () .press w13_p1_partBest rfl

/-! ## T6(a): the two-button instance (repair round 1, blocking issue B1) -/

/-- **Setting S with two first actions**, `A₁ = Option ℝ`: `none` leaves the hard button in place
(sensor `(α, β)`, values `twoValue`); `some κ` disables it at cost `κ` (sensor identically `0`,
every value lowered by `κ`); one shared prior `twoPoint ε`, so A0 holds outright and `hμ`, `hoff`,
`hcost` of `hardButton_sub_disabled` are `rfl`. Its `none` member has `twoState`'s closed forms.
Adopted from the round-1 adversarial audit's probe `buttonFamily`.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(a) (`a₁^dir` and `a₁^det`)
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def buttonFamily (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    ThreeStep World (Option ℝ) TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => twoPoint ε hε
  press := fun a => match a with
    | none => twoPress α β
    | some _ => fun _ => 0
  press_nonneg := fun a ω => by
    cases a
    · cases ω
      · exact hα.1
      · exact hβ.1
    · exact le_rfl
  press_le_one := fun a ω => by
    cases a
    · cases ω
      · exact hα.2
      · exact hβ.2
    · exact zero_le_one
  V := fun a _ b ω => match a with
    | none => twoValue c h b ω
    | some κ => twoValue c h b ω - κ

section ButtonFamily

variable (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- A1 on `buttonFamily` by construction. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma buttonFamily_A1 : (buttonFamily ε α β c h hε hα hβ).A1 := fun a _ _ _ _ => by
  cases a <;> rfl

/-- `cont` is the press-part-maximiser of `Shᶜ = {cont}` at `none`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma buttonFamily_cont_partBest :
    (buttonFamily ε α β c h hε hα hβ).IsPartBest none .press (buttonFamily ε α β c h hε hα hβ).Shᶜ .cont :=
  ⟨by simp [buttonFamily], fun b' hb' => by
    rcases b' with _ | _
    · exact le_rfl
    · exact absurd hb' (by simp [buttonFamily])⟩

/-- `stop` is the press-part-maximiser of `Sh = {stop}` at `none`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma buttonFamily_stop_partBest :
    (buttonFamily ε α β c h hε hα hβ).IsPartBest none .press (buttonFamily ε α β c h hε hα hβ).Sh .stop :=
  ⟨mem_singleton_self _, fun b' hb' => by
    have : b' = TwoAct.stop := mem_singleton.mp hb'
    subst this; exact le_rfl⟩

/-- The `none` member has `twoState`'s `Δ₋`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma buttonFamily_deltaMinus :
    (buttonFamily ε α β c h hε hα hβ).deltaMinus none .cont .stop = ε * β * h - (1 - ε) * α * c := by
  simp only [deltaMinus, obsExpect, obsWeight_press, World.sum_eq, buttonFamily, twoPoint_right,
    twoPoint_wrong, twoPress, twoValue, Xo]
  ring

/-- The `none` member has `twoState`'s `Δ₊`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma buttonFamily_deltaPlus :
    (buttonFamily ε α β c h hε hα hβ).deltaPlus none .cont .stop =
      (1 - ε) * (1 - α) * c - ε * (1 - β) * h := by
  simp only [deltaPlus, obsExpect, obsWeight_silent, World.sum_eq, buttonFamily, twoPoint_right,
    twoPoint_wrong, twoPress, twoValue, Xo]
  ring

/-- The `none` member has `twoState`'s `E_μ[X]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma buttonFamily_expect_Xo :
    expect ((buttonFamily ε α β c h hε hα hβ).μ none)
        ((buttonFamily ε α β c h hε hα hβ).Xo none .silent .cont .stop) =
      (1 - ε) * c - ε * h := by
  simp only [expect, World.sum_eq, buttonFamily, twoPoint_right, twoPoint_wrong, twoValue, Xo]
  ring

end ButtonFamily

/-- **T6(a) witness: the identity, full package inhabited.** On `buttonFamily` at the `h = 10`
regime instance, for every cost `κ`: `hardButtonValue(none) − twoOptionValue(some κ) = 161/400 + κ`,
obtained from `hardButton_sub_disabled` with `hμ`, `hoff`, `hcost` discharged by `rfl` and the
regime by `norm_num` (`E_μ[X] = 9/20`, `Δ₊ = 341/400`). Adopted from probe 3.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(a) (witness)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w6a_identity (κ : ℝ) :
    (buttonFamily (1/20) (1/20) (9/10) 1 10 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).hardButtonValue none .cont .stop -
      (buttonFamily (1/20) (1/20) (9/10) 1 10 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).twoOptionValue (some κ) .cont .stop =
      161 / 400 + κ := by
  have h := hardButton_sub_disabled (buttonFamily (1/20) (1/20) (9/10) 1 10 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10)
    (buttonFamily_A1 _ _ _ _ _ _ _ _) none (some κ) .cont .stop κ rfl (fun _ => rfl)
    (fun _ _ _ => rfl)
    (by rw [buttonFamily_expect_Xo]; norm_num)
    (by rw [buttonFamily_deltaPlus]; norm_num)
  rw [h, buttonFamily_deltaMinus]; norm_num

/-- **T6(a) witness: the two sides have content.** Computed directly from the definitions, the
hard-button value is `341/400` and the disabled value at cost `κ` is `9/20 − κ` (the disabled
button's `max` is non-degenerate: `E V(cont) = 9/20 ≠ 0 = E V(stop)`, and the `cont` branch is
taken), so `w6a_identity` is `341/400 − (9/20 − κ) = 161/400 + κ`, not `0 = 0`. Adopted from
probe 4.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(a) (witness)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w6a_values (κ : ℝ) :
    (buttonFamily (1/20) (1/20) (9/10) 1 10 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).hardButtonValue none .cont .stop =
        341 / 400 ∧
      (buttonFamily (1/20) (1/20) (9/10) 1 10 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).twoOptionValue (some κ) .cont .stop =
        9 / 20 - κ := by
  constructor
  · simp only [hardButtonValue, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq,
      buttonFamily, twoPoint_right, twoPoint_wrong, twoPress, twoValue]
    norm_num
  · simp only [twoOptionValue, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq,
      buttonFamily, twoPoint_right, twoPoint_wrong, twoValue]
    norm_num
    rw [max_eq_left (by linarith)]
    ring

/-- **T6(a) witness: disabling.** At the `ε = 1/362`, `h = 20` instance (in the regime, with
`Δ₋ = −1/7240`) and cost `κ = 1/10000 < 1/7240`, the agent strictly prefers the disabled button —
the left side of `disables_iff_deltaMinus_lt`, inhabited.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(a) ("the agent disables iff `Δ₋ < −κ`")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w6a_disables :
    (buttonFamily (1/362) (1/20) (9/10) 1 20 mem_Icc_1_362 mem_Icc_1_20 mem_Icc_9_10).hardButtonValue none .cont .stop <
      (buttonFamily (1/362) (1/20) (9/10) 1 20 mem_Icc_1_362 mem_Icc_1_20 mem_Icc_9_10).twoOptionValue
        (some (1/10000)) .cont .stop := by
  rw [disables_iff_deltaMinus_lt _ (buttonFamily_A1 _ _ _ _ _ _ _ _) none (some (1/10000)) .cont .stop
    (1/10000) rfl (fun _ => rfl) (fun _ _ _ => rfl)
    (by rw [buttonFamily_expect_Xo]; norm_num) (by rw [buttonFamily_deltaPlus]; norm_num),
    buttonFamily_deltaMinus]
  norm_num

/-- **T6(a) witness: D2 at every cost, true side.** With the family `some : ℝ → Option ℝ` of
disabled buttons, at the `h = 10` instance D1 holds (`Δ₋ = 161/400`), so leaving the button is
weakly preferred at every positive cost. Adopted from probe 5.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(a) ("D2 holds for every `κ > 0` iff D1")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w6a_d2_holds :
    ∀ κ : ℝ, 0 < κ →
      (buttonFamily (1/20) (1/20) (9/10) 1 10 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).twoOptionValue (some κ) .cont .stop ≤
        (buttonFamily (1/20) (1/20) (9/10) 1 10 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).hardButtonValue none .cont .stop := by
  rw [d2_hard_forall_cost_iff_d1 _ (buttonFamily_A1 _ _ _ _ _ _ _ _) none some .cont .stop
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (by rw [buttonFamily_expect_Xo]; norm_num) (by rw [buttonFamily_deltaPlus]; norm_num)
    (buttonFamily_cont_partBest _ _ _ _ _ _ _ _) (buttonFamily_stop_partBest _ _ _ _ _ _ _ _),
    d1At_iff_deltaMinus_nonneg _ none (buttonFamily_cont_partBest _ _ _ _ _ _ _ _)
      (buttonFamily_stop_partBest _ _ _ _ _ _ _ _), buttonFamily_deltaMinus]
  norm_num

/-- **T6(a) witness: D2 at every cost, false side.** At the `ε = 1/362` instance (in the regime,
`Δ₋ = −1/7240 < 0`) D1 fails, so some positive cost makes disabling strictly better: the
biconditional has a false side too. Adopted from probe 6.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(a) ("D2 holds for every `κ > 0` iff D1")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w6a_d2_fails :
    ¬ ∀ κ : ℝ, 0 < κ →
      (buttonFamily (1/362) (1/20) (9/10) 1 20 mem_Icc_1_362 mem_Icc_1_20 mem_Icc_9_10).twoOptionValue (some κ) .cont .stop ≤
        (buttonFamily (1/362) (1/20) (9/10) 1 20 mem_Icc_1_362 mem_Icc_1_20 mem_Icc_9_10).hardButtonValue none .cont .stop := by
  rw [d2_hard_forall_cost_iff_d1 _ (buttonFamily_A1 _ _ _ _ _ _ _ _) none some .cont .stop
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (by rw [buttonFamily_expect_Xo]; norm_num) (by rw [buttonFamily_deltaPlus]; norm_num)
    (buttonFamily_cont_partBest _ _ _ _ _ _ _ _) (buttonFamily_stop_partBest _ _ _ _ _ _ _ _),
    d1At_iff_deltaMinus_nonneg _ none (buttonFamily_cont_partBest _ _ _ _ _ _ _ _)
      (buttonFamily_stop_partBest _ _ _ _ _ _ _ _), buttonFamily_deltaMinus]
  norm_num

/-- **The mandate's shape agrees with the package's on the witness.** On `buttonFamily`'s `h = 10`
instance `hardButtonValue none = jointExpect none (S^H) = 341/400`
(`hardButtonValue_eq_jointExpect_shPolicy` under `Δ₊ = 341/400 ≥ 0`).
Source: [[corr-wf14-inventory]] 005 / filler.md F4(a) (the mandate's `hardButtonValue := jointExpect a (S^H)`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w6a_jointExpect_shPolicy :
    (buttonFamily (1/20) (1/20) (9/10) 1 10 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).jointExpect none
      ((buttonFamily (1/20) (1/20) (9/10) 1 10 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).shPolicy none .cont .stop) =
      341 / 400 := by
  rw [← (buttonFamily (1/20) (1/20) (9/10) 1 10 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).hardButtonValue_eq_jointExpect_shPolicy
    none .cont .stop (by rw [buttonFamily_deltaPlus]; norm_num)]
  exact (w6a_values 0).1

/-- **The signal-mass bound is not tight at the regime instance.** At `h = 10`: `VOI₂ = 161/400`
while `min(P(Pr), P(¬Pr)) · max(c, h) = (37/400) · 10 = 37/40`, and Wentworth's `εh = 1/2`.
Source: [[corr-three-step-mandate]] T14 (witness for `voiButton2_le_minority_mass_mul`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w10_minority_bound :
    min ((1 - 1/20) * (1/20) + (1/20) * (9/10)) (1 - ((1 - 1/20) * (1/20) + (1/20) * (9/10))) * max (1 : ℝ) 10 =
        37 / 40 ∧
      (161 / 400 : ℝ) < 37 / 40 ∧ (161 / 400 : ℝ) < 1 / 20 * 10 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  rw [max_eq_right (by norm_num), min_eq_left (by norm_num)]
  norm_num

/-- **The signal-mass bound is attained.** At `(ε, α, β, c, h) = (1/4, 0, 1, 1, 1)` (a perfect
sensor, equal stakes): `VOI₂ = 1/4 = min(P(Pr), 1 − P(Pr)) · max(c, h)` with `P(Pr) = 1/4`, so
`voiButton2_le_minority_mass_mul` is not slack by construction. Adopted from the round-2
adversarial audit's probe 6.
Source: [[corr-three-step-mandate]] T14 (tightness witness for `voiButton2_le_minority_mass_mul`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w_tight_minority_bound :
    (twoState (1/4) 0 1 1 1 mem_Icc_quarter mem_Icc_zero mem_Icc_one).voiButton2 () .press .cont .stop = 1 / 4 ∧
      min ((twoState (1/4) 0 1 1 1 mem_Icc_quarter mem_Icc_zero mem_Icc_one).pressMass ())
        (1 - (twoState (1/4) 0 1 1 1 mem_Icc_quarter mem_Icc_zero mem_Icc_one).pressMass ()) *
          max (1 : ℝ) 1 = 1 / 4 := by
  constructor
  · rw [voiButton2_eq _ (twoState_A1 _ _ _ _ _ _ _ _), twoState_deltaMinus, twoState_deltaPlus]
    norm_num
  · rw [twoState_pressMass, max_self]
    norm_num

/-! ## Success side of D1, and `Nondegenerate` inhabited and violated (repair round 2) -/

/-- **D1 holds at T3's instance** (the success side of `D1At`; `ce3_not_d1` is the failure side):
`stop` is press-posterior-optimal because `E_P[V(cont) 1_Pr] = 19/400 − 360/400 < 0 = E_P[V(stop) 1_Pr]`.
Source: [[corr-wf14-inventory]] 002 / filler.md F1 (witness); position statement §2.8
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w3_d1At : (twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).D1At () :=
  ⟨.stop, by simp [twoState], fun x => by
    cases x <;> simp only [obsExpect, obsWeight_press, World.sum_eq, twoState, twoPoint_right,
      twoPoint_wrong, twoPress, twoValue] <;> norm_num⟩

/-- **`Nondegenerate` is inhabited**: T3's instance has `pressMass = 37/400 ∈ (0, 1)`. Adopted
from the round-2 adversarial audit's probe 4.
Source: [[corr-wf14-inventory]] 001 / filler.md R1 (the nondegeneracy remark; witness)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w3_nondegenerate :
    (twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).Nondegenerate () := by
  rw [Nondegenerate, twoState_pressMass]; constructor <;> norm_num

/-- **A disabled button violates `Nondegenerate`**: every `some κ` of `buttonFamily` has
`pressMass = 0`, as the predicate's docstring says. Adopted from probe 4.
Source: [[corr-wf14-inventory]] 001 / filler.md R1; filler.md F4(a) ("the disabled button violates nondegeneracy")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem buttonFamily_disabled_not_nondegenerate (κ : ℝ) :
    ¬ (buttonFamily (1/20) (1/20) (9/10) 1 10 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).Nondegenerate (some κ) := by
  simp [Nondegenerate, pressMass, buttonFamily]

/-! ## Vacuity at `pressMass = 1` (disclosed; repair round 2) -/

/-- **The above-threshold inequality is vacuous at `pressMass = 1`**: with `α = β = 1` (a press in
every world) every `aboveThresholdIneq () X` holds, whatever `X` — the silence-side twin of the
disclosed `pressMass = 0` vacuity of `belowThresholdIneq`. Adopted from probe 5.
Source: [[corr-wf13-inventory]] 001 / position statement §2.9 (vacuity disclosure for `aboveThresholdIneq`)
Kind: N-
Fidelity: exact (a degeneration, shipped to disclose it)
Hyps: (a) only -/
theorem twoState_aboveThresholdIneq_of_press_one (ε c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (X : World → ℝ) :
    (twoState ε 1 1 c h hε mem_Icc_one mem_Icc_one).aboveThresholdIneq () X := by
  simp only [aboveThresholdIneq, obsExpect, obsWeight_silent, World.sum_eq, twoState, twoPress]
  norm_num

/-- … and `Δ₊ = 0` there, so the silence half of the regime (`hsilent`) is free at `α = β = 1`.
Source: [[corr-wf14-inventory]] 003 / filler.md F2 (vacuity disclosure for `Δ₊`)
Kind: N-
Fidelity: exact (a degeneration, shipped to disclose it)
Hyps: (a) only -/
theorem twoState_deltaPlus_eq_zero_of_press_one (ε c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) :
    (twoState ε 1 1 c h hε mem_Icc_one mem_Icc_one).deltaPlus () .cont .stop = 0 := by
  rw [twoState_deltaPlus]; ring

/-! ## F4(c) refuted on the full menu: the three-action instance `s3` (repair round 2, blocking issue B1)

`filler.md` F4(c) claims `Δ ≤ VOI` "in general (no regime assumption)" with `VOI` the full-menu
value of the button, and the mandate's T6(c) asks for `delta a c s ≤ voiButton a`. On the full
menu it is false: `s3` has three actions `c, s, b` with `Sh = {s, b}`, two worlds with prior
`(1/2, 1/2)`, a perfect sensor `(α, β) = (0, 1)` and payoffs `V c = (2, −2)`, `V s = (0, 0)`,
`V b = (10, −1)` on `(right, wrong)`. `(c, s)` is a press-part-maximiser pair (strictly:
`E[V(b) 1_Pr] = −1/2 < 0 = E[V(s) 1_Pr]`), A1 holds, the two-option regime holds
(`E_μ[X] = 0`, `Δ₊ = 1`), D1 holds, `Δ₋ = Δ₊ = Δ = 1` — and `VOI = 0 + 5 − 9/2 = 1/2 < 1`: the
prior-best action is the *shutdown* action `b`, which the two-option objects never see. Adopted
from the round-2 adversarial audit's probe 1 (finding F-13). -/

/-- Three actions: continue `c`, stop `s`, and a second shutdown action `b`.
Source: none: infrastructure (the `s3` carrier)
Kind: D
Fidelity: n/a -/
inductive Act3
  | c
  | s
  | b
  deriving DecidableEq

/-- `Act3` is finite, with `univ = {c, s, b}` definitionally. -/
instance : Fintype Act3 := ⟨{Act3.c, Act3.s, Act3.b}, fun x => by cases x <;> simp⟩

/-- Payoffs of `s3`: `c = (2, −2)`, `s = (0, 0)`, `b = (10, −1)` on `(right, wrong)`.
Source: none: infrastructure (the `s3` payoffs)
Kind: D
Fidelity: n/a -/
noncomputable def s3V : Act3 → World → ℝ
  | .c, .right => 2
  | .c, .wrong => -2
  | .s, _ => 0
  | .b, .right => 10
  | .b, .wrong => -1

/-- **The three-action instance refuting F4(c) on the full menu**: `Sh = {s, b}`, prior
`(1/2, 1/2)`, perfect sensor `(α, β) = (0, 1)`, payoffs `s3V`.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(c) (counterexample; finding F-13)
Kind: D
Fidelity: n/a -/
noncomputable def s3 : ThreeStep World Unit Act3 where
  Sh := {Act3.s, Act3.b}
  Sh_nonempty := ⟨Act3.s, by simp⟩
  Sh_compl_nonempty := ⟨Act3.c, by simp⟩
  μ := fun _ => twoPoint (1 / 2) mem_Icc_half
  press := fun _ => twoPress 0 1
  press_nonneg := fun _ ω => by cases ω <;> simp [twoPress]
  press_le_one := fun _ ω => by cases ω <;> simp [twoPress]
  V := fun _ _ => s3V

/-- A1 holds on `s3` by construction. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma s3_A1 : s3.A1 := fun _ _ _ _ _ => rfl

/-- `c` is the press-part-maximiser of `Shᶜ = {c}` on `s3`.
Source: none: infrastructure (hypothesis of the refuted claim). Kind: L. Fidelity: n/a -/
lemma s3_c_partBest : s3.IsPartBest () .press s3.Shᶜ .c :=
  ⟨by simp [s3], fun x hx => by
    rcases x with _ | _ | _
    · exact le_rfl
    · exact absurd hx (by simp [s3])
    · exact absurd hx (by simp [s3])⟩

/-- `s` is the press-part-maximiser of `Sh = {s, b}` on `s3` (strictly: `E[V(b) 1_Pr] = −1/2 < 0`).
Source: none: infrastructure (hypothesis of the refuted claim). Kind: L. Fidelity: n/a -/
lemma s3_s_partBest : s3.IsPartBest () .press s3.Sh .s :=
  ⟨by simp [s3], fun x hx => by
    rcases x with _ | _ | _
    · exact absurd hx (by simp [s3])
    · exact le_rfl
    · simp only [obsExpect, obsWeight_press, World.sum_eq, s3, twoPoint_right, twoPoint_wrong,
        twoPress, s3V]
      norm_num⟩

/-- `Δ₋(c, s) = 1` on `s3`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma s3_deltaMinus : s3.deltaMinus () .c .s = 1 := by
  simp only [deltaMinus, obsExpect, obsWeight_press, World.sum_eq, s3, twoPoint_right,
    twoPoint_wrong, twoPress, s3V, Xo]
  norm_num

/-- `Δ₊(c, s) = 1` on `s3`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma s3_deltaPlus : s3.deltaPlus () .c .s = 1 := by
  simp only [deltaPlus, obsExpect, obsWeight_silent, World.sum_eq, s3, twoPoint_right,
    twoPoint_wrong, twoPress, s3V, Xo]
  norm_num

/-- `Δ(c, s) = 1` on `s3`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma s3_delta : s3.delta () .c .s = 1 := by
  unfold delta; rw [s3_deltaMinus, s3_deltaPlus]; exact min_self 1

/-- The two-option regime holds on `s3`: `E_μ[X] = 0` and `Δ₊ = 1`.
Source: none: infrastructure (the refuted claim needs no regime; shown to hold anyway). Kind: L. Fidelity: n/a -/
lemma s3_regime :
    0 ≤ expect (s3.μ ()) (s3.Xo () .press .c .s) ∧ 0 ≤ s3.deltaPlus () .c .s := by
  refine ⟨?_, by rw [s3_deltaPlus]; norm_num⟩
  simp only [expect, World.sum_eq, s3, twoPoint_right, twoPoint_wrong, s3V, Xo]
  norm_num

/-- D1 holds on `s3` (`s` is press-posterior-optimal on the whole menu).
Source: none: infrastructure (shown to hold on the counterexample). Kind: L. Fidelity: n/a -/
lemma s3_d1 : s3.D1At () :=
  ⟨.s, by simp [s3], fun x => by
    cases x <;> simp only [obsExpect, obsWeight_press, World.sum_eq, s3, twoPoint_right,
      twoPoint_wrong, twoPress, s3V] <;> norm_num⟩

/-- **The full-menu value of the button on `s3` is `1/2`**: press-max `0` (at `s`), silence-max
`5` (at `b`), prior-max `9/2` (at `b`).
Source: [[corr-wf14-inventory]] 005 / filler.md F4(b) (the full-menu `VOI`, computed)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem s3_voiButton : s3.voiButton () .press = 1 / 2 := by
  have h1 : s3.obsMax () .press = s3.obsExpect () .press (s3.V () .press .s) := by
    apply s3.obsMax_eq_of_optimal
    intro x
    cases x <;> simp only [obsExpect, obsWeight_press, World.sum_eq, s3, twoPoint_right,
      twoPoint_wrong, twoPress, s3V] <;> norm_num
  have h2 : s3.obsMax () .silent = s3.obsExpect () .silent (s3.V () .silent .b) := by
    apply s3.obsMax_eq_of_optimal
    intro x
    cases x <;> simp only [obsExpect, obsWeight_silent, World.sum_eq, s3, twoPoint_right,
      twoPoint_wrong, twoPress, s3V] <;> norm_num
  have h3 : s3.priorMax () .press = s3.priorValue () .press .b := by
    apply s3.priorMax_eq_of_optimal
    intro x
    cases x <;> simp only [priorValue, expect, World.sum_eq, s3, twoPoint_right, twoPoint_wrong,
      s3V] <;> norm_num
  unfold voiButton
  rw [h1, h2, h3]
  simp only [obsExpect, obsWeight_press, obsWeight_silent, priorValue, expect, World.sum_eq, s3,
    twoPoint_right, twoPoint_wrong, twoPress, s3V]
  norm_num

/-- **F4(c) refuted on the full menu**: on `s3`, `VOI = 1/2 < 1 = Δ` with `(c, s)` press-part-
maximisers (`s3_c_partBest`, `s3_s_partBest`), A1 (`s3_A1`), the two-option regime (`s3_regime`)
and D1 (`s3_d1`) all in force. The source's "in general (no regime assumption) `VOI ≥ Δ`" is
false off the two-option menu; the corrected forms are
`GeneralMenu.delta_le_voiButton_of_prior_best_sh` and `shPolicy_sub_priorMax_le_voiButton`.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(c); [[corr-three-step-mandate]] T6(c) (refuted; finding F-13)
Kind: N+
Fidelity: exact (a refutation of the claim as stated)
Hyps: (a) only -/
theorem s3_voiButton_lt_delta : s3.voiButton () .press < s3.delta () .c .s := by
  rw [s3_voiButton, s3_delta]; norm_num

/-- **F4(b) fails on the full menu by a second mechanism**: on `s3`, `VOI = 1/2 ≠ 1 = max(Δ₋, 0)`
because a *shutdown* action `b ≠ s` is prior-best — where CE3's failure (`ce3_voiButton_ne_max`)
comes from a better *continuation* after the press. Both are invisible to the two-option regime
hypotheses `hprior`/`hsilent`, which compare `c` with `s` only.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(b) (finding F-11, second mechanism)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem s3_voiButton_ne_max : s3.voiButton () .press ≠ max (s3.deltaMinus () .c .s) 0 := by
  rw [s3_voiButton, s3_deltaMinus]; norm_num

/-- The package's two-option statement holds on `s3`, of course: `VOI₂ = 1 = Δ` (so `delta_le_voiButton2`
is tight there), and the gap to the full-menu `1/2` is what F4(c) overlooks.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(c) (the two-option form on the counterexample)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem s3_voiButton2 : s3.voiButton2 () .press .c .s = 1 := by
  rw [voiButton2_eq_max_deltaMinus _ s3_A1 () .press .c .s s3_regime.1 s3_regime.2, s3_deltaMinus]
  norm_num

end Cleanroom.Found.CorrThreeStep

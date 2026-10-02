import Cleanroom.Corrigibility.CorrThreeStepFacts.Erosion
import Cleanroom.Corrigibility.CorrThreeStepFacts.Identification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# Witnesses B: numerics for T2, T4, T5, T6

* **T2 finding**: `avgConst`, a three-world instance whose sensor has the same *average* press
  rate on `{X ≤ 0}` and on `{X > 0}` yet is not constant; the below-threshold inequality holds
  while `E_μ[X] > 0` — Prop. 8.1's R2 needs the sensor constant on all of `Ω`. `avgConst` holds
  the inequality with equality (a tie); `avgConstS` (`X = (−3, 1, 3)`) holds it strictly
  (audit r1 N10).
* **T6(iii) witnesses** (audit r1): `scaledPair` (the honest `w3` sensor against the same sensor
  halved) has equal press conditionals, different press masses, and the theorem forces the
  silence conditionals apart — `107/121 ≠ 43/109` (N+); `constPair` (two constant sensors)
  inhabits the full hypothesis package with `a ≠ a'` and lands in the inert disjunct (N−).
* **T4**: the crossing index on `(ε, α, β, c, h) = (1/10, 1/20, 9/10, 1, 20)` is `2`
  (`w_crossing_isLeast`); the eroded weights `2/173`, `4/3253`; D1 at `n = 1`, not at `n = 2`.
* **T5**: the exact D1-flip pair over the record `(171/200, 1/50)`: `ε = 1/45` (D1 fails at
  `h/c = 20`, inverted sensor `β < α`) and `ε = 1/8` (D1 holds).
* **T6**: targeted suppression `β' = 1/25` on the `w3` prior breaks D1; the source's instance
  (which also changes `ε` to `1/100`) breaks it too; the silence posterior `2/363 → 22/763` at
  `λ = 1 → 1/2`; the mixed sensor's `Δ₋` runs `3/20, 9/80, 3/40, 3/80, 0`.
-/

namespace Cleanroom.Corrigibility.CorrThreeStepFacts

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

/-! ## T2 finding: equal-in-average is not constant -/

/-- The uniform prior on `Fin 3`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def unif3 : Distr (Fin 3) where
  mass _ := 1/3
  nonneg _ := by norm_num
  sum_eq_one := by rw [Fin.sum_univ_three]; norm_num

/-- `avgConst`: prior uniform on three worlds, `X = (−2, 1, 3)`, sensor `(1/2, 1, 0)`: the
average press rate on `{X > 0} = {1, 2}` is `1/2`, equal to the rate on `{X ≤ 0} = {0}`.
Source: [[corr-wf13-2-inventory]] 003 / miri.md Prop. 8.1, R2 ("not constant across `{X ≤ 0}` versus `{X > 0}`")
Kind: D
Fidelity: n/a (counterexample to the equal-in-average reading)
Hyps: n/a (definition) -/
noncomputable def avgConst : ThreeStep (Fin 3) Unit TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => unif3
  press := fun _ => ![1/2, 1, 0]
  press_nonneg := fun _ w => by fin_cases w <;> norm_num
  press_le_one := fun _ w => by fin_cases w <;> norm_num
  V := fun _ _ => twoValue' where
    twoValue' : TwoAct → Fin 3 → ℝ
      | .cont, w => ![(-2 : ℝ), 1, 3] w
      | .stop, _ => 0

/-- The variable `X = V(cont) − V(stop) = (−2, 1, 3)`. Source: none: witness. Kind: D. Fidelity: n/a -/
lemma avgConst_Xo : avgConst.Xo () .press .cont .stop = ![(-2 : ℝ), 1, 3] := by
  funext w; fin_cases w <;> simp [avgConst, Xo, avgConst.twoValue']

/-- Equal average press rates (product form): `P(Pr ∧ X > 0) · μ(X ≤ 0) = P(Pr ∧ X ≤ 0) · μ(X > 0)`,
here `(1/3) · (1/3) = (1/6) · (2/3)`.
Source: miri.md Prop. 8.1, R2 (the equal-in-average reading). Kind: N−. Fidelity: exact -/
theorem avgConst_equal_average :
    avgConst.pressMassOn () (univ.filter fun w => 0 < avgConst.Xo () .press .cont .stop w) *
        (∑ w ∈ univ.filter (fun w => avgConst.Xo () .press .cont .stop w ≤ 0), unif3.mass w) =
      avgConst.pressMassOn () (univ.filter fun w => avgConst.Xo () .press .cont .stop w ≤ 0) *
        (∑ w ∈ univ.filter (fun w => 0 < avgConst.Xo () .press .cont .stop w), unif3.mass w) := by
  rw [avgConst_Xo]
  simp only [pressMassOn, sum_filter, Fin.sum_univ_three]
  simp [avgConst, unif3]
  norm_num

/-- The sensor is not constant (`press 1 = 1 ≠ 0 = press 2`). Source: none: witness. Kind: N−. Fidelity: exact -/
theorem avgConst_not_const : ¬ ∀ w w', avgConst.press () w = avgConst.press () w' := by
  intro h
  have := h 1 2
  simp [avgConst] at this

/-- The below-threshold inequality holds (`E_P[X 1_Pr] = 0`) …
Source: miri.md Prop. 8.1, R2. Kind: N−. Fidelity: exact -/
theorem avgConst_below : avgConst.belowThresholdIneq () (avgConst.Xo () .press .cont .stop) := by
  rw [avgConst_Xo]
  simp only [belowThresholdIneq, obsExpect, obsWeight_press, Fin.sum_univ_three]
  simp [avgConst, unif3]

/-- … while `E_μ[X] = 2/3 > 0` and the press mass `1/2` is positive: the equal-in-average
sensor does *not* make the button decision-irrelevant.
Source: miri.md Prop. 8.1, R2 (finding: the conclusion needs a sensor constant on `Ω`). Kind: N−. Fidelity: exact -/
theorem avgConst_expect_pos_and_pressMass :
    0 < expect unif3 (avgConst.Xo () .press .cont .stop) ∧ avgConst.pressMass () = 1/2 := by
  rw [avgConst_Xo]
  constructor
  · simp only [expect, Fin.sum_univ_three]; simp [unif3]; norm_num
  · simp only [pressMass, Fin.sum_univ_three]; simp [avgConst, unif3]; norm_num

/-- `avgConstS`: `avgConst` with `X = (−3, 1, 3)` — the same equal average press rates, the
below-threshold inequality now *strict* (`E_P[X 1_Pr] = −1/6 < 0`), `E_μ[X] = 1/3 > 0`.
Source: miri.md Prop. 8.1, R2; audit r1 (fidelity) N10 (the tie in `avgConst`)
Kind: D
Fidelity: n/a (counterexample to the equal-in-average reading, strict)
Hyps: n/a (definition) -/
noncomputable def avgConstS : ThreeStep (Fin 3) Unit TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => unif3
  press := fun _ => ![1/2, 1, 0]
  press_nonneg := fun _ w => by fin_cases w <;> norm_num
  press_le_one := fun _ w => by fin_cases w <;> norm_num
  V := fun _ _ => twoValueS where
    twoValueS : TwoAct → Fin 3 → ℝ
      | .cont, w => ![(-3 : ℝ), 1, 3] w
      | .stop, _ => 0

/-- The variable `X = (−3, 1, 3)`. Source: none: witness. Kind: D. Fidelity: n/a -/
lemma avgConstS_Xo : avgConstS.Xo () .press .cont .stop = ![(-3 : ℝ), 1, 3] := by
  funext w; fin_cases w <;> simp [avgConstS, Xo, avgConstS.twoValueS]

/-- Equal average press rates on `avgConstS` (product form), as for `avgConst`.
Source: miri.md Prop. 8.1, R2 (the equal-in-average reading). Kind: N+. Fidelity: exact -/
theorem avgConstS_equal_average :
    avgConstS.pressMassOn () (univ.filter fun w => 0 < avgConstS.Xo () .press .cont .stop w) *
        (∑ w ∈ univ.filter (fun w => avgConstS.Xo () .press .cont .stop w ≤ 0), unif3.mass w) =
      avgConstS.pressMassOn () (univ.filter fun w => avgConstS.Xo () .press .cont .stop w ≤ 0) *
        (∑ w ∈ univ.filter (fun w => 0 < avgConstS.Xo () .press .cont .stop w), unif3.mass w) := by
  rw [avgConstS_Xo]
  simp only [pressMassOn, sum_filter, Fin.sum_univ_three]
  simp [avgConstS, unif3] <;> norm_num

/-- **F-2, strict (N+).** On `avgConstS` the below-threshold inequality holds strictly
(`E_P[X 1_Pr] = −1/6 < 0`) while `E_μ[X] = 1/3 > 0` at press mass `1/2`, and the sensor is not
constant: the equal-in-average reading of R2 is refuted without a tie.
Source: miri.md Prop. 8.1, R2 (finding: the conclusion needs a sensor constant on `Ω`); audit r1 N10
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem avgConstS_strict :
    avgConstS.obsExpect () .press (avgConstS.Xo () .press .cont .stop) < 0 ∧
      0 < expect unif3 (avgConstS.Xo () .press .cont .stop) ∧ avgConstS.pressMass () = 1/2 ∧
      ¬ ∀ w w', avgConstS.press () w = avgConstS.press () w' := by
  rw [avgConstS_Xo]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [obsExpect, obsWeight_press, Fin.sum_univ_three]; simp [avgConstS, unif3] <;> norm_num
  · simp only [expect, Fin.sum_univ_three]; simp [unif3] <;> norm_num
  · simp only [pressMass, Fin.sum_univ_three]; simp [avgConstS, unif3] <;> norm_num
  · intro h
    have := h 1 2
    simp [avgConstS] at this

/-! ## T4: the crossing index on the instance -/

/-- **T4(iii), the crossing index.** On `(ε, α, β, c, h) = (1/10, 1/20, 9/10, 1, 20)` the least
`n` with `εβh(1 − β)^n < (1 − ε)αc(1 − α)^n` is `2`: compliance fails at the second silent
period.
Source: [[corr-wf14-inventory]] 008 / filler.md R4.3(a); soares.md item 9 ("fails after two silent periods")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w_crossing_isLeast :
    IsLeast {n : ℕ | (1/10 : ℝ) * (9/10) * 20 * (1 - 9/10) ^ n < (1 - 1/10) * (1/20) * 1 * (1 - 1/20) ^ n} 2 := by
  constructor
  · show (1/10 : ℝ) * (9/10) * 20 * (1 - 9/10) ^ 2 < (1 - 1/10) * (1/20) * 1 * (1 - 1/20) ^ 2
    norm_num
  · intro n hn
    by_contra h
    push Not at h
    interval_cases n <;> norm_num at hn

/-- The eroded weight after one silent period: `2/173`. Source: filler.md R4.3(a). Kind: N+. Fidelity: exact -/
theorem w_erode_one : (erode (1/20) (9/10))^[1] (1/10 : ℝ) = 2/173 := by
  simp only [Function.iterate_one, erode]; norm_num

/-- The eroded weight after two silent periods: `4/3253`. Source: filler.md R4.3(a). Kind: N+. Fidelity: exact -/
theorem w_erode_two : (erode (1/20) (9/10))^[2] (1/10 : ℝ) = 4/3253 := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id_eq, erode]; norm_num

/-- After one silent period D1 still holds (`e₁ = 2/173`).
Source: filler.md R4.3(a). Kind: N+. Fidelity: exact -/
theorem w_erosion_d1_one :
    (twoState (2/173) (1/20) (9/10) 1 20 (by constructor <;> norm_num) mem_Icc_1_20 mem_Icc_9_10).D1At () := by
  rw [twoState_d1At_iff]; norm_num

/-- After two silent periods D1 fails (`e₂ = 4/3253`).
Source: filler.md R4.3(a); soares.md item 9. Kind: N+. Fidelity: exact -/
theorem w_erosion_not_d1_two :
    ¬ (twoState (4/3253) (1/20) (9/10) 1 20 (by constructor <;> norm_num) mem_Icc_1_20 mem_Icc_9_10).D1At () := by
  rw [twoState_d1At_iff]; norm_num

/-! ## T5: the D1-flip pair over one record -/

/-- `ε = 1/45`, `(α, β) = (221/1760, 1/10)` reproduces the record `(171/200, 1/50)`.
Source: [[corr-wf13-inventory]] 007 / miri.md Prop. 15.1 numerics. Kind: N+. Fidelity: exact -/
theorem w_record_low : record (1/45) (221/1760) (1/10) = (171/200, 1/50) := by
  unfold record; norm_num

/-- `ε = 1/8`, `(α, β) = (4/175, 21/25)` reproduces the same record.
Source: miri.md Prop. 15.1 numerics. Kind: N+. Fidelity: exact -/
theorem w_record_high : record (1/8) (4/175) (21/25) = (171/200, 1/50) := by
  unfold record; norm_num

/-- On the low fibre point the posterior is `4/225 < 1/21`: D1 fails at `h/c = 20`, and the
sensor is inverted (`β = 1/10 < 221/1760 = α`).
Source: miri.md Prop. 15.1 numerics (the source's decimals `0.022, 0.126, 0.091, 0.016`). Kind: N+. Fidelity: exact -/
theorem w_flip_low :
    (twoState (1/45) (221/1760) (1/10) 1 20 (by constructor <;> norm_num) (by constructor <;> norm_num)
        (by constructor <;> norm_num)).posteriorPress () .wrong = 4/225 ∧
      ¬ (twoState (1/45) (221/1760) (1/10) 1 20 (by constructor <;> norm_num) (by constructor <;> norm_num)
        (by constructor <;> norm_num)).D1At () ∧ (1/10 : ℝ) < 221/1760 := by
  refine ⟨?_, ?_, by norm_num⟩
  · rw [twoState_posteriorPress_wrong]; norm_num
  · rw [twoState_d1At_iff]; norm_num

/-- On the high fibre point the posterior is `21/25 ≥ 1/21`: D1 holds.
Source: miri.md Prop. 15.1 numerics (`0.96`). Kind: N+. Fidelity: exact -/
theorem w_flip_high :
    (twoState (1/8) (4/175) (21/25) 1 20 (by constructor <;> norm_num) (by constructor <;> norm_num)
        (by constructor <;> norm_num)).posteriorPress () .wrong = 21/25 ∧
      (twoState (1/8) (4/175) (21/25) 1 20 (by constructor <;> norm_num) (by constructor <;> norm_num)
        (by constructor <;> norm_num)).D1At () := by
  constructor
  · rw [twoState_posteriorPress_wrong]; norm_num
  · rw [twoState_d1At_iff]; norm_num

/-! ## T6: targeted suppression and the silence side -/

/-- **T6(ii), targeted suppression on the `w3` prior.** Lowering `β` alone to `1/25`
(`< (1 − ε)αc/(εh) = 19/400`) breaks D1.
Source: [[corr-wf14-inventory]] 010 / filler.md R7 (targeted suppression), like-for-like
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w_targeted_not_d1 :
    ¬ (twoState (1/20) (1/20) (1/25) 1 20 mem_Icc_1_20 mem_Icc_1_20 (by constructor <;> norm_num)).D1At () := by
  rw [twoState_d1At_iff]; norm_num

/-- **T6(ii), the source's instance.** `ε = 1/100`, `β' = 1/5` (the source also changes `ε`,
which violates A0 across `a₁` — a presentation finding): D1 fails there too.
Source: filler.md R7 ("targeted suppression … `ε = 1/100`, `β' = 1/5` … D1 fails")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w_targeted_source_not_d1 :
    ¬ (twoState (1/100) (1/20) (1/5) 1 20 (by constructor <;> norm_num) mem_Icc_1_20
      (by constructor <;> norm_num)).D1At () := by
  rw [twoState_d1At_iff]; norm_num

/-- **T6(i), the silence side on `w3`.** `P(W | ¬Pr) = 2/363` at `λ = 1` and `22/763` at
`λ = 1/2` (the source's `0.0055 → 0.0288`).
Source: filler.md R7. Kind: N+. Fidelity: exact -/
theorem w_silentPosterior :
    silentPosterior (1/20) (1/20) (9/10) 1 = 2/363 ∧ silentPosterior (1/20) (1/20) (9/10) (1/2) = 22/763 := by
  constructor <;> (unfold silentPosterior; norm_num)

/-- **T6(iv), the mixed sensor's `Δ₋`** on `(ε, α, β, c, h) = (1/10, 1/10, 3/5, 1, 4)` with
`k = 0`: `3/20, 9/80, 3/40, 3/80, 0` at `d = 0, 1/4, 1/2, 3/4, 1`.
Source: [[corr-wf14-inventory]] 010 / selection.md R2.2(iii) (`selection_checks.py` C4)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w_mixed_deltaMinus :
    (twoState (1/10) (1/10) (3/5) 1 4 (by constructor <;> norm_num) (by constructor <;> norm_num)
        (by constructor <;> norm_num)).deltaMinus () .cont .stop = 3/20 ∧
      (twoState (1/10) ((1 - 1/4) * (1/10) + 1/4 * 0) ((1 - 1/4) * (3/5) + 1/4 * 0) 1 4
        (by constructor <;> norm_num) (by constructor <;> norm_num)
        (by constructor <;> norm_num)).deltaMinus () .cont .stop = 9/80 ∧
      (twoState (1/10) ((1 - 1/2) * (1/10) + 1/2 * 0) ((1 - 1/2) * (3/5) + 1/2 * 0) 1 4
        (by constructor <;> norm_num) (by constructor <;> norm_num)
        (by constructor <;> norm_num)).deltaMinus () .cont .stop = 3/40 ∧
      (twoState (1/10) ((1 - 3/4) * (1/10) + 3/4 * 0) ((1 - 3/4) * (3/5) + 3/4 * 0) 1 4
        (by constructor <;> norm_num) (by constructor <;> norm_num)
        (by constructor <;> norm_num)).deltaMinus () .cont .stop = 3/80 ∧
      (twoState (1/10) ((1 - 1) * (1/10) + 1 * 0) ((1 - 1) * (3/5) + 1 * 0) 1 4
        (by constructor <;> norm_num) (by constructor <;> norm_num)
        (by constructor <;> norm_num)).deltaMinus () .cont .stop = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (rw [twoState_deltaMinus]; norm_num)

/-- The mixed instance is in the continue-by-default regime at `d = 0` and `d = 1/2`, so
`voiButton2 = Δ₋` there: `3/20` and `3/40` — the value of information falls with `d`.
Source: selection.md R2.2(iii) ("value of information falls monotonically"). Kind: N+. Fidelity: exact -/
theorem w_mixed_voiButton2 :
    (twoState (1/10) (1/10) (3/5) 1 4 (by constructor <;> norm_num) (by constructor <;> norm_num)
        (by constructor <;> norm_num)).voiButton2 () .press .cont .stop = 3/20 ∧
      (twoState (1/10) (1/20) (3/10) 1 4 (by constructor <;> norm_num) (by constructor <;> norm_num)
        (by constructor <;> norm_num)).voiButton2 () .press .cont .stop = 3/40 := by
  constructor
  · rw [voiButton2_eq_max_deltaMinus _ (twoState_A1 _ _ _ _ _ _ _ _) () .press .cont .stop
      (by rw [show (twoState (1/10) (1/10) (3/5) 1 4 _ _ _).μ () = twoPoint (1/10) (by constructor <;> norm_num) from rfl,
        twoState_expect_Xo]; norm_num)
      (by rw [twoState_deltaPlus]; norm_num), twoState_deltaMinus]
    norm_num
  · rw [voiButton2_eq_max_deltaMinus _ (twoState_A1 _ _ _ _ _ _ _ _) () .press .cont .stop
      (by rw [show (twoState (1/10) (1/20) (3/10) 1 4 _ _ _).μ () = twoPoint (1/10) (by constructor <;> norm_num) from rfl,
        twoState_expect_Xo]; norm_num)
      (by rw [twoState_deltaPlus]; norm_num), twoState_deltaMinus]
    norm_num

/-! ## T6(iii): witnesses for the total-expectation theorem (audit r1) -/

/-- The two-state payoff of continuing, `(1, −20)`. Source: none: witness. Kind: D. Fidelity: n/a -/
def X20 : World → ℝ := twoValue 1 20 .cont

/-- **`scaledPair`**: `A₁ = Bool` on the `w3` prior `ε = 1/20`; `true` is the honest sensor
`(1/20, 9/10)`, `false` the same sensor halved `(1/40, 9/20)`.
Source: filler.md R7 (last paragraph); audit r1 (adversarial) N3. Kind: D. Fidelity: n/a (witness) -/
noncomputable def scaledPair : ThreeStep World Bool TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => twoPoint (1/20) mem_Icc_1_20
  press := fun a ω => match a, ω with
    | true, .right => 1/20
    | true, .wrong => 9/10
    | false, .right => 1/40
    | false, .wrong => 9/20
  press_nonneg := fun a ω => by cases a <;> cases ω <;> norm_num
  press_le_one := fun a ω => by cases a <;> cases ω <;> norm_num
  V := fun _ _ => twoValue 1 20

/-- **T6(iii), N+.** In `scaledPair` the press conditionals agree (`−341/37` both, by scale
invariance) and the press masses differ (`37/400 ≠ 37/800`), so `pressMass_eq_or_condExp_eq`
forces the silence conditionals apart — and they are: `107/121 ≠ 43/109`. The theorem has bite:
an `a₁`-blind conditional model cannot hold across these two actions.
Source: filler.md R7 (last paragraph); audit r1 (adversarial) N3
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem scaledPair_forces_silence_apart :
    scaledPair.condExpPress true X20 = scaledPair.condExpPress false X20 ∧
      scaledPair.pressMass true ≠ scaledPair.pressMass false ∧
      scaledPair.condExpSilent true X20 = 107/121 ∧ scaledPair.condExpSilent false X20 = 43/109 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [condExpPress, condExpSilent, obsExpect, pressMass, obsWeight_press, obsWeight_silent,
      World.sum_eq, scaledPair, twoPoint_right, twoPoint_wrong, X20, twoValue]
     norm_num)

/-- **`constPair`**: two constant sensors `1/2`, `1/4` on the `w3` prior.
Source: filler.md R7; audit r1 (adversarial) N3. Kind: D. Fidelity: n/a (witness) -/
noncomputable def constPair : ThreeStep World Bool TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => twoPoint (1/20) mem_Icc_1_20
  press := fun a _ => match a with
    | true => 1/2
    | false => 1/4
  press_nonneg := fun a _ => by cases a <;> norm_num
  press_le_one := fun a _ => by cases a <;> norm_num
  V := fun _ _ => twoValue 1 20

/-- **T6(iii), N− (the inert disjunct).** `constPair` inhabits the full hypothesis package of
`pressMass_eq_or_condExp_eq` with `a ≠ a'` and different press masses; the conclusion lands in
the right disjunct (`E[X | Pr] = E[X | ¬Pr] = −1/20`). Degenerate by the theorem's own content:
every different-mass instance of the package is inert, so this is the best a full-package witness
can be; `scaledPair` is the N+ for the content.
Source: filler.md R7 (last paragraph); audit r1 (adversarial) N3
Kind: N−
Fidelity: exact
Hyps: (a) only -/
theorem constPair_package :
    constPair.Nondegenerate true ∧ constPair.Nondegenerate false ∧
      constPair.condExpPress true X20 = constPair.condExpPress false X20 ∧
      constPair.condExpSilent true X20 = constPair.condExpSilent false X20 ∧
      constPair.pressMass true ≠ constPair.pressMass false ∧
      constPair.condExpPress true X20 = constPair.condExpSilent true X20 := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [condExpPress, condExpSilent, obsExpect, pressMass, obsWeight_press,
      obsWeight_silent, World.sum_eq, constPair, twoPoint_right, twoPoint_wrong, X20, twoValue]
     norm_num)

end Cleanroom.Corrigibility.CorrThreeStepFacts

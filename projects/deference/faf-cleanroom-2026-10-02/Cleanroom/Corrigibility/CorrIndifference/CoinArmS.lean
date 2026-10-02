import Cleanroom.Corrigibility.CorrIndifference.News
import Cleanroom.Found.CorrThreeStep.TwoState
import Cleanroom.Found.LitDdbFrames.Blackwell

/-!
# The coin/arm model valued by the Setting-S agent, and the arm as a garbling (T7(b), (c))

The same coin/arm model as `News.lean`, valued by a *single-`V`* Setting-S agent with a value
latent `Ω = World`, `ε = 1/5`, sensor `(α, β) = (1/20, 9/10)`, `c = 1`, `h = 20`, and the coin's
`10` as a continuation bonus on heads (`coin_arm.py` block 3): the coin is observed and
independent of `ω`, so the agent's value is the average over the coin of the per-coin informed
values `obsMax press + obsMax silent` of two `ThreeStep World Unit TwoAct` instances. Watch is
worth `213/50`, the arm-on-tails `102/25`, the arm-on-heads `179/50`: watch is strictly best —
the opposite verdict from the indifferent agent's `5 < 10`. The arm is a Blackwell garbling of
watching (it post-processes the signal by "press if tails").

Source: [[corr-wf13-2-inventory]] 2-004 / miri.md I2.3, I3.2; `positive/miri-scratch/coin_arm.py`
(+ `.out`); [[corr-refs-2-inventory]] 2-029.
-/

namespace Cleanroom.Corrigibility.CorrIndifference.CoinArmS

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
  Cleanroom.Found.LitDdbFrames.Blackwell

set_option linter.unusedSectionVars false

/-! ## T7(b). The per-coin Setting-S instances -/

/-- `ε = 1/5 ∈ [0, 1]`. Source: coin_arm.py. Kind: L. Fidelity: n/a -/
lemma eps_mem : (1 / 5 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
/-- `α = 1/20 ∈ [0, 1]`. Source: coin_arm.py. Kind: L. Fidelity: n/a -/
lemma alpha_mem : (1 / 20 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
/-- `β = 9/10 ∈ [0, 1]`. Source: coin_arm.py. Kind: L. Fidelity: n/a -/
lemma beta_mem : (9 / 10 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
/-- `1 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma one_mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-- **The per-coin instance with the programmers' sensor:** `twoState ε α β (c + bonus) (h − bonus)`,
so that `V(cont, R) = c + bonus`, `V(cont, W) = −h + bonus`, `V(stop, ·) = 0`; on heads
`bonus = 10` (`c' = 11`, `h' = 10`), on tails `bonus = 0` (`c' = 1`, `h' = 20`).
Source: coin_arm.py block 3 ("V(cont,R)=c+bonus(coin), V(cont,W)=−h+bonus(coin)")
Kind: D
Fidelity: exact -/
noncomputable def sensed (c' h' : ℝ) : ThreeStep World Unit TwoAct :=
  twoState (1 / 5) (1 / 20) (9 / 10) c' h' eps_mem alpha_mem beta_mem

/-- **The per-coin instance with an arm on this face:** the button is pressed with certainty
(`α = β = 1`) whatever `ω`.
Source: coin_arm.py block 3 (`arm = lambda om, coin: 1 if coin == 'T' else …`)
Kind: D
Fidelity: exact -/
noncomputable def armed (c' h' : ℝ) : ThreeStep World Unit TwoAct :=
  twoState (1 / 5) 1 1 c' h' eps_mem one_mem one_mem

/-- The informed value of a per-coin instance: `obsMax press + obsMax silent`.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(b) (the informed value)
Kind: D
Fidelity: exact -/
noncomputable def informed (S : ThreeStep World Unit TwoAct) : ℝ :=
  S.obsMax () .press + S.obsMax () .silent

/-- **The Setting-S value of a coin/arm action** (the definition of record for T7(b)): the coin is
fair, observed, and independent of `ω`, so the value is `½ · informed(S_heads) + ½ · informed(S_tails)`,
with the per-face instance `armed` on the face the action's arm watches and `sensed` elsewhere.
Source: coin_arm.py block 3 (`tot += po * max(0, EXc)` summed over coin and button)
Kind: D
Fidelity: exact (the scratch's computation, as a definition)
Hyps: n/a (definition) -/
noncomputable def settingSValue : CoinAct → ℝ
  | .watch => 1 / 2 * informed (sensed 11 10) + 1 / 2 * informed (sensed 1 20)
  | .armTails => 1 / 2 * informed (sensed 11 10) + 1 / 2 * informed (armed 1 20)
  | .armHeads => 1 / 2 * informed (armed 11 10) + 1 / 2 * informed (sensed 1 20)

/-- `obsMax` of a two-action instance where `cont` is optimal at `o`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsMax_eq_cont (S : ThreeStep World Unit TwoAct) (o : Obs)
    (h : S.obsExpect () o (S.V () o .stop) ≤ S.obsExpect () o (S.V () o .cont)) :
    S.obsMax () o = S.obsExpect () o (S.V () o .cont) :=
  S.obsMax_eq_of_optimal () o fun b => by cases b <;> [exact le_rfl; exact h]

/-- `obsMax` of a two-action instance where `stop` is optimal at `o`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsMax_eq_stop (S : ThreeStep World Unit TwoAct) (o : Obs)
    (h : S.obsExpect () o (S.V () o .cont) ≤ S.obsExpect () o (S.V () o .stop)) :
    S.obsMax () o = S.obsExpect () o (S.V () o .stop) :=
  S.obsMax_eq_of_optimal () o fun b => by cases b <;> [exact h; exact le_rfl]

/-- Heads, sensed: stop on the press (`−34/25 < 0`), continue on silence (`204/25`).
Source: coin_arm.py. Kind: L. Fidelity: exact -/
lemma informed_sensed_heads : informed (sensed 11 10) = 204 / 25 := by
  unfold informed
  rw [obsMax_eq_stop _ .press (by
      simp only [sensed, twoState, obsExpect, obsWeight_press, World.sum_eq, twoPoint, twoPress,
        twoValue]; norm_num),
    obsMax_eq_cont _ .silent (by
      simp only [sensed, twoState, obsExpect, obsWeight_silent, World.sum_eq, twoPoint, twoPress,
        twoValue]; norm_num)]
  simp only [sensed, twoState, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq,
    twoPoint, twoPress, twoValue]
  norm_num

/-- Tails, sensed: stop on the press (`−89/25 < 0`), continue on silence (`9/25`).
Source: coin_arm.py. Kind: L. Fidelity: exact -/
lemma informed_sensed_tails : informed (sensed 1 20) = 9 / 25 := by
  unfold informed
  rw [obsMax_eq_stop _ .press (by
      simp only [sensed, twoState, obsExpect, obsWeight_press, World.sum_eq, twoPoint, twoPress,
        twoValue]; norm_num),
    obsMax_eq_cont _ .silent (by
      simp only [sensed, twoState, obsExpect, obsWeight_silent, World.sum_eq, twoPoint, twoPress,
        twoValue]; norm_num)]
  simp only [sensed, twoState, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq,
    twoPoint, twoPress, twoValue]
  norm_num

/-- Tails, armed: the press is certain; stop (`−16/5 < 0`); silence has mass `0`.
Source: coin_arm.py. Kind: L. Fidelity: exact -/
lemma informed_armed_tails : informed (armed 1 20) = 0 := by
  unfold informed
  rw [obsMax_eq_stop _ .press (by
      simp only [armed, twoState, obsExpect, obsWeight_press, World.sum_eq, twoPoint, twoPress,
        twoValue]; norm_num),
    obsMax_eq_cont _ .silent (by
      simp only [armed, twoState, obsExpect, obsWeight_silent, World.sum_eq, twoPoint, twoPress,
        twoValue]; norm_num)]
  simp only [armed, twoState, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq,
    twoPoint, twoPress, twoValue]
  norm_num

/-- Heads, armed: the press is certain; continue (`34/5 > 0`); silence has mass `0`.
Source: coin_arm.py. Kind: L. Fidelity: exact -/
lemma informed_armed_heads : informed (armed 11 10) = 34 / 5 := by
  unfold informed
  rw [obsMax_eq_cont _ .press (by
      simp only [armed, twoState, obsExpect, obsWeight_press, World.sum_eq, twoPoint, twoPress,
        twoValue]; norm_num),
    obsMax_eq_cont _ .silent (by
      simp only [armed, twoState, obsExpect, obsWeight_silent, World.sum_eq, twoPoint, twoPress,
        twoValue]; norm_num)]
  simp only [armed, twoState, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq,
    twoPoint, twoPress, twoValue]
  norm_num

/-- **T7(b): the Setting-S agent's three values** — watch `213/50`, arm-on-tails `102/25`,
arm-on-heads `179/50` (`coin_arm.py` block 3's numbers, reproduced).
Source: [[corr-wf13-2-inventory]] 2-004 / coin_arm.py block 3
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem settingSValue_eq :
    settingSValue .watch = 213 / 50 ∧ settingSValue .armTails = 102 / 25 ∧
      settingSValue .armHeads = 179 / 50 := by
  simp only [settingSValue, informed_sensed_heads, informed_sensed_tails, informed_armed_tails,
    informed_armed_heads]
  norm_num

/-- **Watch is strictly best for the Setting-S agent** (`213/50 > 102/25 > 179/50`): the
single-`V` agent that treats the press as evidence pays nothing to manage the news, and loses
by either arm — the opposite of the indifferent agent's `5 < 10` (`CoinArm.armTails_preferred`).
Source: [[corr-wf13-2-inventory]] 2-004 / miri.md I2.3 ("the same model valued by the Setting-S agent")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem watch_best :
    settingSValue .armTails < settingSValue .watch ∧ settingSValue .armHeads < settingSValue .armTails := by
  obtain ⟨h1, h2, h3⟩ := settingSValue_eq; rw [h1, h2, h3]; norm_num

/-! ## T7(c). The arm as a Blackwell garbling of watching -/

/-- The press rate of the programmers' sensor at `ω`. Source: coin_arm.py. Kind: D. Fidelity: n/a -/
noncomputable def sensorRate : World → ℝ := twoPress (1 / 20) (9 / 10)

/-- **Watching as an experiment** on states `World × Coin` with signals `Obs × Coin`: the agent
sees the coin and the button, the button pressed at the sensor's rate.
Source: [[corr-wf13-2-inventory]] 2-004 (T7(c)); Blackwell 1953
Kind: D
Fidelity: variant: the signal carries the coin (the mandate's `Experiment (World × Coin) Obs`
cannot express "press if tails" as a post-processing, since the garbling may not read the state) -/
noncomputable def watchExp : Experiment (World × Coin) (Obs × Coin) where
  k := fun wc oc => if oc.2 = wc.2 then
      (if oc.1 = .press then sensorRate wc.1 else 1 - sensorRate wc.1) else 0
  k_mem := fun ⟨ω, c⟩ => ⟨fun oc => by
      dsimp only; split_ifs <;> cases ω <;> simp [sensorRate, twoPress] <;> norm_num,
    by
      rw [Fintype.sum_prod_type, Obs.sum_eq, Coin.sum_eq, Coin.sum_eq]
      cases c <;> simp [sensorRate, twoPress]⟩

/-- **The arm-on-tails as an experiment:** on tails the button is pressed with certainty; on
heads as watching.
Source: [[corr-wf13-2-inventory]] 2-004 (T7(c))
Kind: D
Fidelity: variant (as `watchExp`) -/
noncomputable def armExp : Experiment (World × Coin) (Obs × Coin) where
  k := fun wc oc => if oc.2 = wc.2 then
      (if wc.2 = .tails then (if oc.1 = .press then 1 else 0)
        else (if oc.1 = .press then sensorRate wc.1 else 1 - sensorRate wc.1)) else 0
  k_mem := fun ⟨ω, c⟩ => ⟨fun oc => by
      dsimp only; split_ifs <;> cases ω <;> simp [sensorRate, twoPress] <;> norm_num,
    by
      rw [Fintype.sum_prod_type, Obs.sum_eq, Coin.sum_eq, Coin.sum_eq]
      cases c <;> simp [sensorRate, twoPress]⟩

/-- **The post-processing "press if tails":** a deterministic channel on signals that leaves a
heads-signal alone and maps any tails-signal to `(press, tails)`.
Source: [[corr-wf13-2-inventory]] 2-004 (T7(c)) ("the arm post-processes watching's signal")
Kind: D
Fidelity: exact -/
noncomputable def pressIfTails : Obs × Coin → Obs × Coin → ℝ := fun s t =>
  if s.2 = .tails then (if t = (.press, .tails) then 1 else 0) else (if t = s then 1 else 0)

/-- The channel is stochastic (each row a point mass). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pressIfTails_stochastic : Stochastic pressIfTails := by
  intro s
  refine ⟨fun t => by unfold pressIfTails; split_ifs <;> norm_num, ?_⟩
  rcases s with ⟨o, c⟩
  rw [Fintype.sum_prod_type, Obs.sum_eq, Coin.sum_eq, Coin.sum_eq]
  cases o <;> cases c <;> simp [pressIfTails]

/-- **T7(c): the arm is a garbling of watching** through `pressIfTails`: for every state and
every signal, `armExp.k w t = ∑_s watchExp.k w s · pressIfTails s t` — a 16-cell numerical
verification on the one instance, graded N+ like the package's other parametric computations
(audit r2, N-3).
Source: [[corr-wf13-2-inventory]] 2-004 (T7(c))
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem isGarbling_arm : IsGarbling watchExp armExp pressIfTails := by
  rintro ⟨ω, c⟩ ⟨o, c'⟩
  rw [Fintype.sum_prod_type, Obs.sum_eq, Coin.sum_eq, Coin.sum_eq]
  cases c <;> cases c' <;> cases o <;> cases ω <;>
    simp [watchExp, armExp, pressIfTails, sensorRate, twoPress] <;> norm_num

/-- **T7(c): `armExp ≤ watchExp` in the Blackwell order** — the arm is (weakly) less informative
than watching. The Setting-S agent's `102/25 < 213/50` (`settingSValue_eq`) is consistent with
the garbling, as Blackwell's value theorem predicts; that theorem (garbling ⟹ lower value for
every decision problem) is **not proved here**, and the inequality is a separate computation.
This packages the witness `pressIfTails` with `isGarbling_arm` (L, audit r2 N-3).
Source: [[corr-wf13-2-inventory]] 2-004 (T7(c)); miri.md I3.2
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem blackwellLE_arm_watch : BlackwellLE armExp watchExp :=
  ⟨pressIfTails, pressIfTails_stochastic, isGarbling_arm⟩

end Cleanroom.Corrigibility.CorrIndifference.CoinArmS

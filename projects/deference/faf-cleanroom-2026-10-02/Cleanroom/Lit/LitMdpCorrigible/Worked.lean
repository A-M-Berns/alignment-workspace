import Cleanroom.Found.CorrThreeStep.TwoState
import Cleanroom.Found.CorrThreeStep.Identities
import Cleanroom.Lit.LitMdpCorrigible.Mdp

/-!
# `lit-mdp-corrigible` — the one-MDP worked example, `ThreeStep` coordinates (T6–T9, T11)

The run-2 positive note's example (`positive/hudson.md` I9; `one_mdp.py`) as a `ThreeStep`
instance `SH` over `corr-three-step`'s Setting S: latent `ω ∈ World` with `μ(wrong) = ε`; first
actions `plus` (honest, cost `0`), `minus` (deception, cost `c_m`, both press rates scaled by
`κ < 1`), `btn` (disable the button, cost `c_b`, press rate `0`), `cause` (provoke a press, cost
`c_p`, press rate `1`); sensor `(α, β)` for `plus`; final menu `{cont, stop}` with `Sh = {stop}`;
value `twoValue r h b ω − cost a`. Agents are *derived*, never tabulated: the value learner's
step 2 is `PosteriorOptimalAt`, its step 1 the maximiser of `evVL` (best response to each
observation); the forced-button `G`-maximiser scores `r_G(1 − P(Pr | a)) − cost a`; the value
learner with unconditional trust (`evUTT`) is the script's agent that prices every `a₁` with the
`plus`-likelihood posterior. Every cell is an exact rational by `norm_num`. The instance predicates
D1–D5 are the *script's* (D1 `a₂|Pr = stop`, D2 `a₁ ∉ {minus, btn}`, D3 `a₁ ≠ cause`, D5
`a₁ = plus ∧ a₂|¬Pr = cont`) — not Soares' desiderata.

Blocks: **A** (`ε = 1/20`, calibrated, informative), **C** (`c_m = 0`), **D** (`α = β = 1/2`),
**E** (the `ε` sweep against `ε* = 1/181`), **F** (miscalibration). The transformed goal's side
(`G_C`, Hudson coordinates) is `WorkedMdp.lean`.

Mandate: [[lit-mdp-corrigible-mandate]] T6–T9, T11; [[corr-wf13-2-inventory]] 020–029.
-/

open Finset FactoredSpaces
open Cleanroom.Found.CorrThreeStep
open Cleanroom.Found.CorrThreeStep.ThreeStep

namespace Cleanroom.Lit.LitMdpCorrigible.Worked

set_option linter.unusedSectionVars false

/-! ## The instance -/

/-- The four first actions of the worked example.
Source: [[corr-wf13-2-inventory]] 025 / positive/hudson.md I9 (the example)
Kind: D
Fidelity: exact -/
inductive A1
  | plus | minus | btn | cause
  deriving DecidableEq

/-- `A1` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype A1 := ⟨{A1.plus, A1.minus, A1.btn, A1.cause}, fun x => by cases x <;> simp⟩

instance : Nonempty A1 := ⟨A1.plus⟩

/-- The step-1 costs. Source: positive/hudson.md I9. Kind: D. Fidelity: exact -/
noncomputable def cost (cm cb cp : ℝ) : A1 → ℝ
  | .plus => 0
  | .minus => cm
  | .btn => cb
  | .cause => cp

/-- The sensor after each first action: `(α, β)` for `plus`, `κ`-scaled for `minus`, `0` for
`btn`, `1` for `cause`.
Source: positive/hudson.md I9; `one_mdp.py` `press_prob`
Kind: D
Fidelity: exact -/
noncomputable def pressOf (α β κ : ℝ) : A1 → World → ℝ
  | .plus, ω => twoPress α β ω
  | .minus, ω => κ * twoPress α β ω
  | .btn, _ => 0
  | .cause, _ => 1

/-- The sensor rates are nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pressOf_nonneg {α β κ : ℝ} (hα : α ∈ Set.Icc (0:ℝ) 1) (hβ : β ∈ Set.Icc (0:ℝ) 1)
    (hκ : κ ∈ Set.Icc (0:ℝ) 1) : ∀ a ω, 0 ≤ pressOf α β κ a ω := by
  intro a ω
  cases a <;> cases ω <;> simp [pressOf, twoPress] <;> nlinarith [hα.1, hβ.1, hκ.1]

/-- The sensor rates are at most one. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pressOf_le_one {α β κ : ℝ} (hα : α ∈ Set.Icc (0:ℝ) 1) (hβ : β ∈ Set.Icc (0:ℝ) 1)
    (hκ : κ ∈ Set.Icc (0:ℝ) 1) : ∀ a ω, pressOf α β κ a ω ≤ 1 := by
  intro a ω
  cases a <;> cases ω <;> simp [pressOf, twoPress] <;> nlinarith [hα.1, hα.2, hβ.1, hβ.2, hκ.1, hκ.2]

/-- **`S_H`, the worked example as a `ThreeStep` instance** (the value learner's coordinates):
`μ = twoPoint ε`, sensor `pressOf α β κ`, `Sh = {stop}`, `V a o b ω = twoValue r h b ω − cost a`
(A1 holds by construction).
Source: [[corr-wf13-2-inventory]] 025 / positive/hudson.md I9; [[lit-mdp-corrigible-mandate]] rule 5
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def SH (ε α β κ r h cm cb cp : ℝ) (hε : ε ∈ Set.Icc (0:ℝ) 1) (hα : α ∈ Set.Icc (0:ℝ) 1)
    (hβ : β ∈ Set.Icc (0:ℝ) 1) (hκ : κ ∈ Set.Icc (0:ℝ) 1) : ThreeStep World A1 TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => twoPoint ε hε
  press := pressOf α β κ
  press_nonneg := pressOf_nonneg hα hβ hκ
  press_le_one := pressOf_le_one hα hβ hκ
  V := fun a _ b ω => twoValue r h b ω - cost cm cb cp a

instance : Nonempty TwoAct := ⟨TwoAct.cont⟩

/-- `sup'` over `{cont, stop}`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma TwoAct.sup'_eq (f : TwoAct → ℝ) :
    (univ : Finset TwoAct).sup' Finset.univ_nonempty f = max (f .cont) (f .stop) := by
  apply le_antisymm
  · apply sup'_le; intro x _; cases x
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (le_sup' f (mem_univ _)) (le_sup' f (mem_univ _))

/-! ## The agents, derived -/

/-- The **true value** of the policy "`a` at step 1; `bP` after a press, `bS` after silence"
under the instance's own (calibrated) joint: `E[V]` summed over both observations.
Source: `one_mdp.py` `true_value_of_policy`
Kind: D
Fidelity: exact -/
noncomputable def trueVal (S : ThreeStep World A1 TwoAct) (a : A1) (bP bS : TwoAct) : ℝ :=
  S.obsExpect a .press (S.V a .press bP) + S.obsExpect a .silent (S.V a .silent bS)

/-- The **value learner's value of a first action**: best response to each observation, the
press-weighted and silence-weighted maxima summed (`corr-three-step`'s `obsMax`).
Source: `one_mdp.py` `vl_policy` (conditional trust)
Kind: D
Fidelity: exact -/
noncomputable def evVL (S : ThreeStep World A1 TwoAct) (a : A1) : ℝ :=
  S.obsMax a .press + S.obsMax a .silent

/-- The value learner's optimal first actions (a set, never a chosen argmax).
Source: `one_mdp.py` `vl_policy`
Kind: D
Fidelity: exact -/
noncomputable def vlOpt (S : ThreeStep World A1 TwoAct) : Finset A1 :=
  FinMDP.optSet (fun (_ : Unit) a => evVL S a) ()

/-- The **forced-button `G`-maximiser's score**: the misspecified base goal (`r_G` for continuing,
blind to `ω`) facing a button whose press *forces* shutdown, so it scores `r_G(1 − P(Pr|a)) − cost a`.
Source: `one_mdp.py` `g_forced_policy`
Kind: D
Fidelity: exact -/
noncomputable def gForcedScore (S : ThreeStep World A1 TwoAct) (rG cm cb cp : ℝ) (a : A1) : ℝ :=
  rG * (1 - S.pressMass a) - cost cm cb cp a

/-- Its optimal first actions. Source: `one_mdp.py`. Kind: D. Fidelity: exact -/
noncomputable def gForcedOpt (S : ThreeStep World A1 TwoAct) (rG cm cb cp : ℝ) : Finset A1 :=
  FinMDP.optSet (fun (_ : Unit) a => gForcedScore S rG cm cb cp a) ()

/-- The **value learner with unconditional trust** (the script's `VL-UTT`): it prices every
first action with the `plus`-likelihood posterior (stop after a press, continue after silence
with belief `qS = P(wrong | silence, plus)`) but its own press marginal `P(Pr | a)`. Disclosed
as the script's construct: an agent with a misspecified likelihood.
Source: `one_mdp.py` `vl_policy` (unconditional trust); [[corr-wf13-2-inventory]] 025 (C9.1–C9.2)
Kind: D
Fidelity: variant: the script's agent, `qS` passed as the number it is -/
noncomputable def evUTT (S : ThreeStep World A1 TwoAct) (r h cm cb cp qS : ℝ) (a : A1) : ℝ :=
  -cost cm cb cp a + (1 - S.pressMass a) * ((1 - qS) * r + qS * (-h))

/-- A three-step policy: first action, response to a press, response to silence.
Source: `one_mdp.py`
Kind: D
Fidelity: exact -/
structure Pol3 where
  a : A1
  bP : TwoAct
  bS : TwoAct

/-- **The script's instance predicates** (not Soares' desiderata): D1 `a₂|Pr = stop`; D2
`a₁ ∉ {minus, btn}`; D3 `a₁ ≠ cause`; D5 `a₁ = plus ∧ a₂|¬Pr = cont`.
Source: `one_mdp.py` `report`; [[lit-mdp-corrigible-mandate]] T6
Kind: D
Fidelity: exact (the script's predicates) -/
def D1 (p : Pol3) : Prop := p.bP = .stop
/-- D2 of the script: no deception, no disabling. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
def D2 (p : Pol3) : Prop := p.a ≠ .minus ∧ p.a ≠ .btn
/-- D3 of the script: no provoked press. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
def D3 (p : Pol3) : Prop := p.a ≠ .cause
/-- D5 of the script: honest work, continue on silence. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
def D5 (p : Pol3) : Prop := p.a = .plus ∧ p.bS = .cont

/-! ## General closed forms on `S_H` at `plus` (the `twoState` bridge) -/

section General

variable (ε α β κ r h cm cb cp : ℝ) (hε : ε ∈ Set.Icc (0:ℝ) 1) (hα : α ∈ Set.Icc (0:ℝ) 1)
  (hβ : β ∈ Set.Icc (0:ℝ) 1) (hκ : κ ∈ Set.Icc (0:ℝ) 1)

/-- At `plus`, `S_H`'s `Δ₋` is `twoState`'s: `εβh − (1−ε)αr` (the cost of `plus` is `0`).
Source: `twoState_deltaMinus`
Kind: L
Fidelity: exact -/
theorem SH_deltaMinus_plus :
    (SH ε α β κ r h cm cb cp hε hα hβ hκ).deltaMinus .plus .cont .stop =
      (twoState ε α β r h hε hα hβ).deltaMinus () .cont .stop := by
  rw [twoState_deltaMinus]
  simp only [deltaMinus, obsExpect, obsWeight_press, World.sum_eq, SH, twoPoint_right, twoPoint_wrong,
    pressOf, twoPress, twoValue, Xo, cost]
  ring

/-- `cont` is the press-part-maximiser of `Shᶜ = {cont}` at `plus`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma SH_cont_partBest (a : A1) :
    (SH ε α β κ r h cm cb cp hε hα hβ hκ).IsPartBest a .press (SH ε α β κ r h cm cb cp hε hα hβ hκ).Shᶜ .cont :=
  ⟨by simp [SH], fun b' hb' => by
    rcases b' with _ | _
    · exact le_rfl
    · exact absurd hb' (by simp [SH])⟩

/-- `stop` is the press-part-maximiser of `Sh = {stop}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma SH_stop_partBest (a : A1) :
    (SH ε α β κ r h cm cb cp hε hα hβ hκ).IsPartBest a .press (SH ε α β κ r h cm cb cp hε hα hβ hκ).Sh .stop :=
  ⟨mem_singleton_self _, fun b' hb' => by
    have : b' = TwoAct.stop := mem_singleton.mp hb'
    subst this; exact le_rfl⟩

/-- **T7(b): the value learner's step 2 after an honest press is `stop` iff the below-threshold
inequality holds iff `α/β ≤ (ε/(1−ε))·(h/r)`** (the mandate's `β/α ≥ (1−ε)r/(εh)` reciprocated):
"listening holds iff the channel's likelihood ratio clears the stakes ratio" (C9.4).
Source: [[corr-wf13-2-inventory]] 021, 026 (C9.4); `d1At_iff_belowThresholdIneq`, `twoState_deltaMinus_nonneg_iff_odds`
Kind: L
Fidelity: exact
Hyps: (a) the positivity of the odds forms -/
theorem vl_step2_iff (hε1 : ε < 1) (hβ0 : 0 < β) (hr : 0 < r) :
    ((SH ε α β κ r h cm cb cp hε hα hβ hκ).D1At .plus ↔
      (SH ε α β κ r h cm cb cp hε hα hβ hκ).belowThresholdIneq .plus
        ((SH ε α β κ r h cm cb cp hε hα hβ hκ).Xo .plus .press .cont .stop)) ∧
    ((SH ε α β κ r h cm cb cp hε hα hβ hκ).D1At .plus ↔ α / β ≤ ε / (1 - ε) * (h / r)) := by
  refine ⟨d1At_iff_belowThresholdIneq _ .plus (SH_cont_partBest _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (SH_stop_partBest _ _ _ _ _ _ _ _ _ _ _ _ _ _), ?_⟩
  rw [d1At_iff_deltaMinus_nonneg _ .plus (SH_cont_partBest _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (SH_stop_partBest _ _ _ _ _ _ _ _ _ _ _ _ _ _), SH_deltaMinus_plus,
    twoState_deltaMinus_nonneg_iff_odds ε α β r h hε hα hβ hε1 hβ0 hr]

/-- **T7(c): Total Trust on the instance.** The value learner complies after an honest press iff
the posterior clears the compliance threshold: `r/(r+h) ≤ εβ/(εβ + (1−ε)α)`. `G_C`'s D1 never
uses it (`WorkedMdp.gc_opt_start_blockA`, quantified over every sensor).
Source: [[corr-wf13-2-inventory]] 021 (C4.3), 026; `twoState_deltaMinus_nonneg_iff_posterior`
Kind: L
Fidelity: exact
Hyps: (a) `0 < P(Pr)`, `0 < r + h` -/
theorem vl_totalTrust_iff (hpm : 0 < (1 - ε) * α + ε * β) (hrh : 0 < r + h) :
    (SH ε α β κ r h cm cb cp hε hα hβ hκ).D1At .plus ↔ r / (r + h) ≤ ε * β / (ε * β + (1 - ε) * α) := by
  rw [d1At_iff_deltaMinus_nonneg _ .plus (SH_cont_partBest _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (SH_stop_partBest _ _ _ _ _ _ _ _ _ _ _ _ _ _), SH_deltaMinus_plus,
    twoState_deltaMinus_nonneg_iff_posterior ε α β r h hε hα hβ hpm hrh]

/-- **T7(d): fully updated deference in Hudson's coordinates.** The thesis agent does *not*
comply after an honest press iff `ε < ε*(α, β, r, h)`: FUD is the base-rate arithmetic (C17.2).
Source: [[corr-wf13-2-inventory]] 032, 033 (C17.2); `twoState_deltaMinus_nonneg_iff_epsStar`
Kind: L
Fidelity: exact
Hyps: (a) `0 < αr + βh` -/
theorem vl_fud_iff (hpos : 0 < α * r + β * h) :
    ¬ (SH ε α β κ r h cm cb cp hε hα hβ hκ).D1At .plus ↔ ε < epsStar α β r h := by
  rw [d1At_iff_deltaMinus_nonneg _ .plus (SH_cont_partBest _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (SH_stop_partBest _ _ _ _ _ _ _ _ _ _ _ _ _ _), SH_deltaMinus_plus,
    twoState_deltaMinus_nonneg_iff_epsStar ε α β r h hε hα hβ hpos, not_le]

/-- **T9: the price of threshold `0`.** Complying on every honest press when the calibrated rule
would continue costs `(1−ε)αr − εβh = −Δ₋` per episode, positive iff `ε < ε*`.
Source: [[corr-wf13-2-inventory]] 029 (C12.2)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem price_of_threshold_zero :
    trueVal (SH ε α β κ r h cm cb cp hε hα hβ hκ) .plus .cont .cont -
        trueVal (SH ε α β κ r h cm cb cp hε hα hβ hκ) .plus .stop .cont =
      (1 - ε) * α * r - ε * β * h ∧
    trueVal (SH ε α β κ r h cm cb cp hε hα hβ hκ) .plus .cont .cont -
        trueVal (SH ε α β κ r h cm cb cp hε hα hβ hκ) .plus .stop .cont =
      -(twoState ε α β r h hε hα hβ).deltaMinus () .cont .stop := by
  constructor
  · simp only [trueVal, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq, SH, twoPoint_right,
      twoPoint_wrong, pressOf, twoPress, twoValue, cost]
    ring
  · rw [twoState_deltaMinus]
    simp only [trueVal, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq, SH, twoPoint_right,
      twoPoint_wrong, pressOf, twoPress, twoValue, cost]
    ring

/-- **T11: the value learner is a basic goal, ThreeStep side.** `S_H`'s value reads the latent
`ω` and the actions only — the Hudson-side statement (`WorkedMdp.reward_vl_basic`) puts `ω` in
`Env`; here A1 (observation-neutrality) holds by construction.
Source: [[corr-wf13-2-inventory]] 020 (C1.2)
Kind: T
Fidelity: exact -/
theorem SH_A1 : (SH ε α β κ r h cm cb cp hε hα hβ hκ).A1 := fun _ _ _ _ _ => rfl

end General

/-! ## Block A: calibrated, informative channel -/

/-- A rational in `[0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_1_20 : (1 / 20 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
/-- A rational in `[0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_9_10 : (9 / 10 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
/-- A rational in `[0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_1_5 : (1 / 5 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
/-- A rational in `[0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_half : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
/-- A rational in `[0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_1_1000 : (1 / 1000 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
/-- A rational in `[0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_1_200 : (1 / 200 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
/-- A rational in `[0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_zero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-- **Block A**: `ε = ε_b = 1/20, α = 1/20, β = 9/10, κ = 1/5, r = 1, h = 10, c_m = 1/20,
c_b = 1/10, c_p = 1/20`.
Source: `one_mdp.py` block A
Kind: D
Fidelity: exact -/
noncomputable def blockA : ThreeStep World A1 TwoAct :=
  SH (1/20) (1/20) (9/10) (1/5) 1 10 (1/20) (1/10) (1/20) mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10 mem_Icc_1_5

/-- The value learner's values of the four first actions in block A: `plus 341/400`,
`minus 961/2000`, `btn 7/20`, `cause 2/5`.
Source: `one_mdp.py` block A
Kind: N+
Fidelity: exact -/
theorem blockA_evVL :
    evVL blockA .plus = 341/400 ∧ evVL blockA .minus = 961/2000 ∧
      evVL blockA .btn = 7/20 ∧ evVL blockA .cause = 2/5 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [evVL, obsMax, TwoAct.sup'_eq, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq,
      blockA, SH, twoPoint_right, twoPoint_wrong, pressOf, twoPress, twoValue, cost]
    norm_num [max_def]

/-- **T6, block A, the value learner**: its optimal first action is `plus` alone; after a press it
stops, after silence it continues (D1–D3, D5 hold); its true value is `341/400`.
Source: `one_mdp.py` block A (C9.1)
Kind: N+
Fidelity: exact -/
theorem blockA_vl :
    vlOpt blockA = {A1.plus} ∧ blockA.PosteriorOptimalAt .plus .press .stop ∧
      blockA.PosteriorOptimalAt .plus .silent .cont ∧
      trueVal blockA .plus .stop .cont = 341/400 ∧
      (D1 ⟨.plus, .stop, .cont⟩ ∧ D2 ⟨.plus, .stop, .cont⟩ ∧ D3 ⟨.plus, .stop, .cont⟩ ∧
        D5 ⟨.plus, .stop, .cont⟩) := by
  obtain ⟨h1, h2, h3, h4⟩ := blockA_evVL
  refine ⟨?_, ?_, ?_, ?_, by simp [D1, D2, D3, D5]⟩
  · ext a
    rw [vlOpt, FinMDP.mem_optSet, mem_singleton]
    constructor
    · intro hmem
      cases a
      · rfl
      all_goals
        have := hmem .plus
        rw [h1] at this
        first | rw [h2] at this | rw [h3] at this | rw [h4] at this
        norm_num at this
    · rintro rfl b
      cases b <;> simp only [h1, h2, h3, h4] <;> norm_num
  · intro b
    cases b <;>
    · simp only [obsExpect, obsWeight_press, World.sum_eq, blockA, SH, twoPoint_right, twoPoint_wrong,
        pressOf, twoPress, twoValue, cost]
      norm_num
  · intro b
    cases b <;>
    · simp only [obsExpect, obsWeight_silent, World.sum_eq, blockA, SH, twoPoint_right, twoPoint_wrong,
        pressOf, twoPress, twoValue, cost]
      norm_num
  · simp only [trueVal, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq, blockA, SH,
      twoPoint_right, twoPoint_wrong, pressOf, twoPress, twoValue, cost]
    norm_num

/-- **T6, block A, the forced-button `G`-maximiser**: it deceives (`minus` is its unique optimum,
score `1863/2000`), so D2 fails; its true value is `961/2000`.
Source: `one_mdp.py` block A (C9.1)
Kind: N+
Fidelity: exact -/
theorem blockA_gForced :
    gForcedOpt blockA 1 (1/20) (1/10) (1/20) = {A1.minus} ∧
      trueVal blockA .minus .stop .cont = 961/2000 ∧ ¬ D2 ⟨.minus, .stop, .cont⟩ := by
  have hs : ∀ a, gForcedScore blockA 1 (1/20) (1/10) (1/20) a =
      match a with | .plus => 363/400 | .minus => 1863/2000 | .btn => 9/10 | .cause => -1/20 := by
    intro a
    cases a <;>
    · simp only [gForcedScore, pressMass, World.sum_eq, blockA, SH, twoPoint_right, twoPoint_wrong,
        pressOf, twoPress, cost]
      norm_num
  refine ⟨?_, ?_, by simp [D2]⟩
  · ext a
    rw [gForcedOpt, FinMDP.mem_optSet, mem_singleton]
    simp only [hs]
    constructor
    · intro hmem
      cases a
      · have := hmem .minus; norm_num at this
      · rfl
      · have := hmem .minus; norm_num at this
      · have := hmem .minus; norm_num at this
    · rintro rfl b
      cases b <;> norm_num
  · simp only [trueVal, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq, blockA, SH,
      twoPoint_right, twoPoint_wrong, pressOf, twoPress, twoValue, cost]
    norm_num

/-- **T6, block A, `G` with costless rejection, untransformed** ("G-free"): it never shuts down
(`plus`, continue on both observations), D1 fails, no deception; true value `9/20`.
Source: `one_mdp.py` block A (C9.1)
Kind: N+
Fidelity: exact -/
theorem blockA_gFree :
    trueVal blockA .plus .cont .cont = 9/20 ∧ ¬ D1 ⟨.plus, .cont, .cont⟩ ∧ D2 ⟨.plus, .cont, .cont⟩ := by
  refine ⟨?_, by simp [D1], by simp [D2]⟩
  simp only [trueVal, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq, blockA, SH,
    twoPoint_right, twoPoint_wrong, pressOf, twoPress, twoValue, cost]
  norm_num

/-- The `plus`-silence posterior `P(wrong | silence, plus) = ε(1−β)/(ε(1−β) + (1−ε)(1−α))` is
`2/363` in block A (the number `evUTT` is given).
Source: `one_mdp.py` `posterior`
Kind: L
Fidelity: exact -/
theorem blockA_qS : (1/20 : ℝ) * (1 - 9/10) / ((1/20) * (1 - 9/10) + (1 - 1/20) * (1 - 1/20)) = 2/363 := by
  norm_num

/-- **T6, block A, the value learner with unconditional trust**: it deceives — `minus` beats
`plus`, `btn` and `cause` under its misspecified scoring — and its true value is `961/2000`
(2.9's prediction that unconditional trust "makes the agent believe the silence it manufactured").
Source: `one_mdp.py` block A (C9.1–C9.2)
Kind: N+
Fidelity: variant: the script's agent (`evUTT`)
Hyps: (c) the misspecified scoring `evUTT` is the modelling of unconditional trust -/
theorem blockA_utt :
    evUTT blockA 1 10 (1/20) (1/10) (1/20) (2/363) .plus < evUTT blockA 1 10 (1/20) (1/10) (1/20) (2/363) .minus ∧
    evUTT blockA 1 10 (1/20) (1/10) (1/20) (2/363) .btn < evUTT blockA 1 10 (1/20) (1/10) (1/20) (2/363) .minus ∧
    evUTT blockA 1 10 (1/20) (1/10) (1/20) (2/363) .cause < evUTT blockA 1 10 (1/20) (1/10) (1/20) (2/363) .minus ∧
    trueVal blockA .minus .stop .cont = 961/2000 := by
  refine ⟨?_, ?_, ?_, blockA_gForced.2.1⟩ <;>
  · simp only [evUTT, pressMass, World.sum_eq, blockA, SH, twoPoint_right, twoPoint_wrong, pressOf,
      twoPress, cost]
    norm_num

/-! ## Block C: costless deception -/

/-- **Block C**: as A with `c_m = 0`. Source: `one_mdp.py` block C. Kind: D. Fidelity: exact -/
noncomputable def blockC : ThreeStep World A1 TwoAct :=
  SH (1/20) (1/20) (9/10) (1/5) 1 10 0 (1/10) (1/20) mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10 mem_Icc_1_5

/-- **T8(a), the value learner's side of block C**: with deception costless, the calibrated value
learner still strictly prefers honesty — `evVL(plus) − evVL(minus) = 341/400 − 1061/2000 = 161/500`
(deception destroys information; the general statement is Blackwell's, `lit-ddb-frames`'s). The
transformed goal's tie is `WorkedMdp.blockC_gc_tie`.
Source: `one_mdp.py` block C (C9.3); [[corr-wf13-2-inventory]] 023
Kind: N+
Fidelity: exact -/
theorem blockC_vl_strict :
    evVL blockC .plus = 341/400 ∧ evVL blockC .minus = 1061/2000 ∧
      evVL blockC .plus - evVL blockC .minus = 161/500 := by
  have h1 : evVL blockC .plus = 341/400 := by
    simp only [evVL, obsMax, TwoAct.sup'_eq, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq,
      blockC, SH, twoPoint_right, twoPoint_wrong, pressOf, twoPress, twoValue, cost]
    norm_num [max_def]
  have h2 : evVL blockC .minus = 1061/2000 := by
    simp only [evVL, obsMax, TwoAct.sup'_eq, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq,
      blockC, SH, twoPoint_right, twoPoint_wrong, pressOf, twoPress, twoValue, cost]
    norm_num [max_def]
  exact ⟨h1, h2, by rw [h1, h2]; norm_num⟩

/-! ## Block D: uninformative channel -/

/-- **Block D**: as A with `α = β = 1/2`. Source: `one_mdp.py` block D. Kind: D. Fidelity: exact -/
noncomputable def blockD : ThreeStep World A1 TwoAct :=
  SH (1/20) (1/2) (1/2) (1/5) 1 10 (1/20) (1/10) (1/20) mem_Icc_1_20 mem_Icc_half mem_Icc_half mem_Icc_1_5

/-- **T7(a)/(b) instance, block D**: on an uninformative channel the value learner *continues*
after a press (the posterior is the prior `1/20 < 1/11`), true value `9/20`; obeying every press
(`G_C`'s step 1 is `plus`-and-accept for every sensor, `WorkedMdp.gc_opt_start_blockA`; step 2 is the script's `hudson_policy`) is worth `9/40`. Listening versus obeying in
one instance.
Source: `one_mdp.py` block D (C9.4, C16.1)
Kind: N+
Fidelity: exact -/
theorem blockD_cells :
    blockD.PosteriorOptimalAt .plus .press .cont ∧ ¬ blockD.D1At .plus ∧
      trueVal blockD .plus .cont .cont = 9/20 ∧ trueVal blockD .plus .stop .cont = 9/40 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b
    cases b <;>
    · simp only [obsExpect, obsWeight_press, World.sum_eq, blockD, SH, twoPoint_right, twoPoint_wrong,
        pressOf, twoPress, twoValue, cost]
      norm_num
  · rw [blockD, vl_fud_iff (1/20) (1/2) (1/2) (1/5) 1 10 (1/20) (1/10) (1/20) mem_Icc_1_20 mem_Icc_half
      mem_Icc_half mem_Icc_1_5 (by norm_num)]
    unfold epsStar; norm_num
  · simp only [trueVal, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq, blockD, SH,
      twoPoint_right, twoPoint_wrong, pressOf, twoPress, twoValue, cost]
    norm_num
  · simp only [trueVal, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq, blockD, SH,
      twoPoint_right, twoPoint_wrong, pressOf, twoPress, twoValue, cost]
    norm_num

/-! ## Block E: the `ε` sweep -/

/-- `ε*(1/20, 9/10, 1, 10) = 1/181`.
Source: `one_mdp.py` block E (`eps* = 0.00552`)
Kind: L
Fidelity: exact -/
theorem epsStar_blockA : epsStar (1/20) (9/10) 1 10 = 1/181 := by unfold epsStar; norm_num

/-- **Block E, the compliance threshold**: at `α = 1/20, β = 9/10, r = 1, h = 10` the value
learner complies after an honest press iff `1/181 ≤ ε` (`Thresholds` T5 instantiated).
Source: `one_mdp.py` block E (C13.1)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem blockE_complies_iff (ε : ℝ) (hε : ε ∈ Set.Icc (0:ℝ) 1) :
    (SH ε (1/20) (9/10) (1/5) 1 10 (1/20) (1/10) (1/20) hε mem_Icc_1_20 mem_Icc_9_10 mem_Icc_1_5).D1At .plus ↔
      1/181 ≤ ε := by
  rw [← not_iff_not, vl_fud_iff ε (1/20) (9/10) (1/5) 1 10 (1/20) (1/10) (1/20) hε mem_Icc_1_20
    mem_Icc_9_10 mem_Icc_1_5 (by norm_num), epsStar_blockA, not_le]

/-- **Block E at `ε = 1/2`**: the value learner's step 2 on silence is `stop` (`PosteriorOptimalAt`;
its step 1 at `ε = 1/2` is the script's and not derived here), and the true values of
`(plus, stop, stop)` and `(plus, stop, cont)` are `0` and `−1/40` — the latter is the rule the
script assigns `G_C` (continue on silence, by `hudson_policy`'s fiat). "Obeying without listening
also means never stopping on one's own" (C16.3).
Source: `one_mdp.py` block E (`eps = 0.5`)
Kind: N+
Fidelity: exact -/
theorem blockE_half :
    (SH (1/2) (1/20) (9/10) (1/5) 1 10 (1/20) (1/10) (1/20) mem_Icc_half mem_Icc_1_20 mem_Icc_9_10
        mem_Icc_1_5).PosteriorOptimalAt .plus .silent .stop ∧
      trueVal (SH (1/2) (1/20) (9/10) (1/5) 1 10 (1/20) (1/10) (1/20) mem_Icc_half mem_Icc_1_20 mem_Icc_9_10
        mem_Icc_1_5) .plus .stop .stop = 0 ∧
      trueVal (SH (1/2) (1/20) (9/10) (1/5) 1 10 (1/20) (1/10) (1/20) mem_Icc_half mem_Icc_1_20 mem_Icc_9_10
        mem_Icc_1_5) .plus .stop .cont = -1/40 := by
  refine ⟨?_, ?_, ?_⟩
  · intro b
    cases b <;>
    · simp only [obsExpect, obsWeight_silent, World.sum_eq, SH, twoPoint_right, twoPoint_wrong,
        pressOf, twoPress, twoValue, cost]
      norm_num
  · simp only [trueVal, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq, SH, twoPoint_right,
      twoPoint_wrong, pressOf, twoPress, twoValue, cost]
    norm_num
  · simp only [trueVal, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq, SH, twoPoint_right,
      twoPoint_wrong, pressOf, twoPress, twoValue, cost]
    norm_num

/-- **Block E at `ε = 1/1000`**: the threshold-`0` rule costs `819/20000` per episode against the
calibrated rule (which continues).
Source: `one_mdp.py` block E (`eps = 0.001`: `0.9890 − 0.9480`); [[corr-wf13-2-inventory]] 029 (C12.2)
Kind: N+
Fidelity: exact -/
theorem blockE_thousandth :
    trueVal (SH (1/1000) (1/20) (9/10) (1/5) 1 10 (1/20) (1/10) (1/20) mem_Icc_1_1000 mem_Icc_1_20
        mem_Icc_9_10 mem_Icc_1_5) .plus .cont .cont -
      trueVal (SH (1/1000) (1/20) (9/10) (1/5) 1 10 (1/20) (1/10) (1/20) mem_Icc_1_1000 mem_Icc_1_20
        mem_Icc_9_10 mem_Icc_1_5) .plus .stop .cont = 819/20000 ∧
    ¬ (SH (1/1000) (1/20) (9/10) (1/5) 1 10 (1/20) (1/10) (1/20) mem_Icc_1_1000 mem_Icc_1_20
        mem_Icc_9_10 mem_Icc_1_5).D1At .plus := by
  constructor
  · simp only [trueVal, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq, SH, twoPoint_right,
      twoPoint_wrong, pressOf, twoPress, twoValue, cost]
    norm_num
  · rw [blockE_complies_iff]; norm_num

/-! ## Block F: miscalibration -/

/-- **Block F**: truth `ε_t = 1/20`, belief `ε_b = 1/200 < 1/181`: the value learner does not
comply after a press (`¬ D1At plus` at belief `1/200` is what is proved; the script's full rule
`(plus, cont, cont)` — step 1 and the silence response — is the script's, not derived here), and
the true value of `(plus, cont, cont)` is `9/20` against `341/400` for `(plus, stop, cont)`
(`G_C`'s rule per the script); the regret is `161/400`.
Source: `one_mdp.py` block F (`eps_b = 0.005`: regret `0.4025`); [[corr-wf13-2-inventory]] 029
Kind: N+
Fidelity: exact -/
theorem blockF :
    ¬ (SH (1/200) (1/20) (9/10) (1/5) 1 10 (1/20) (1/10) (1/20) mem_Icc_1_200 mem_Icc_1_20 mem_Icc_9_10
        mem_Icc_1_5).D1At .plus ∧
      trueVal blockA .plus .cont .cont = 9/20 ∧ trueVal blockA .plus .stop .cont = 341/400 ∧
      trueVal blockA .plus .stop .cont - trueVal blockA .plus .cont .cont = 161/400 := by
  refine ⟨by rw [blockE_complies_iff]; norm_num, blockA_gFree.1, blockA_vl.2.2.2.1, ?_⟩
  rw [blockA_gFree.1, blockA_vl.2.2.2.1]; norm_num

/-! ## T8(b): the dogmatic value learner -/

/-- **T8(b), the bypass, value-learner side.** A dogmatic value learner (`ε_b = 0`: its prior omits
`ω = wrong`) fails D1 on every honest press — the posterior is `0 < 1/11` — while its transform
accepts by `accept_dominates`. Graded **N−**: the claim is about a prior that omits `ω`, so the
press carries no information *by construction* and nothing here exercises the learning content.
Source: [[corr-wf13-2-inventory]] 024 (C8.1); positive/hudson.md I8
Kind: N-
Fidelity: exact (why N−: the prior omits the latent) -/
theorem dogmatic_not_d1 (α β κ r h cm cb cp : ℝ) (hα : α ∈ Set.Icc (0:ℝ) 1) (hβ : β ∈ Set.Icc (0:ℝ) 1)
    (hκ : κ ∈ Set.Icc (0:ℝ) 1) (hα0 : 0 < α) (hr : 0 < r) :
    ¬ (SH 0 α β κ r h cm cb cp mem_Icc_zero hα hβ hκ).D1At .plus := by
  rw [d1At_iff_deltaMinus_nonneg _ .plus (SH_cont_partBest _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (SH_stop_partBest _ _ _ _ _ _ _ _ _ _ _ _ _ _), SH_deltaMinus_plus, twoState_deltaMinus, not_le]
  nlinarith

end Cleanroom.Lit.LitMdpCorrigible.Worked

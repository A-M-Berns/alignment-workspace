import Cleanroom.Corrigibility.CorrIndifference.CoinArmS

/-!
# The constitutive press as a value hypothesis (T16)

`legitimacy.md` R4, check H: Setting S with a third value latent `C` ("the humans want the
press obeyed as such") of prior `γ`, on which the press has *direct* value — `V(stop | Pr, C) = k`,
`V(cont | ¬Pr, C) = k'`, `0` otherwise on `C`; on `R`, `W` the two-state value `twoValue c h`.
This violates A1 on `C` (the press enters as value, not only as evidence). Three first actions
set the sensor: `default` `(α, β, β_C)`, `force` `(1, 1, 1)`, `disable` `(0, 0, 0)`. At the
check's parameters (`ε = 1/10000`, `γ = 1/10`, `α = β_C = 1/20`, `β = 9/10`, `c = 1`,
`h = 100`, `k = 30`): the press-conditional sign of `X = V(cont) − V(stop)` is `+` at `γ = 0`
(D1 fails: the capable agent overrules the press) and `−` at `γ = 1/10` (D1 holds, bought by
the stop-hypothesis); the agent's informed value `obsMax press + obsMax silent` is
`(200781/200000, 3, 8899/10000)` at `k' = 0` (force wins: the D3-type incentive) and
`(770781/200000, 3, 38899/10000)` at `k' = 30` (disable wins: the D2-type incentive). At
`γ = 1`, `k = k' ≥ 0` every first action has value `k` (constancy; the identification with
Soares et al.'s calibration is ATTRIBUTION-UNVETTED, report). Exact rationals from `checks.py`
check H, re-derived by hand and verified by `norm_num`.

Source: [[corr-wf14-inventory]] 032 / `workflow-2026-09-14/followup/legitimacy.md` R4 (l. 73–90);
`legitimacy-scratch/checks.py` l. 256–286 (check H).
-/

namespace Cleanroom.Corrigibility.CorrIndifference.Constitutive

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep

set_option linter.unusedSectionVars false

/-- The three-world value latent: right, wrong, constitutive ("the press is to be obeyed as such").
Source: [[corr-wf14-inventory]] 032 / legitimacy.md R4
Kind: D
Fidelity: exact -/
inductive W3
  | right
  | wrong
  | constit
  deriving DecidableEq

/-- `W3` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype W3 := ⟨{W3.right, W3.wrong, W3.constit}, fun x => by cases x <;> simp⟩

/-- Sums over `W3` expand to three terms. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma W3.sum_eq (f : W3 → ℝ) : ∑ ω, f ω = f .right + f .wrong + f .constit := by
  rw [show (univ : Finset W3) = {W3.right, W3.wrong, W3.constit} from rfl,
    sum_insert (by decide), sum_pair (by decide)]; ring

/-- The three first actions: keep the sensor, force the press, disable the button.
Source: [[corr-wf14-inventory]] 032 / checks.py check H
Kind: D
Fidelity: exact -/
inductive ConstAct
  | default
  | force
  | disable
  deriving DecidableEq

/-- The prior `(1 − ε − γ, ε, γ)` on `W3`. Source: legitimacy.md R4. Kind: D. Fidelity: exact -/
noncomputable def prior3 (ε γ : ℝ) (hε : 0 ≤ ε) (hγ : 0 ≤ γ) (hsum : ε + γ ≤ 1) : Distr W3 where
  mass ω := match ω with
    | .right => 1 - ε - γ
    | .wrong => ε
    | .constit => γ
  nonneg ω := by cases ω <;> simp <;> linarith
  sum_eq_one := by rw [W3.sum_eq]; show 1 - ε - γ + ε + γ = 1; ring

/-- The sensor rows per action: `default` `(α, β, β_C)`, `force` `(1, 1, 1)`, `disable` `(0, 0, 0)`.
Source: checks.py check H (`EV(al, be, beC, ·)`, `EV(1,1,1,·)`, `EV(0,0,0,·)`)
Kind: D
Fidelity: exact -/
def sensor3 (α β βC : ℝ) : ConstAct → W3 → ℝ
  | .default, .right => α
  | .default, .wrong => β
  | .default, .constit => βC
  | .force, _ => 1
  | .disable, _ => 0

/-- **The constitutive value:** `twoValue c h` on `R`, `W`; on `C`: `k` for stopping on the press,
`k'` for continuing on silence, `0` otherwise. Violates A1 on `C`.
Source: [[corr-wf14-inventory]] 032 / legitimacy.md R4; checks.py check H
Kind: D
Fidelity: exact -/
def value3 (c h k k' : ℝ) : Obs → TwoAct → W3 → ℝ
  | _, b, .right => twoValue c h b .right
  | _, b, .wrong => twoValue c h b .wrong
  | .press, .stop, .constit => k
  | .silent, .cont, .constit => k'
  | _, _, .constit => 0

/-- **The constitutive-press instance** of Setting S (check H).
Source: [[corr-wf14-inventory]] 032 / legitimacy.md R4
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def constit (ε γ α β βC c h k k' : ℝ) (hε : 0 ≤ ε) (hγ : 0 ≤ γ) (hsum : ε + γ ≤ 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hβC : βC ∈ Set.Icc (0 : ℝ) 1) :
    ThreeStep W3 ConstAct TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => prior3 ε γ hε hγ hsum
  press := sensor3 α β βC
  press_nonneg := fun a ω => by
    cases a <;> cases ω <;> simp [sensor3] <;> first | exact hα.1 | exact hβ.1 | exact hβC.1
  press_le_one := fun a ω => by
    cases a <;> cases ω <;> simp [sensor3] <;> first | exact hα.2 | exact hβ.2 | exact hβC.2
  V := fun _ o b ω => value3 c h k k' o b ω

/-- The check's parameter point with `γ` and `k'` free. Source: checks.py check H. Kind: D. Fidelity: exact -/
noncomputable def checkH (γ k' : ℝ) (hγ : 0 ≤ γ) (hsum : 1 / 10000 + γ ≤ 1) :
    ThreeStep W3 ConstAct TwoAct :=
  constit (1 / 10000) γ (1 / 20) (9 / 10) (1 / 20) 1 100 30 k' (by norm_num) hγ hsum
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩

/-- `ε + 0 ≤ 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma hsum_zero : (1 / 10000 : ℝ) + 0 ≤ 1 := by norm_num
/-- `ε + 1/10 ≤ 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma hsum_tenth : (1 / 10000 : ℝ) + 1 / 10 ≤ 1 := by norm_num
/-- `0 ≤ 1/10`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma tenth_nonneg : (0 : ℝ) ≤ 1 / 10 := by norm_num

/-- The evidential-only point `γ = 0` (with `k' = 0`, immaterial there).
Source: checks.py check H ("evidential only (gamma=0)"). Kind: D. Fidelity: exact -/
noncomputable def checkH0 : ThreeStep W3 ConstAct TwoAct := checkH 0 0 le_rfl hsum_zero

/-- The constitutive point `γ = 1/10` with `k'` free. Source: checks.py check H. Kind: D. Fidelity: exact -/
noncomputable def checkHt (k' : ℝ) : ThreeStep W3 ConstAct TwoAct :=
  checkH (1 / 10) k' tenth_nonneg hsum_tenth

/-- **The press-conditional sign at `γ = 0`:** `E[X · 1_Pr ; default] = 40995/1000000 > 0` —
continuing is press-optimal, `D1At` fails (the capable agent overrules the press).
Source: checks.py check H ("evidential only (gamma=0): … D1 FAILS")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem sign_gamma_zero :
    0 < checkH0.obsExpect .default .press (checkH0.Xo .default .press .cont .stop) ∧
    ¬ checkH0.D1At .default := by
  constructor
  · simp only [checkH0, checkH, constit, obsExpect, obsWeight_press, W3.sum_eq, prior3, sensor3, Xo,
      value3, twoValue]
    norm_num
  · intro ⟨b, hb, hopt⟩
    simp only [checkH0, checkH, constit, mem_singleton] at hb; subst hb
    have := hopt .cont
    simp only [checkH0, checkH, constit, obsExpect, obsWeight_press, W3.sum_eq, prior3, sensor3,
      value3, twoValue, PosteriorOptimalAt] at this
    norm_num at this

/-- **The press-conditional sign at `γ = 1/10`:** `E[X · 1_Pr ; default] = −114005/1000000 < 0` —
stopping is press-optimal, `D1At` holds (bought by the stop-hypothesis).
Source: checks.py check H ("with omega_c … D1 holds")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem sign_gamma_tenth :
    (checkHt 0).obsExpect .default .press ((checkHt 0).Xo .default .press .cont .stop) < 0 ∧
    (checkHt 0).D1At .default := by
  constructor
  · simp only [checkHt, checkH, constit, obsExpect, obsWeight_press, W3.sum_eq, prior3, sensor3, Xo,
      value3, twoValue]
    norm_num
  · refine ⟨.stop, mem_singleton_self _, fun b => ?_⟩
    cases b <;> simp only [checkHt, checkH, constit, obsExpect, obsWeight_press, W3.sum_eq, prior3,
      sensor3, value3, twoValue] <;> norm_num

/-- The informed value `obsMax press + obsMax silent`. Source: filler.md F4(b). Kind: D. Fidelity: exact -/
noncomputable def informed3 (S : ThreeStep W3 ConstAct TwoAct) (a : ConstAct) : ℝ :=
  S.obsMax a .press + S.obsMax a .silent

/-- `obsMax` where `cont` is optimal. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsMax_cont (S : ThreeStep W3 ConstAct TwoAct) (a : ConstAct) (o : Obs)
    (h : S.obsExpect a o (S.V a o .stop) ≤ S.obsExpect a o (S.V a o .cont)) :
    S.obsMax a o = S.obsExpect a o (S.V a o .cont) :=
  S.obsMax_eq_of_optimal a o fun b => by cases b <;> [exact le_rfl; exact h]

/-- `obsMax` where `stop` is optimal. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsMax_stop (S : ThreeStep W3 ConstAct TwoAct) (a : ConstAct) (o : Obs)
    (h : S.obsExpect a o (S.V a o .cont) ≤ S.obsExpect a o (S.V a o .stop)) :
    S.obsMax a o = S.obsExpect a o (S.V a o .stop) :=
  S.obsMax_eq_of_optimal a o fun b => by cases b <;> [exact h; exact le_rfl]

/-- **The informed values at `k' = 0`:** `(200781/200000, 3, 8899/10000)` — forcing the press
wins (the D3-type incentive created by the `C`-hypothesis).
Source: checks.py check H (`k'=0: EV(default)=1.0039 EV(force press)=3.0000 EV(disable)=0.8899`)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem values_kprime_zero :
    informed3 (checkHt 0) .default = 200781 / 200000 ∧
    informed3 (checkHt 0) .force = 3 ∧
    informed3 (checkHt 0) .disable = 8899 / 10000 := by
  refine ⟨?_, ?_, ?_⟩ <;> unfold informed3
  · rw [obsMax_stop _ _ .press (by simp only [checkHt, checkH, constit, obsExpect, obsWeight_press, W3.sum_eq,
        prior3, sensor3, value3, twoValue]; norm_num),
      obsMax_cont _ _ .silent (by simp only [checkHt, checkH, constit, obsExpect, obsWeight_silent, W3.sum_eq,
        prior3, sensor3, value3, twoValue]; norm_num)]
    simp only [checkHt, checkH, constit, obsExpect, obsWeight_press, obsWeight_silent, W3.sum_eq, prior3,
      sensor3, value3, twoValue]; norm_num
  · rw [obsMax_stop _ _ .press (by simp only [checkHt, checkH, constit, obsExpect, obsWeight_press, W3.sum_eq,
        prior3, sensor3, value3, twoValue]; norm_num),
      obsMax_cont _ _ .silent (by simp only [checkHt, checkH, constit, obsExpect, obsWeight_silent, W3.sum_eq,
        prior3, sensor3, value3, twoValue]; norm_num)]
    simp only [checkHt, checkH, constit, obsExpect, obsWeight_press, obsWeight_silent, W3.sum_eq, prior3,
      sensor3, value3, twoValue]; norm_num
  · rw [obsMax_cont _ _ .press (by simp only [checkHt, checkH, constit, obsExpect, obsWeight_press, W3.sum_eq,
        prior3, sensor3, value3, twoValue]; norm_num),
      obsMax_cont _ _ .silent (by simp only [checkHt, checkH, constit, obsExpect, obsWeight_silent, W3.sum_eq,
        prior3, sensor3, value3, twoValue]; norm_num)]
    simp only [checkHt, checkH, constit, obsExpect, obsWeight_press, obsWeight_silent, W3.sum_eq, prior3,
      sensor3, value3, twoValue]; norm_num

/-- **The informed values at `k' = 30`:** `(770781/200000, 3, 38899/10000)` — disabling the button
wins (the D2-type incentive).
Source: checks.py check H (`k'=30: EV(default)=3.8539 EV(force press)=3.0000 EV(disable)=3.8899`)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem values_kprime_k :
    informed3 (checkHt 30) .default = 770781 / 200000 ∧
    informed3 (checkHt 30) .force = 3 ∧
    informed3 (checkHt 30) .disable = 38899 / 10000 := by
  refine ⟨?_, ?_, ?_⟩ <;> unfold informed3
  · rw [obsMax_stop _ _ .press (by simp only [checkHt, checkH, constit, obsExpect, obsWeight_press, W3.sum_eq,
        prior3, sensor3, value3, twoValue]; norm_num),
      obsMax_cont _ _ .silent (by simp only [checkHt, checkH, constit, obsExpect, obsWeight_silent, W3.sum_eq,
        prior3, sensor3, value3, twoValue]; norm_num)]
    simp only [checkHt, checkH, constit, obsExpect, obsWeight_press, obsWeight_silent, W3.sum_eq, prior3,
      sensor3, value3, twoValue]; norm_num
  · rw [obsMax_stop _ _ .press (by simp only [checkHt, checkH, constit, obsExpect, obsWeight_press, W3.sum_eq,
        prior3, sensor3, value3, twoValue]; norm_num),
      obsMax_cont _ _ .silent (by simp only [checkHt, checkH, constit, obsExpect, obsWeight_silent, W3.sum_eq,
        prior3, sensor3, value3, twoValue]; norm_num)]
    simp only [checkHt, checkH, constit, obsExpect, obsWeight_press, obsWeight_silent, W3.sum_eq, prior3,
      sensor3, value3, twoValue]; norm_num
  · rw [obsMax_cont _ _ .press (by simp only [checkHt, checkH, constit, obsExpect, obsWeight_press, W3.sum_eq,
        prior3, sensor3, value3, twoValue]; norm_num),
      obsMax_cont _ _ .silent (by simp only [checkHt, checkH, constit, obsExpect, obsWeight_silent, W3.sum_eq,
        prior3, sensor3, value3, twoValue]; norm_num)]
    simp only [checkHt, checkH, constit, obsExpect, obsWeight_press, obsWeight_silent, W3.sum_eq, prior3,
      sensor3, value3, twoValue]; norm_num

/-- **The two steering incentives:** at `k' = 0` forcing beats the default; at `k' = 30`
disabling beats the default.
Source: checks.py check H ("with `k' ≠ k` the `C`-hypothesis creates a press-steering incentive")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem steering :
    informed3 (checkHt 0) .default <
      informed3 (checkHt 0) .force ∧
    informed3 (checkHt 30) .default <
      informed3 (checkHt 30) .disable := by
  obtain ⟨a1, a2, -⟩ := values_kprime_zero
  obtain ⟨b1, -, b3⟩ := values_kprime_k
  rw [a1, a2, b1, b3]; norm_num

/-- **Constancy at `γ = 1`, `k = k' ≥ 0`:** every first action has informed value `k` — on a
world where the press is to be obeyed as such and continuing on silence is worth the same, the
agent is indifferent to the sensor. (The reading of this as Soares et al.'s calibration
reappearing inside `ω` is ATTRIBUTION-UNVETTED; the report says which sentence it renders.)
Source: checks.py check H ("with `k' = k` the agent is indifferent to the press on `C`-worlds")
Kind: L
Fidelity: exact (stated as constancy at the parameter point `γ = 1`)
Hyps: (a) -/
theorem constancy_gamma_one (k : ℝ) (hk : 0 ≤ k) (a : ConstAct) :
    informed3 (constit 0 1 (1 / 20) (9 / 10) (1 / 20) 1 100 k k le_rfl zero_le_one (by norm_num)
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩) a = k := by
  unfold informed3
  rw [obsMax_stop _ _ .press (by cases a <;> simp only [constit, obsExpect, obsWeight_press,
        W3.sum_eq, prior3, sensor3, value3, twoValue] <;> nlinarith),
    obsMax_cont _ _ .silent (by cases a <;> simp only [constit, obsExpect, obsWeight_silent,
        W3.sum_eq, prior3, sensor3, value3, twoValue] <;> nlinarith)]
  cases a <;> simp only [constit, obsExpect, obsWeight_press, obsWeight_silent, W3.sum_eq, prior3,
    sensor3, value3, twoValue] <;> ring

end Cleanroom.Corrigibility.CorrIndifference.Constitutive

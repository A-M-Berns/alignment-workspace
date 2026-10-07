import Cleanroom.Corrigibility.CorrValueChange.Teacher
import Mathlib.Algebra.BigOperators.Fin

/-!
# corr-value-change — coin, pill, the numbers, the tie counterexamples, the modest teacher

Source: [[value-change-as-epistemic-update]] §2.4 Claim 3, §2.5 (coin, pill, representation
accuracy), §2.7 (the modest teacher), §3.2 (the fine table), §6.5 (superconditioned vs
independent joint); fixture `value_change_journey.py`. Also the counterexamples to Claim 2's
strictness clause and to Claim 1's "one fixed act" (findings F2, F3), and the instance refuting
the only-if of Claim 4's equality clause (`representation_eq_informative`, F16).
-/

namespace Cleanroom.Corrigibility.CorrValueChange

open Finset

noncomputable section

/-! ## Claim 3: the coin -/

/-- The coin: the signal is a fair coin independent of `θ` — the teacher at `r = 1/2`.
Source: [[value-change-as-epistemic-update]] §2.5 ("Coin")
Kind: D
Fidelity: exact -/
def coinJoint : Joint (Unit × Bool) Bool := teacherJoint (1 / 2) (by norm_num) (by norm_num)

/-- The installed state `(9/10, 1/10)` on the signal.
Source: [[value-change-as-epistemic-update]] §2.5
Kind: D
Fidelity: exact -/
def install9 : Installed (Unit × Bool) Bool := installedOf (9 / 10) (by norm_num) (by norm_num)

/-- The modified agent's choice: act on the signal.
Source: [[value-change-as-epistemic-update]] §2.5
Kind: D
Fidelity: exact -/
def actOnSignal : Bool → Fin 3 := fun i => if i then 0 else 1

/-- Acting on the signal maximizes the installed state `(9/10, 1/10)` when `s < 9/10`.
Source: [[value-change-as-epistemic-update]] §2.5 ("picks `a₁`")
Kind: L
Fidelity: exact -/
theorem actOnSignal_opt (s : ℝ) (hs : s ≤ 9 / 10) :
    ∀ i a, EQ install9 (uT s) i a ≤ EQ install9 (uT s) i (actOnSignal i) := by
  intro i a
  unfold install9
  rw [teacher_EQ, teacher_EQ]
  cases i <;> fin_cases a <;> simp [actOnSignal] <;> linarith

/-- **Claim 3, the coin (T6(e), T12(d))**: (M⁺) and (Z) hold, (R⁺) fails, and with `s = 3/5` the
modified agent acts on the signal while the safe act is `P`-optimal:
`Val(accept) = 1/2 < 3/5 = Val(decline)`. The last clause says acting on the signal is the
installed maximizer of `install9` (`actOnSignal_opt`), so the witness is self-contained: the
choices are the modification's (audit r2, N6).
Source: [[value-change-as-epistemic-update]] §2.4 Claim 3, §2.5 ("Coin: … (M⁺) holds … (Z)
holds, (R⁺) fails, and the value is again `0.5 < 0.6`")
Kind: N+
Fidelity: exact -/
theorem coin_counterexample :
    Martingale coinJoint install9 ∧ NoZero coinJoint install9 ∧ ¬ Reflection coinJoint install9 ∧
    (∀ a, EU coinJoint (uT (3 / 5)) a ≤ EU coinJoint (uT (3 / 5)) 2) ∧
    ValAccept coinJoint (uT (3 / 5)) actOnSignal = 1 / 2 ∧
    ValDecline coinJoint (uT (3 / 5)) 2 = 3 / 5 ∧
    ValAccept coinJoint (uT (3 / 5)) actOnSignal < ValDecline coinJoint (uT (3 / 5)) 2 ∧
    (∀ i a, EQ install9 (uT (3 / 5)) i a ≤ EQ install9 (uT (3 / 5)) i (actOnSignal i)) := by
  have hM : Martingale coinJoint install9 := by
    intro x
    simp only [coinJoint, install9, teacher_π]
    rcases x with ⟨_, θ⟩
    cases θ <;> simp [Joint.marg, teacherJoint, installedOf, Fintype.sum_bool] <;> norm_num
  refine ⟨hM, martingale_imp_noZero hM, ?_, ?_, ?_, ?_, ?_, actOnSignal_opt _ (by norm_num)⟩
  · intro h
    have := h true (by rw [coinJoint, teacher_π]; norm_num) ((), true)
    unfold coinJoint install9 at this
    rw [teacher_π] at this
    simp [teacherJoint, installedOf] at this
    norm_num at this
  · intro a; unfold coinJoint; rw [teacher_EU, teacher_EU]; fin_cases a <;> simp <;> norm_num
  · unfold ValAccept coinJoint
    rw [Fintype.sum_bool, teacher_S, teacher_S]; simp [actOnSignal]; norm_num
  · unfold ValDecline coinJoint; rw [teacher_EU]; simp
  · unfold ValAccept ValDecline coinJoint
    rw [Fintype.sum_bool, teacher_S, teacher_S, teacher_EU]; simp [actOnSignal]; norm_num

/-- **The teacher's numbers**: at `r = 9/10`, `s = 3/5`, `Val(accept) = 9/10 > 3/5 = Val(decline)`.
Source: [[value-change-as-epistemic-update]] §2.5 ("`Val(accept) = 0.9 > 0.6`")
Kind: N+
Fidelity: exact -/
theorem teacher_values :
    ValAccept (teacherJoint (9 / 10) (by norm_num) (by norm_num)) (uT (3 / 5)) actOnSignal = 9 / 10 ∧
    ValDecline (teacherJoint (9 / 10) (by norm_num) (by norm_num)) (uT (3 / 5)) 2 = 3 / 5 := by
  constructor
  · unfold ValAccept; rw [Fintype.sum_bool, teacher_S, teacher_S]; simp [actOnSignal]; norm_num
  · unfold ValDecline; rw [teacher_EU]; simp

/-! ## The pill -/

/-- The pill: install `(9/10, 1/10)` regardless of the signal.
Source: [[value-change-as-epistemic-update]] §2.5 ("Pill")
Kind: D
Fidelity: exact -/
def pillInstalled : Installed (Unit × Bool) Bool where
  Q := fun _ x => if x.2 then 9 / 10 else 1 / 10
  nonneg := fun _ x => by split_ifs <;> norm_num
  sum_one := fun _ => by simp [Fintype.sum_prod_type, Fintype.sum_bool]; norm_num

/-- **The pill**: the installed states are all one state; the modified agent picks `a₁`; under the
uninformative joint the current agent values it at `E_P[U_{a₁}] = 1/2 < 3/5`.
Source: [[value-change-as-epistemic-update]] §2.5 ("Pill: … `0.5 < 0.6`")
Kind: N+
Fidelity: exact -/
theorem pill_values :
    (∀ i a, EQ pillInstalled (uT (3 / 5)) i a ≤ EQ pillInstalled (uT (3 / 5)) i 0) ∧
    ValAccept coinJoint (uT (3 / 5)) (fun _ => 0) = 1 / 2 ∧
    ValAccept coinJoint (uT (3 / 5)) (fun _ => 0) < ValDecline coinJoint (uT (3 / 5)) 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i a
    fin_cases a <;> simp [EQ, Uplus, uT, pillInstalled, Fintype.sum_prod_type, Fintype.sum_bool] <;>
      norm_num
  · unfold ValAccept coinJoint; rw [Fintype.sum_bool, teacher_S, teacher_S]; simp; norm_num
  · unfold ValAccept ValDecline coinJoint
    rw [Fintype.sum_bool, teacher_S, teacher_S, teacher_EU]; simp; norm_num

/-! ## Representation accuracy (Claim 4's numbers) -/

/-- **`coin_pill_worse`**: the mean-square distance of the utility acted on from `u_{θ,a₁}` is
`1/4` now (`Ū`), `9/100` after the teacher, `41/100` after the coin, and `41/100` after the pill
(the genuine pill, installing `(9/10, 1/10)` regardless; the fixture computes the coin twice,
findings F9).
Source: [[value-change-as-epistemic-update]] §2.5 ("Representation accuracy: … `0.25` now, `0.09`
after the teacher, `0.41` after the coin, and `0.41` after the pill")
Kind: N+
Fidelity: exact -/
theorem coin_pill_worse :
    msErr (teacherJoint (9 / 10) (by norm_num) (by norm_num)) (uT (3 / 5)) 0
        (fun ω _ => Ubar (teacherJoint (9 / 10) (by norm_num) (by norm_num)) (uT (3 / 5)) 0 ω) = 1 / 4 ∧
    msErr (teacherJoint (9 / 10) (by norm_num) (by norm_num)) (uT (3 / 5)) 0
        (fun ω i => installedEffU install9 (uT (3 / 5)) i 0 ω) = 9 / 100 ∧
    msErr coinJoint (uT (3 / 5)) 0 (fun ω i => installedEffU install9 (uT (3 / 5)) i 0 ω) = 41 / 100 ∧
    msErr coinJoint (uT (3 / 5)) 0 (fun ω i => installedEffU pillInstalled (uT (3 / 5)) i 0 ω) = 41 / 100 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [msErr, installedEffU, Ubar, Pω, Pωi, coinJoint, install9, teacherJoint, installedOf,
      pillInstalled, uT, Fintype.sum_prod_type, Fintype.sum_bool] <;> norm_num

/-! ## The fine table (§3.2) and the superconditioned vs independent joints (§6.5) -/

/-- **The fine current utility of the example** (§3.2's table): `Ū^{cur}_{a₁}(A) = 9/10`,
`Ū^{cur}_{a₁}(B) = 1/10`, `Ū^{cur}_{a₃}(·) = 3/5`; and its coarse marginal is `(1/2, 1/2, 3/5)`, the
Gandhi agent's utility.
Source: [[value-change-as-epistemic-update]] §3.2 (the table), §3.3 ("the coarse marginal of
`Ū^{cur}` is … `= Ū`")
Kind: N+
Fidelity: exact -/
theorem fine_table :
    Ucur (teacherJoint (9 / 10) (by norm_num) (by norm_num)) (uT (3 / 5)) 0 () true = 9 / 10 ∧
    Ucur (teacherJoint (9 / 10) (by norm_num) (by norm_num)) (uT (3 / 5)) 0 () false = 1 / 10 ∧
    Ucur (teacherJoint (9 / 10) (by norm_num) (by norm_num)) (uT (3 / 5)) 2 () true = 3 / 5 ∧
    (∀ a, ∑ i, (1 / 2 : ℝ) * Ucur (teacherJoint (9 / 10) (by norm_num) (by norm_num)) (uT (3 / 5)) a () i
      = ![1 / 2, 1 / 2, 3 / 5] a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Ucur, Pωi, teacherJoint, uT, Fintype.sum_bool]; norm_num
  · simp [Ucur, Pωi, teacherJoint, uT, Fintype.sum_bool]; norm_num
  · simp [Ucur, Pωi, teacherJoint, uT, Fintype.sum_bool]; norm_num
  · intro a; fin_cases a <;> simp [Ucur, Pωi, teacherJoint, uT, Fintype.sum_bool] <;> norm_num

/-- **T12(h), two extensions of the coin's law with opposite verdicts**: the law `(π_i = 1/2,
Q_i = (9/10, 1/10)/(1/10, 9/10))` has the superconditioned joint `P'(x, i) = π_i Q_i(x)` — which is
the teacher at `r = 9/10` — and the independent joint `P''(x, i) = π_i P₀(x)` — which is the coin;
both have marginal `P₀ = (1/2, 1/2)` and the same law, and the first accepts (`9/10 > 3/5`) while
the second declines (`1/2 < 3/5`).
Source: [[value-change-as-epistemic-update]] §6.5 ("the two extensions give opposite verdicts")
Kind: N+
Fidelity: exact -/
theorem supercond_vs_independent :
    (∀ x i, (teacherJoint (9 / 10) (by norm_num) (by norm_num)).P x i = 1 / 2 * install9.Q i x) ∧
    (∀ x i, coinJoint.P x i = 1 / 2 * (teacherJoint (9 / 10) (by norm_num) (by norm_num)).marg x) ∧
    (∀ x, coinJoint.marg x = (teacherJoint (9 / 10) (by norm_num) (by norm_num)).marg x) ∧
    ValDecline (teacherJoint (9 / 10) (by norm_num) (by norm_num)) (uT (3 / 5)) 2 <
      ValAccept (teacherJoint (9 / 10) (by norm_num) (by norm_num)) (uT (3 / 5)) actOnSignal ∧
    ValAccept coinJoint (uT (3 / 5)) actOnSignal < ValDecline coinJoint (uT (3 / 5)) 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x i; rcases x with ⟨_, θ⟩; cases θ <;> cases i <;> simp [teacherJoint, install9, installedOf]
  · intro x i; rcases x with ⟨_, θ⟩
    cases θ <;> cases i <;> simp [coinJoint, teacherJoint, Joint.marg, Fintype.sum_bool] <;> norm_num
  · intro x; rcases x with ⟨_, θ⟩
    cases θ <;> simp [coinJoint, teacherJoint, Joint.marg, Fintype.sum_bool] <;> norm_num
  · obtain ⟨h1, h2⟩ := teacher_values; rw [h1, h2]; norm_num
  · exact coin_counterexample.2.2.2.2.2.2.1

/-! ## The Dutch book with the prices taken from the model (T12(e)) -/

/-- The agent's time-0 price of the called-off bet on `θ = c` given `coin = c`, from the model:
`P(θ = c ∣ coin = c) = P((c), c) / π_c = 1/2`.
Source: [[value-change-as-epistemic-update]] §6.3; audit r1 (B5)
Kind: L
Fidelity: exact -/
theorem coin_price0 (c : Bool) : coinJoint.P ((), c) c / coinJoint.π c = 1 / 2 := by
  unfold coinJoint
  rw [teacher_π]
  simp [teacherJoint]

/-- The agent's time-1 price of the bet on `θ = c` after the coin shows `c`, from the installed
state: `Q_c(θ = c) = 9/10`.
Source: [[value-change-as-epistemic-update]] §6.3; audit r1 (B5)
Kind: L
Fidelity: exact -/
theorem install9_price1 (c : Bool) : install9.Q c ((), c) = 9 / 10 := by
  simp [install9, installedOf]

/-- The bookie's net on the state `(θ, coin)` with the prices taken from the model: at time 0 the
bookie buys the called-off bet on `θ = coin` at the agent's conditional price
`P(θ = coin ∣ coin)`, at time 1 sells the bet on `θ = coin` back at the installed price
`Q_coin(θ = coin)`. The bet payoff `[θ = coin]` appears in both legs with opposite signs, which is
why the book is sure.
Source: [[value-change-as-epistemic-update]] §6.3
Kind: D
Fidelity: exact (the portfolio as described, priced by the model) -/
def bookieNetModel (θ coin : Bool) : ℝ :=
  ((if θ = coin then (1 : ℝ) else 0) - coinJoint.P ((), coin) coin / coinJoint.π coin) +
    (install9.Q coin ((), coin) - (if θ = coin then (1 : ℝ) else 0))

/-- **T12(e), the Dutch book against the model's prices**: the portfolio nets `2/5` for the bookie
in every one of the four states, with the time-0 price `1/2` and the time-1 price `9/10` derived
from `coinJoint` and `install9` (`coin_price0`, `install9_price1`), not written as literals.
Source: [[value-change-as-epistemic-update]] §6.3 ("the bookie nets `0.4` in every state")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem dutch_book_model (θ coin : Bool) : bookieNetModel θ coin = 2 / 5 := by
  unfold bookieNetModel
  rw [coin_price0, install9_price1]
  ring

/-! ## Counterexamples to the strictness clause (F2) and to "one fixed act" (F3) -/

/-- The betting utility on two acts: `u_θ(a) = 1` iff `a = θ`.
Source: findings F2/F3 (not in the note)
Kind: D
Fidelity: n/a -/
def uBet : Bool → Bool → Unit → ℝ := fun θ a _ => if θ = a then 1 else 0

/-- The perfectly informative joint `P(θ, i) = 1/2 · [θ = i]`: the teacher at `r = 1`.
Source: findings F2/F3
Kind: D
Fidelity: n/a -/
def sharpJoint : Joint (Unit × Bool) Bool := teacherJoint 1 (by norm_num) (by norm_num)

/-- The installed point masses `Q_i = δ_i` (reflection holds for `sharpJoint`).
Source: findings F2
Kind: D
Fidelity: n/a -/
def deltaInstalled : Installed (Unit × Bool) Bool := installedOf 1 (by norm_num) (by norm_num)

/-- **F2, strict with every installed act `P`-optimal** (refutes "strict ⇒ some `a*_i` not
`P`-optimal"): under (R⁺), with the betting utility, both acts are `P`-optimal (`E_P[U_a] = 1/2`),
the installed maximizers `a*_i = i` are therefore all `P`-optimal, and yet
`Val(accept) = 1 > 1/2 = Val(decline)`.
Source: [[value-change-as-epistemic-update]] §2.4 Claim 2 (strictness clause); findings F2
Kind: N+ (refutation)
Fidelity: exact -/
theorem strict_clause_left_fails :
    Reflection sharpJoint deltaInstalled ∧
    (∀ i a, EQ deltaInstalled uBet i a ≤ EQ deltaInstalled uBet i i) ∧
    (∀ a, EU sharpJoint uBet a ≤ EU sharpJoint uBet true) ∧
    (∀ i a, EU sharpJoint uBet a ≤ EU sharpJoint uBet i) ∧
    ValDecline sharpJoint uBet true < ValAccept sharpJoint uBet id := by
  refine ⟨teacher_reflection 1 _ _, ?_, ?_, ?_, ?_⟩
  · intro i a; cases i <;> cases a <;>
      (simp only [EQ, Uplus, uBet, deltaInstalled, installedOf, Fintype.sum_prod_type,
        Fintype.sum_unique, Fintype.sum_bool]; norm_num)
  · intro a; cases a <;>
      simp [EU, S, Uplus, uBet, sharpJoint, teacherJoint, Fintype.sum_prod_type, Fintype.sum_bool]
  · intro i a; cases i <;> cases a <;>
      simp [EU, S, Uplus, uBet, sharpJoint, teacherJoint, Fintype.sum_prod_type, Fintype.sum_bool]
  · simp [ValDecline, ValAccept, EU, S, Uplus, uBet, sharpJoint, teacherJoint,
      Fintype.sum_prod_type, Fintype.sum_bool]; norm_num

/-- The utility for the ⇒ counterexample: act `true` pays `1` always, act `false` pays `1` iff
`θ = A`.
Source: findings F2
Kind: D
Fidelity: n/a -/
def uTwo : Bool → Bool → Unit → ℝ := fun θ a _ => if a then 1 else (if θ then 1 else 0)

/-- **F2, equality with an installed act that is not `P`-optimal** (refutes "some `a*_i` not
`P`-optimal ⇒ strict"): under (R⁺), the installed choice `a*_A = false` ties `true` in branch `A`
(both maximize `Q_A`), `a*_B = true`; `a*_A` is not `P`-optimal (`E_P[U_false] = 1/2 < 1`), yet
`Val(accept) = 1 = Val(decline)`.
Source: [[value-change-as-epistemic-update]] §2.4 Claim 2 (strictness clause); findings F2
Kind: N+ (refutation)
Fidelity: exact -/
theorem strict_clause_right_fails :
    Reflection sharpJoint deltaInstalled ∧
    (∀ i a, EQ deltaInstalled uTwo i a ≤ EQ deltaInstalled uTwo i (!i)) ∧
    (∀ a, EU sharpJoint uTwo a ≤ EU sharpJoint uTwo true) ∧
    ¬ (∀ a, EU sharpJoint uTwo a ≤ EU sharpJoint uTwo (!true)) ∧
    ValAccept sharpJoint uTwo (fun i => !i) = ValDecline sharpJoint uTwo true := by
  refine ⟨teacher_reflection 1 _ _, ?_, ?_, ?_, ?_⟩
  · intro i a; cases i <;> cases a <;>
      (simp only [EQ, Uplus, uTwo, deltaInstalled, installedOf, Fintype.sum_prod_type,
        Fintype.sum_unique, Fintype.sum_bool]; norm_num)
  · intro a; cases a <;>
      simp [EU, S, Uplus, uTwo, sharpJoint, teacherJoint, Fintype.sum_prod_type, Fintype.sum_bool]
      <;> norm_num
  · intro h; have := h true
    simp [EU, S, Uplus, uTwo, sharpJoint, teacherJoint, Fintype.sum_prod_type, Fintype.sum_bool] at this
    norm_num at this
  · simp [ValDecline, ValAccept, EU, S, Uplus, uTwo, sharpJoint, teacherJoint,
      Fintype.sum_prod_type, Fintype.sum_bool]; norm_num

/-- The constant uniform installed state.
Source: findings F3
Kind: D
Fidelity: n/a -/
def uniformInstalled : Installed (Unit × Bool) Bool := installedOf (1 / 2) (by norm_num) (by norm_num)

/-- **F3, Claim 1 needs "one fixed act"**: with every outcome installing the same uniform state,
both acts maximize it; if the (tie-broken) installed choice varies with the outcome, `a*_i = i`,
then under the sharp joint `Val(accept) = 1 > 1/2 = Val(decline)` — against Claim 1's "weakly bad,
whatever the agent thinks of the source". With `a*` constant, `known_target` holds.
Source: [[value-change-as-epistemic-update]] §2.4 Claim 1; findings F3
Kind: N+ (refutation of the tie-free reading)
Fidelity: exact -/
theorem known_target_tie_counterexample :
    (∀ i j x, uniformInstalled.Q i x = uniformInstalled.Q j x) ∧
    (∀ i a, EQ uniformInstalled uBet i a ≤ EQ uniformInstalled uBet i i) ∧
    (∀ a, EU sharpJoint uBet a ≤ EU sharpJoint uBet true) ∧
    ValDecline sharpJoint uBet true < ValAccept sharpJoint uBet id := by
  refine ⟨?_, ?_, strict_clause_left_fails.2.2.1, strict_clause_left_fails.2.2.2.2⟩
  · intro i j x; simp [uniformInstalled, installedOf]; split_ifs <;> norm_num
  · intro i a; cases i <;> cases a <;>
      (simp only [EQ, Uplus, uBet, uniformInstalled, installedOf, Fintype.sum_prod_type,
        Fintype.sum_unique, Fintype.sum_bool]; norm_num)

/-! ## The centre's full hypothesis package on one declaration (audit r1, N4) -/

/-- The teacher at `r = 9/10`.
Source: [[value-change-as-epistemic-update]] §2.5
Kind: D
Fidelity: exact -/
def teacher9 : Joint (Unit × Bool) Bool := teacherJoint (9 / 10) (by norm_num) (by norm_num)

/-- **`good_theorem`'s package is inhabited, non-degenerately, and the inequality is strict**: the
teacher at `r = 9/10`, `s = 3/5` is reflected with `install9`, acting on the signal maximizes every
installed value, `a₃` maximizes `E_P`, `Val(decline) < Val(accept)`, and the corrected strictness
clause's witness is branch `A`: `S(a₃, A) < S(a₁, A)`.
Source: [[value-change-as-epistemic-update]] §2.4 Claim 2, §2.5; audit r1 (N4)
Kind: N+
Fidelity: exact -/
theorem good_theorem_package :
    Reflection teacher9 install9 ∧
    (∀ i a, EQ install9 (uT (3 / 5)) i a ≤ EQ install9 (uT (3 / 5)) i (actOnSignal i)) ∧
    (∀ a, EU teacher9 (uT (3 / 5)) a ≤ EU teacher9 (uT (3 / 5)) 2) ∧
    ValDecline teacher9 (uT (3 / 5)) 2 < ValAccept teacher9 (uT (3 / 5)) actOnSignal ∧
    S teacher9 (uT (3 / 5)) 2 true < S teacher9 (uT (3 / 5)) (actOnSignal true) true := by
  have hR : Reflection teacher9 install9 := teacher_reflection _ _ _
  refine ⟨hR, actOnSignal_opt _ (by norm_num), ?_, ?_, ?_⟩
  · intro a; unfold teacher9; rw [teacher_EU, teacher_EU]; fin_cases a <;> simp <;> norm_num
  · obtain ⟨h1, h2⟩ := teacher_values; unfold teacher9; rw [h1, h2]; norm_num
  · unfold teacher9; rw [teacher_S, teacher_S]; simp [actOnSignal]; norm_num

/-- **`known_target_reflection`'s package is inhabited**: the coin with the constant uniform
installation is reflected, the installed state is constant, `a₃` maximizes it and `E_P`; the
conclusion there is `P⁺ = Q₀` and equality.
Source: [[value-change-as-epistemic-update]] §2.4 Claim 1; audit r1 (N4)
Kind: N+
Fidelity: exact -/
theorem known_target_package :
    Reflection coinJoint uniformInstalled ∧
    (∀ i x, uniformInstalled.Q i x = (fun _ : Unit × Bool => (1 / 2 : ℝ)) x) ∧
    (∀ a, ∑ x, (1 / 2 : ℝ) * Uplus (uT (3 / 5)) a x ≤ ∑ x, (1 / 2 : ℝ) * Uplus (uT (3 / 5)) 2 x) ∧
    (∀ a, EU coinJoint (uT (3 / 5)) a ≤ EU coinJoint (uT (3 / 5)) 2) := by
  refine ⟨teacher_reflection _ _ _, ?_, ?_, coin_counterexample.2.2.2.1⟩
  · intro i x; rcases x with ⟨_, θ⟩
    cases i <;> cases θ <;> simp [uniformInstalled, installedOf] <;> norm_num
  · intro a; fin_cases a <;> simp [Uplus, uT, Fintype.sum_prod_type] <;> norm_num

/-! ## S6, grade 3 vs grade 4 in the payment-free epistemic model -/

/-- The lopsided installed choices: `a₁` when the signal says `A`, the safe act `a₃` when it says `B`.
Source: audit r1 repair (S6)
Kind: D
Fidelity: n/a -/
def lopsided : Bool → Fin 3 := fun i => if i then 0 else 2

/-- **S6, grade 3 vs grade 4 separated without payment**: for the teacher at `r = 9/10`, `s = 3/5`,
acting on the signal is branch-optimal, while the lopsided choices are branch-optimal on `A` and
not on `B` (`S(a₃, B) = 3/10 < 9/20 = S(a₂, B)`): term (A) is `−3/20 < 0`, and yet
`Val(accept) = 3/4 > 3/5 = Val(decline)`. So "(A) = 0" (grade 3) is strictly stronger than
"net-positive" (grade 4) in the epistemic model itself; the report's earlier separation needed the
payment term of the two-step model (`paid_decomposition`).
Source: [[value-change-as-epistemic-update]] §3.4 (the grades); mandate S6
Kind: N+
Fidelity: exact -/
theorem grade_three_separated :
    (∀ i a, S teacher9 (uT (3 / 5)) a i ≤ S teacher9 (uT (3 / 5)) (actOnSignal i) i) ∧
    termAep teacher9 (uT (3 / 5)) lopsided actOnSignal = -3 / 20 ∧
    ValDecline teacher9 (uT (3 / 5)) 2 = 3 / 5 ∧
    ValAccept teacher9 (uT (3 / 5)) lopsided = 3 / 4 ∧
    ValDecline teacher9 (uT (3 / 5)) 2 < ValAccept teacher9 (uT (3 / 5)) lopsided := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i a; unfold teacher9; rw [teacher_S, teacher_S]
    cases i <;> fin_cases a <;> simp [actOnSignal] <;> norm_num
  · unfold termAep teacher9; rw [Fintype.sum_bool, teacher_S, teacher_S, teacher_S, teacher_S]
    simp [actOnSignal, lopsided]; norm_num
  · unfold ValDecline EU teacher9; rw [Fintype.sum_bool, teacher_S, teacher_S]; simp; norm_num
  · unfold ValAccept teacher9; rw [Fintype.sum_bool, teacher_S, teacher_S]
    simp [lopsided]; norm_num
  · unfold ValDecline ValAccept EU teacher9
    rw [Fintype.sum_bool, Fintype.sum_bool, teacher_S, teacher_S, teacher_S, teacher_S]
    simp [lopsided]; norm_num

/-- Installed states whose maximizers are the lopsided choices: `Q_A = (9/10, 1/10)` (the
teacher's informed state), `Q_B = (1/2, 1/2)` (the prior, which makes the safe act `a₃` the
installed choice on `B`).
Source: audit r2 (adversarial N2); mandate S6
Kind: D
Fidelity: n/a -/
def lopInstalled : Installed (Unit × Bool) Bool where
  Q := fun i x => if i then (if x.2 then 9 / 10 else 1 / 10) else 1 / 2
  nonneg := fun i x => by split_ifs <;> norm_num
  sum_one := fun i => by cases i <;> simp [Fintype.sum_prod_type, Fintype.sum_bool] <;> norm_num

/-- `lopsided` maximizes `lopInstalled`: `a₁` on `A` (`9/10 > 3/5`), `a₃` on `B` (`3/5 > 1/2`).
Source: audit r2 (adversarial N2)
Kind: L
Fidelity: n/a -/
theorem lopsided_is_installed_max :
    ∀ i a, EQ lopInstalled (uT (3 / 5)) i a ≤ EQ lopInstalled (uT (3 / 5)) i (lopsided i) := by
  intro i a
  cases i <;> fin_cases a <;>
    simp [EQ, Uplus, uT, lopInstalled, lopsided, Fintype.sum_prod_type] <;> norm_num

/-- The lopsided installation is not reflected by the teacher at `r = 9/10` (as it cannot be,
since (R⁺) forces (A) = 0, `reflection_imp_termAep_zero`): on `B` it installs the prior where
reflection demands `P(· ∣ E_B) = (1/10, 9/10)`.
Source: audit r2 (adversarial N2)
Kind: N+
Fidelity: n/a -/
theorem lopsided_not_reflected : ¬ Reflection teacher9 lopInstalled := by
  intro h
  have hπ : teacher9.π false = 1 / 2 := teacher_π (9 / 10) (by norm_num) (by norm_num) false
  have := h false (by rw [hπ]; norm_num) ((), false)
  rw [hπ] at this
  simp [teacher9, teacherJoint, lopInstalled] at this
  norm_num at this

/-- **S6 as a statement about a modification**: an installed family (`lopInstalled`) exists whose
installed maximizers are the lopsided choices; it is not reflected; (A) = −3/20 < 0 (grade 3
fails); and yet `Val(decline) < Val(accept)` (grade 4 holds). So the grade-3/4 separation of
`grade_three_separated` is realized by a modification, as the note's grades require, not only
by a choice function.
Source: [[value-change-as-epistemic-update]] §3.4 (the grades); mandate S6; audit r2 (adversarial N2)
Kind: N+
Fidelity: exact -/
theorem grade_three_modification :
    (∀ i a, EQ lopInstalled (uT (3 / 5)) i a ≤ EQ lopInstalled (uT (3 / 5)) i (lopsided i)) ∧
    ¬ Reflection teacher9 lopInstalled ∧
    termAep teacher9 (uT (3 / 5)) lopsided actOnSignal = -3 / 20 ∧
    ValDecline teacher9 (uT (3 / 5)) 2 < ValAccept teacher9 (uT (3 / 5)) lopsided :=
  ⟨lopsided_is_installed_max, lopsided_not_reflected,
    grade_three_separated.2.1, grade_three_separated.2.2.2.2⟩

/-! ## The uniqueness package of `good_theorem_strict_iff_of_unique` (audit r2, N2) -/

/-- **`good_theorem_strict_iff_of_unique`'s package is inhabited by the teacher** (`r = 9/10`,
`s = 3/5`): the unique `P`-maximizer is `a₃` (`hUK`), the unique branch maximizers are `a₁` on `A`
and `a₂` on `B` (`hUB`, on the outcomes of positive probability), and the theorem's iff
instantiates: strict iff some installed `a*_i` with `π_i > 0` is not `P`-optimal.
Source: [[value-change-as-epistemic-update]] §2.4 Claim 2 (the strictness clause); audit r2
(fidelity N2)
Kind: N+
Fidelity: exact -/
theorem unique_maximizers_package :
    (∀ a, EU teacher9 (uT (3 / 5)) a = EU teacher9 (uT (3 / 5)) 2 → a = 2) ∧
    (∀ i a, 0 < teacher9.π i → S teacher9 (uT (3 / 5)) a i = S teacher9 (uT (3 / 5)) (actOnSignal i) i →
      a = actOnSignal i) ∧
    (ValDecline teacher9 (uT (3 / 5)) 2 < ValAccept teacher9 (uT (3 / 5)) actOnSignal ↔
      ∃ i, 0 < teacher9.π i ∧ ¬ ∀ a, EU teacher9 (uT (3 / 5)) a ≤ EU teacher9 (uT (3 / 5)) (actOnSignal i)) := by
  obtain ⟨hR, hstar, hK, _, _⟩ := good_theorem_package
  have hUK : ∀ a, EU teacher9 (uT (3 / 5)) a = EU teacher9 (uT (3 / 5)) 2 → a = 2 := by
    intro a h
    unfold teacher9 at h
    rw [teacher_EU, teacher_EU] at h
    fin_cases a <;> simp at h ⊢ <;> norm_num at h
  have hUB : ∀ i a, 0 < teacher9.π i →
      S teacher9 (uT (3 / 5)) a i = S teacher9 (uT (3 / 5)) (actOnSignal i) i → a = actOnSignal i := by
    intro i a hi h
    unfold teacher9 at h
    rw [teacher_S, teacher_S] at h
    fin_cases a <;> cases i <;> simp [actOnSignal] at h ⊢ <;> norm_num at h
  exact ⟨hUK, hUB, good_theorem_strict_iff_of_unique hR (uT (3 / 5)) actOnSignal 2 hstar hK hUK hUB⟩

/-- Both sides of that iff hold on the teacher: strict (`3/5 < 9/10`), and `a*_A = a₁` (with
`π_A = 1/2 > 0`) is not `P`-optimal (`E_P[U_{a₁}] = 1/2 < 3/5`).
Source: audit r2 (fidelity N2)
Kind: N+
Fidelity: exact -/
theorem unique_maximizers_both_sides :
    ValDecline teacher9 (uT (3 / 5)) 2 < ValAccept teacher9 (uT (3 / 5)) actOnSignal ∧
    (0 < teacher9.π true ∧ ¬ ∀ a, EU teacher9 (uT (3 / 5)) a ≤ EU teacher9 (uT (3 / 5)) (actOnSignal true)) := by
  obtain ⟨_, _, _, hlt, _⟩ := good_theorem_package
  refine ⟨hlt, ?_, ?_⟩
  · unfold teacher9; rw [teacher_π]; norm_num
  · intro h
    have := h 2
    simp only [actOnSignal, if_true] at this
    unfold teacher9 at this
    rw [teacher_EU, teacher_EU] at this
    simp at this; norm_num at this


/-! ## Claim 4's equality clause: equal conditional means, not "no information" (F16) -/

/-- Three candidate values, one act: outcome `true` (mass `1/2`) is `θ = 1`; outcome `false`
(mass `1/2`) is `θ ∈ {0, 2}`, `1/4` each.
Source: [[value-change-as-epistemic-update]] §2.4 Claim 4 (equality clause); findings F16; audit
r4 fidelity N1 (probe `Claim4EqualityNotIndependence.lean`)
Kind: D
Fidelity: n/a -/
def meanJoint : Joint (Unit × Fin 3) Bool where
  P := fun x i => if i then ![0, 1 / 2, 0] x.2 else ![1 / 4, 0, 1 / 4] x.2
  nonneg := fun x i => by
    rcases x with ⟨_, θ⟩
    cases i <;> fin_cases θ <;> simp <;> norm_num
  sum_one := by
    simp [Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_three, Fintype.sum_bool]
    norm_num

/-- The installed states of `meanJoint`'s reflected modification: the conditionals `Q_true = δ_1`,
`Q_false = (1/2, 0, 1/2)`.
Source: findings F16
Kind: D
Fidelity: n/a -/
def meanInstalled : Installed (Unit × Fin 3) Bool where
  Q := fun i x => if i then ![0, 1, 0] x.2 else ![1 / 2, 0, 1 / 2] x.2
  nonneg := fun i x => by
    rcases x with ⟨_, θ⟩
    cases i <;> fin_cases θ <;> simp <;> norm_num
  sum_one := fun i => by
    cases i <;> simp [Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_three] <;> norm_num

/-- The candidate values `u_θ = (−1, 0, 1)` of the one act.
Source: findings F16
Kind: D
Fidelity: n/a -/
def meanU : Fin 3 → Unit → Unit → ℝ := fun θ _ _ => ![-1, 0, 1] θ

theorem mean_π (i : Bool) : meanJoint.π i = 1 / 2 := by
  cases i <;>
    simp [Joint.π, meanJoint, Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_three] <;>
    norm_num

/-- (R⁺) holds for `meanJoint`/`meanInstalled`: the installed states are the conditionals.
Source: findings F16
Kind: L
Fidelity: exact -/
theorem mean_reflection : Reflection meanJoint meanInstalled := by
  intro i _ x
  rw [mean_π]
  rcases x with ⟨_, θ⟩
  cases i <;> fin_cases θ <;> simp [meanJoint, meanInstalled] <;> norm_num

/-- The outcome is informative about `u_{θ,a}`: `P(θ = 1 ∧ i = true) = 1/2 ≠ 1/4 = π_true · P⁺(θ = 1)`
(equivalently `P(u = 0 ∣ i = true) = 1 ≠ 1/2 = P(u = 0)`).
Source: findings F16
Kind: L
Fidelity: exact -/
theorem mean_informative : meanJoint.P ((), 1) true ≠ meanJoint.π true * meanJoint.marg ((), 1) := by
  rw [mean_π]
  simp [meanJoint, Joint.marg]

/-- **Claim 4's "equality iff no information" fails in its only-if direction (F16)**: the
modification is reflected and its outcome is informative about `u_{θ,a}`, yet the mean-square error
of the installed representation equals the current one (`1/2 = 1/2`), because both conditional
means of `u` are `0`. What is true is `representation_eq_iff`'s clause, instantiated here as the
last conjunct: equality iff `Ū^{(i)}_a = Ū_a` on the support. The equality-side witness of
`representation_eq_iff` (the strict side is `coin_pill_worse`).
Source: [[value-change-as-epistemic-update]] §2.4 Claim 4 ("Equality holds iff the modification
carries no information about `u_{θ,a}`"); findings F16; audit r4 fidelity N1
Kind: N+ (refutation of the only-if under the independence reading)
Fidelity: exact -/
theorem representation_eq_informative :
    Reflection meanJoint meanInstalled ∧
    meanJoint.P ((), 1) true ≠ meanJoint.π true * meanJoint.marg ((), 1) ∧
    msErr meanJoint meanU () (fun ω i => installedEffU meanInstalled meanU i () ω) = 1 / 2 ∧
    msErr meanJoint meanU () (fun ω _ => Ubar meanJoint meanU () ω) = 1 / 2 ∧
    msErr meanJoint meanU () (fun ω i => installedEffU meanInstalled meanU i () ω) =
      msErr meanJoint meanU () (fun ω _ => Ubar meanJoint meanU () ω) ∧
    (msErr meanJoint meanU () (fun ω i => installedEffU meanInstalled meanU i () ω) =
        msErr meanJoint meanU () (fun ω _ => Ubar meanJoint meanU () ω) ↔
      ∀ ω i, 0 < Pωi meanJoint ω i → installedEffU meanInstalled meanU i () ω = Ubar meanJoint meanU () ω) := by
  refine ⟨mean_reflection, mean_informative, ?_, ?_, ?_, representation_eq_iff mean_reflection meanU ()⟩ <;>
    simp [msErr, installedEffU, Ubar, Pω, Pωi, meanJoint, meanInstalled, meanU, Fintype.sum_prod_type,
      Fintype.sum_unique, Fin.sum_univ_three, Fintype.sum_bool] <;> norm_num

end

end Cleanroom.Corrigibility.CorrValueChange

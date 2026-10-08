import Cleanroom.Corrigibility.CorrValueChange.Variants
import Mathlib.Algebra.BigOperators.Fin

/-!
# corr-value-change — the modest teacher (T9(c))

Source: [[value-change-as-epistemic-update]] §2.7 (Example), §6.6. `P(θ = A) = 3/10`; the source
is perfectly informative but modest: when `θ = A` it installs `Q_A = (9/10, 1/10)`, when `θ = B`
it installs `Q_B = (1/10, 9/10)`. Act-value reflection fails on `a₁` and `a₂` (and holds on the
safe act `a₃`, findings F5), (M⁺) fails (`17/50 ≠ 3/10`), no event `L` of positive probability
gives (R⁺∣L), yet `Val(accept) = 1 > 7/10 = Val(decline)` and (A) = 0.

The last section (`act_value_beyond_reflection`, repair r3) supplies what the sharp teacher does not:
a modification on which act-value reflection holds while both (R⁺) and (M⁺) fail, so that
`act_value_good` applies where `good_theorem` does not — §2.7's "trust without the outcome events".
The section after it (`act_value_hfac_needed`, repair r4) shows that `act_value_good`'s "the choice
is a function of the vector" hypothesis cannot be dropped.
-/

namespace Cleanroom.Corrigibility.CorrValueChange

open Finset

noncomputable section

variable {Ω Θ I A : Type} [Fintype Ω] [Fintype Θ] [Fintype I] [Fintype A] [DecidableEq Ω]
  [DecidableEq Θ] [DecidableEq I] [DecidableEq A]

/-- Act-value reflection for a single act `a`: `E_0[U_a ∣ (V_b)_b] = V_a` on every cell.
Source: [[value-change-as-epistemic-update]] §2.7 ("for every `a`")
Kind: D
Fidelity: exact (one act of `ActValueReflection`) -/
def ActValueReflectionOn (J : Joint (Ω × Θ) I) (Q : Installed (Ω × Θ) I) (u : Θ → A → Ω → ℝ)
    (a : A) : Prop :=
  ∀ i, ∑ j ∈ Vcell Q u i, S J u a j = Vvec Q u i a * ∑ j ∈ Vcell Q u i, J.π j

/-- Act-value reflection is act-value reflection on every act.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem actValueReflection_iff (J : Joint (Ω × Θ) I) (Q : Installed (Ω × Θ) I)
    (u : Θ → A → Ω → ℝ) : ActValueReflection J Q u ↔ ∀ a, ActValueReflectionOn J Q u a := Iff.rfl

/-- The modest teacher's joint: `P(θ, i) = [θ = i] · (3/10 if θ = A else 7/10)`.
Source: [[value-change-as-epistemic-update]] §2.7 ("`P_0(θ = A) = 0.3`; when `θ = A` it installs
`Q_1` … when `θ = B` it installs `Q_2`")
Kind: D
Fidelity: exact -/
def modestJoint : Joint (Unit × Bool) Bool where
  P := fun x i => if x.2 = i then (if i then 3 / 10 else 7 / 10) else 0
  nonneg := fun x i => by split_ifs <;> norm_num
  sum_one := by simp [Fintype.sum_prod_type, Fintype.sum_bool]; norm_num

/-- The branch values of the modest teacher: `S(·, A) = (3/10, 0, 9/50)`, `S(·, B) = (0, 7/10, 21/50)`.
Source: [[value-change-as-epistemic-update]] §2.7
Kind: L
Fidelity: exact -/
theorem modest_S (a : Fin 3) (i : Bool) :
    S modestJoint (uT (3 / 5)) a i =
      ![if i then 3 / 10 else 0, if i then 0 else 7 / 10, if i then 9 / 50 else 21 / 50] a := by
  fin_cases a <;> cases i <;>
    simp [S, Uplus, uT, modestJoint, Fintype.sum_prod_type, Fintype.sum_bool] <;> norm_num

/-- `E_P[U_a] = (3/10, 7/10, 3/5)`.
Source: [[value-change-as-epistemic-update]] §2.7 ("`Val(decline) = max(0.3, 0.7, 0.6)`")
Kind: L
Fidelity: exact -/
theorem modest_EU (a : Fin 3) : EU modestJoint (uT (3 / 5)) a = ![3 / 10, 7 / 10, 3 / 5] a := by
  unfold EU; rw [Fintype.sum_bool, modest_S, modest_S]; fin_cases a <;> simp <;> norm_num

/-- The two installed vectors differ, so each `V`-cell is a singleton.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem modest_Vcell (i : Bool) : Vcell install9 (uT (3 / 5)) i = {i} := by
  ext j
  simp only [Vcell, mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro h
    by_contra hne
    have := congrFun h 0
    simp only [Vvec] at this
    unfold install9 at this
    rw [teacher_EQ, teacher_EQ] at this
    cases i <;> cases j <;> simp at this hne <;> norm_num at this
  · rintro rfl; rfl

/-- `π_A = 3/10`, `π_B = 7/10`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem modest_π (i : Bool) : modestJoint.π i = if i then 3 / 10 else 7 / 10 := by
  cases i <;> simp [Joint.π, modestJoint, Fintype.sum_prod_type, Fintype.sum_bool]

/-- **T9(c), the modest teacher**: act-value reflection fails on `a₁` and on `a₂`
(`E_0[U_{a₁} ∣ V = (9/10, 1/10, 3/5)] = 1 ≠ 9/10`) and holds on the safe act `a₃` (F5); (M⁺) fails;
the modified agent acts on the signal; `Val(accept) = 1`, `Val(decline) = 7/10` (with `a^K = a₂`);
and (A) = 0 — the installed choices are the informed old-`U` choices.
Source: [[value-change-as-epistemic-update]] §2.7 (Example, computed)
Kind: N+
Fidelity: exact except that the note says reflection fails "on every act" (F5: not on `a₃`) -/
theorem modest_teacher :
    ¬ ActValueReflectionOn modestJoint install9 (uT (3 / 5)) 0 ∧
    ¬ ActValueReflectionOn modestJoint install9 (uT (3 / 5)) 1 ∧
    ActValueReflectionOn modestJoint install9 (uT (3 / 5)) 2 ∧
    ¬ Martingale modestJoint install9 ∧
    (∀ i a, EQ install9 (uT (3 / 5)) i a ≤ EQ install9 (uT (3 / 5)) i (actOnSignal i)) ∧
    ValAccept modestJoint (uT (3 / 5)) actOnSignal = 1 ∧
    (∀ a, EU modestJoint (uT (3 / 5)) a ≤ EU modestJoint (uT (3 / 5)) 1) ∧
    ValDecline modestJoint (uT (3 / 5)) 1 = 7 / 10 ∧
    (∀ i a, S modestJoint (uT (3 / 5)) a i ≤ S modestJoint (uT (3 / 5)) (actOnSignal i) i) ∧
    termAep modestJoint (uT (3 / 5)) actOnSignal actOnSignal = 0 := by
  refine ⟨?_, ?_, ?_, ?_, actOnSignal_opt _ (by norm_num), ?_, ?_, ?_, ?_, ?_⟩
  · intro h; have := h true
    rw [modest_Vcell, sum_singleton, sum_singleton, modest_S, modest_π] at this
    simp [Vvec, install9, teacher_EQ] at this; norm_num at this
  · intro h; have := h true
    rw [modest_Vcell, sum_singleton, sum_singleton, modest_S, modest_π] at this
    simp [Vvec, install9, teacher_EQ] at this; norm_num at this
  · intro i
    rw [modest_Vcell, sum_singleton, sum_singleton, modest_S, modest_π]
    simp [Vvec, install9, teacher_EQ]; cases i <;> simp <;> norm_num
  · intro h; have := h ((), true)
    rw [Fintype.sum_bool, modest_π, modest_π] at this
    simp [Joint.marg, modestJoint, install9, installedOf, Fintype.sum_bool] at this
    norm_num at this
  · unfold ValAccept; rw [Fintype.sum_bool, modest_S, modest_S]; simp [actOnSignal]; norm_num
  · intro a; rw [modest_EU, modest_EU]; fin_cases a <;> simp <;> norm_num
  · unfold ValDecline; rw [modest_EU]; simp
  · intro i a; rw [modest_S, modest_S]; cases i <;> fin_cases a <;> simp [actOnSignal] <;> norm_num
  · unfold termAep; simp

/-- **(M⁺) fails numerically**: `E[Q(A)] = 17/50 ≠ 3/10 = P(A)`.
Source: [[value-change-as-epistemic-update]] §2.7 ("`E_0[Q(A)] = 0.34 ≠ 0.3`"), §6.6
Kind: N+
Fidelity: exact -/
theorem modest_martingale_numbers :
    ∑ i, modestJoint.π i * install9.Q i ((), true) = 17 / 50 ∧ modestJoint.marg ((), true) = 3 / 10 := by
  constructor
  · rw [Fintype.sum_bool, modest_π, modest_π]; simp [install9, installedOf]; norm_num
  · simp [Joint.marg, modestJoint, Fintype.sum_bool]

/-- **The modest teacher admits no legitimacy event**: for every event `L` of positive
probability, (R⁺∣L) fails — because `P(· ∣ E_i ∧ L)` is concentrated on `θ = i` while `Q_i` gives
the other hypothesis probability `1/10`. So (A) = 0 and net-positivity hold here at a grade
strictly below conditional reflection (S6: the third grade separated from the second).
Source: [[value-change-as-epistemic-update]] §2.7 ("no faithful extension makes the update a
conditioning"), §3.4 (the grades)
Kind: P
Fidelity: exact
Hyps: (a) `0 < P(L)` -/
theorem modest_no_condReflection (L : Finset ((Unit × Bool) × Bool)) (hL : 0 < modestJoint.massL L) :
    ¬ CondReflection modestJoint install9 L := by
  intro h
  have hsum : modestJoint.massL L = modestJoint.πL L true + modestJoint.πL L false := by
    unfold Joint.massL; rw [Fintype.sum_bool]
  have hzero : ∀ i, modestJoint.P ((), !i) i = 0 := by intro i; cases i <;> simp [modestJoint]
  have key : ∀ i, 0 < modestJoint.πL L i → False := by
    intro i hi
    have := h i hi ((), !i)
    unfold Joint.PL at this
    rw [hzero] at this
    have hQ : install9.Q i ((), !i) = 1 / 10 := by
      cases i <;> simp [install9, installedOf] <;> norm_num
    rw [hQ] at this
    split_ifs at this <;> nlinarith
  rcases (modestJoint.πL_nonneg L true).lt_or_eq with h1 | h1
  · exact key true h1
  rcases (modestJoint.πL_nonneg L false).lt_or_eq with h2 | h2
  · exact key false h2
  rw [hsum, ← h1, ← h2] at hL; exact lt_irrefl 0 (by linarith)

/-! ## The sharp teacher: act-value reflection holds (the witness for `act_value_good`) -/

/-- Under the point-mass installation `δ_i` with the betting utility, the installed act-value
vector at outcome `i` is `a ↦ [i = a]`.
Source: findings F2; audit r1 (the witness for T9(a))
Kind: L
Fidelity: n/a -/
theorem sharp_Vvec (i a : Bool) : Vvec deltaInstalled uBet i a = if i = a then 1 else 0 := by
  unfold Vvec EQ deltaInstalled installedOf Uplus uBet
  cases i <;> cases a <;> simp [Fintype.sum_prod_type]

/-- The cells of the sharp vector are singletons: the vector identifies the outcome.
Source: audit r1 (the witness for T9(a))
Kind: L
Fidelity: n/a -/
theorem sharp_Vcell (i : Bool) : Vcell deltaInstalled uBet i = {i} := by
  ext j
  simp only [Vcell, mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro h
    have := congrFun h true
    rw [sharp_Vvec, sharp_Vvec] at this
    cases i <;> cases j <;> simp at this ⊢
  · rintro rfl; rfl

/-- **Act-value reflection holds for the sharp teacher** (`sharpJoint`, `deltaInstalled`, `uBet`):
on each (singleton) cell, `E_0[U_a ∣ V] = V_a`.
Source: [[value-change-as-epistemic-update]] §2.7; audit r1
Kind: N+
Fidelity: exact -/
theorem sharp_actValueReflection : ActValueReflection sharpJoint deltaInstalled uBet := by
  intro a i
  rw [sharp_Vcell, sum_singleton, sum_singleton]
  have h := S_eq_of_reflection (teacher_reflection 1 (by norm_num) (by norm_num)) uBet a i
  unfold sharpJoint deltaInstalled
  rw [h]; unfold Vvec; exact mul_comm _ _

/-- **The full hypothesis package of `act_value_good` is inhabited, non-degenerately**: the sharp
teacher has act-value reflection, `a* = id` is a function of the vector and maximizes it, `a^K = true`
is `P`-optimal, and the conclusion is strict there: `Val(decline) = 1/2 < 1 = Val(accept)` (two
distinct installed vectors, a perfectly informative signal).
Source: [[value-change-as-epistemic-update]] §2.7; audit r1 (B2)
Kind: N+
Fidelity: exact -/
theorem act_value_package :
    ActValueReflection sharpJoint deltaInstalled uBet ∧
    (∀ i j, Vvec deltaInstalled uBet i = Vvec deltaInstalled uBet j → id i = id j) ∧
    (∀ i a, Vvec deltaInstalled uBet i a ≤ Vvec deltaInstalled uBet i (id i)) ∧
    (∀ a, EU sharpJoint uBet a ≤ EU sharpJoint uBet true) ∧
    ValDecline sharpJoint uBet true < ValAccept sharpJoint uBet id := by
  refine ⟨sharp_actValueReflection, ?_, ?_, strict_clause_left_fails.2.2.1,
    strict_clause_left_fails.2.2.2.2⟩
  · intro i j h
    have := congrFun h true
    rw [sharp_Vvec, sharp_Vvec] at this
    cases i <;> cases j <;> simp at this ⊢
  · intro i a; rw [sharp_Vvec, sharp_Vvec]; cases i <;> cases a <;> simp


/-! ## Act-value trust beyond reflection: a witness for `act_value_good` that is not reflected

The sharp teacher (`act_value_package`) is fully reflected (`teacher_reflection 1`), so on it the
conclusion of `act_value_good` already follows from `good_theorem`; the modest teacher fails
act-value reflection on two acts. The model here (adopted from the audit r3 adversarial probe
`ActValueBeyondReflection.lean`) separates the two hypotheses: three candidate values `Θ = Fin 3`,
two acts, two outcomes; only `θ = 0` is value-relevant, so the installed states can agree with the
conditionals `P(· ∣ E_i)` on every act value and disagree as distributions. -/

/-- The joint `P(((), θ), i)`: `π = (1/2, 1/2)`; given `i = true` the candidates have weights
`(3/10, 1/10, 1/10)`, given `i = false` `(1/10, 1/5, 1/5)`.
Source: audit r3 (adversarial) probe; [[value-change-as-epistemic-update]] §2.7
Kind: D
Fidelity: n/a (a separating instance, not in the note) -/
def avJoint : Joint (Unit × Fin 3) Bool where
  P := fun x i => if i then ![3 / 10, 1 / 10, 1 / 10] x.2 else ![1 / 10, 1 / 5, 1 / 5] x.2
  nonneg := fun x i => by
    rcases x with ⟨_, θ⟩
    cases i <;> fin_cases θ <;> simp <;> norm_num
  sum_one := by
    simp [Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_three, Fintype.sum_bool]
    norm_num

/-- The installed states: `Q_true = (3/5, 2/5, 0)`, `Q_false = (1/5, 0, 4/5)`. Each agrees with the
conditional `P(· ∣ E_i)` on `θ = 0` (`3/5`, `1/5`) and disagrees on how the rest splits.
Source: audit r3 (adversarial) probe
Kind: D
Fidelity: n/a -/
def avInstalled : Installed (Unit × Fin 3) Bool where
  Q := fun i x => if i then ![3 / 5, 2 / 5, 0] x.2 else ![1 / 5, 0, 4 / 5] x.2
  nonneg := fun i x => by
    rcases x with ⟨_, θ⟩
    cases i <;> fin_cases θ <;> simp <;> norm_num
  sum_one := fun i => by
    cases i <;> simp [Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_three] <;> norm_num

/-- Two acts: `true` pays the constant `2/5`; `false` pays `1` iff `θ = 0`. Only `θ = 0` is
value-relevant, which is why act-value reflection can hold while the states differ.
Source: audit r3 (adversarial) probe
Kind: D
Fidelity: n/a -/
def avU : Fin 3 → Bool → Unit → ℝ := fun θ a _ => if a then 2 / 5 else ![1, 0, 0] θ

/-- The installed choice: `false` (bet on `θ = 0`) after `true`, the safe act after `false`.
Source: audit r3 (adversarial) probe
Kind: D
Fidelity: n/a -/
def avStar : Bool → Bool := fun i => !i

theorem avπ (i : Bool) : avJoint.π i = 1 / 2 := by
  cases i <;> simp [Joint.π, avJoint, Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_three] <;>
    norm_num

theorem avS (a i : Bool) :
    S avJoint avU a i = if i then (if a then 1 / 5 else 3 / 10) else (if a then 1 / 5 else 1 / 10) := by
  cases i <;> cases a <;>
    simp [S, Uplus, avJoint, avU, Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_three] <;>
    norm_num

theorem avEU (a : Bool) : EU avJoint avU a = 2 / 5 := by
  cases a <;> simp [EU, avS, Fintype.sum_bool] <;> norm_num

theorem avVvec (i a : Bool) :
    Vvec avInstalled avU i a = if i then (if a then 2 / 5 else 3 / 5) else (if a then 2 / 5 else 1 / 5) := by
  cases i <;> cases a <;>
    simp [Vvec, EQ, Uplus, avInstalled, avU, Fintype.sum_prod_type, Fintype.sum_unique,
      Fin.sum_univ_three] <;> norm_num

/-- The value vectors of the two outcomes differ, so the cells of the partition are singletons.
Source: audit r3 (adversarial) probe
Kind: L
Fidelity: n/a -/
theorem avVcell (i : Bool) : Vcell avInstalled avU i = {i} := by
  ext j
  simp only [Vcell, mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro h
    have h' := congrFun h false
    rw [avVvec, avVvec] at h'
    cases i <;> cases j <;> simp at h' ⊢ <;> (try norm_num at h')
  · rintro rfl; rfl

/-- **Act-value reflection holds** on `avJoint`/`avInstalled`: on every (singleton) cell,
`S(a, i) = V_a(i) · π_i`.
Source: [[value-change-as-epistemic-update]] §2.7; audit r3 (adversarial) probe
Kind: N+
Fidelity: exact -/
theorem av_actValueReflection : ActValueReflection avJoint avInstalled avU := by
  intro a i
  rw [avVcell, sum_singleton, sum_singleton, avVvec, avS, avπ]
  cases i <;> cases a <;> norm_num

/-- **(R⁺) fails** there: `P(((), 1), true) = 1/10 ≠ 1/5 = π_true · Q_true((), 1)`.
Source: audit r3 (adversarial) probe
Kind: N+ (refutation)
Fidelity: exact -/
theorem av_not_reflection : ¬ Reflection avJoint avInstalled := by
  intro h
  have := h true (by rw [avπ]; norm_num) ((), 1)
  rw [avπ] at this
  simp [avJoint, avInstalled] at this <;> norm_num at this

/-- **(M⁺) fails** there: `P⁺((), 1) = 3/10 ≠ 1/5 = ∑_i π_i Q_i((), 1)`. So no faithful extension
makes this update a conditioning (`lawMartingale_of_reflection`), as in the note's §2.7 example.
Source: audit r3 (adversarial) probe; [[value-change-as-epistemic-update]] §2.7
Kind: N+ (refutation)
Fidelity: exact -/
theorem av_not_martingale : ¬ Martingale avJoint avInstalled := by
  intro h
  have := h ((), 1)
  rw [Fintype.sum_bool, avπ, avπ] at this
  simp [Joint.marg, avJoint, avInstalled, Fintype.sum_bool] at this <;> norm_num at this

theorem av_hfac : ∀ i j, Vvec avInstalled avU i = Vvec avInstalled avU j → avStar i = avStar j := by
  intro i j h
  have h' := congrFun h false
  rw [avVvec, avVvec] at h'
  cases i <;> cases j <;> simp [avStar] at h' ⊢ <;> (try norm_num at h')

theorem av_hstar : ∀ i a, Vvec avInstalled avU i a ≤ Vvec avInstalled avU i (avStar i) := by
  intro i a
  rw [avVvec, avVvec]
  cases i <;> cases a <;> simp [avStar] <;> norm_num

theorem av_hK : ∀ a, EU avJoint avU a ≤ EU avJoint avU true := by
  intro a; rw [avEU, avEU]

theorem av_values :
    ValAccept avJoint avU avStar = 1 / 2 ∧ ValDecline avJoint avU true = 2 / 5 := by
  constructor
  · unfold ValAccept; rw [Fintype.sum_bool, avS, avS]; simp [avStar]; norm_num
  · unfold ValDecline; exact avEU true

/-- **T9(a) bites beyond reflection**: the full hypothesis package of `act_value_good` on a
modification that is neither reflected (¬(R⁺)) nor martingale (¬(M⁺)), with the inequality strict,
`Val(decline) = 2/5 < 1/2 = Val(accept)`, and the theorem instantiated. On this instance
`good_theorem` does not apply (its hypothesis fails), so the act-value form is strictly weaker as a
hypothesis — which `act_value_package` (the sharp teacher, reflected) does not show.
Source: [[value-change-as-epistemic-update]] §2.7 ("with no mention of the installed state");
audit r3 (adversarial) N1, probe `ActValueBeyondReflection.lean`
Kind: N+
Fidelity: exact -/
theorem act_value_beyond_reflection :
    ActValueReflection avJoint avInstalled avU ∧
    ¬ Reflection avJoint avInstalled ∧
    ¬ Martingale avJoint avInstalled ∧
    (∀ i j, Vvec avInstalled avU i = Vvec avInstalled avU j → avStar i = avStar j) ∧
    (∀ i a, Vvec avInstalled avU i a ≤ Vvec avInstalled avU i (avStar i)) ∧
    (∀ a, EU avJoint avU a ≤ EU avJoint avU true) ∧
    ValDecline avJoint avU true ≤ ValAccept avJoint avU avStar ∧
    ValDecline avJoint avU true < ValAccept avJoint avU avStar := by
  refine ⟨av_actValueReflection, av_not_reflection, av_not_martingale, av_hfac, av_hstar, av_hK,
    act_value_good avJoint avInstalled avU avStar true av_actValueReflection av_hfac av_hstar av_hK, ?_⟩
  obtain ⟨h1, h2⟩ := av_values
  rw [h1, h2]; norm_num


/-! ## `act_value_good`'s `hfac` is load-bearing (repair r4; audit r4 adversarial N1) -/

/-- The anti-choice: after signal `i`, bet on `!i`.
Source: audit r4 adversarial N1 (probe `ActValueHfacNeeded.lean`)
Kind: D
Fidelity: n/a -/
def antiStar : Bool → Bool := fun i => !i

theorem anti_Vvec (i a : Bool) : Vvec uniformInstalled uBet i a = 1 / 2 := by
  unfold Vvec EQ uniformInstalled installedOf Uplus uBet
  cases i <;> cases a <;> simp [Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool] <;>
    norm_num

theorem anti_Vcell (i : Bool) : Vcell uniformInstalled uBet i = univ := by
  ext j
  simp only [Vcell, mem_filter, mem_univ, true_and, iff_true]
  funext a; rw [anti_Vvec, anti_Vvec]

theorem anti_S (a i : Bool) : S sharpJoint uBet a i = if i = a then 1 / 2 else 0 := by
  unfold S sharpJoint teacherJoint Uplus uBet
  cases i <;> cases a <;> simp [Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool] <;>
    norm_num

theorem anti_π (i : Bool) : sharpJoint.π i = 1 / 2 := teacher_π 1 (by norm_num) (by norm_num) i

/-- Act-value reflection holds for the sharp joint with the constant uniform installation: the
vector is constant (`V_a ≡ 1/2`), so the one cell is `I` and the condition is `E_P[U_a] = 1/2`.
Source: [[value-change-as-epistemic-update]] §2.7; audit r4 adversarial N1
Kind: L
Fidelity: exact -/
theorem anti_actValueReflection : ActValueReflection sharpJoint uniformInstalled uBet := by
  intro a i
  rw [anti_Vcell, anti_Vvec, Fintype.sum_bool, Fintype.sum_bool, anti_S, anti_S, anti_π, anti_π]
  cases a <;> norm_num

theorem anti_hstar :
    ∀ i a, Vvec uniformInstalled uBet i a ≤ Vvec uniformInstalled uBet i (antiStar i) := by
  intro i a; rw [anti_Vvec, anti_Vvec]

theorem anti_EU (a : Bool) : EU sharpJoint uBet a = 1 / 2 := by
  unfold EU; rw [Fintype.sum_bool, anti_S, anti_S]; cases a <;> norm_num

theorem anti_hK : ∀ a, EU sharpJoint uBet a ≤ EU sharpJoint uBet true := by
  intro a; rw [anti_EU, anti_EU]

/-- The anti-choice is not a function of the vector: `V(true) = V(false)` but `!true ≠ !false`.
Source: audit r4 adversarial N1
Kind: L
Fidelity: exact -/
theorem anti_not_hfac :
    ¬ ∀ i j, Vvec uniformInstalled uBet i = Vvec uniformInstalled uBet j → antiStar i = antiStar j := by
  intro h
  have := h true false (by funext a; rw [anti_Vvec, anti_Vvec])
  simp [antiStar] at this

theorem anti_values :
    ValAccept sharpJoint uBet antiStar = 0 ∧ ValDecline sharpJoint uBet true = 1 / 2 := by
  constructor
  · unfold ValAccept; rw [Fintype.sum_bool, anti_S, anti_S]; simp [antiStar]
  · unfold ValDecline; exact anti_EU true

/-- **`act_value_good`'s `hfac` is load-bearing**: on the sharp joint with the constant uniform
installation and the betting utility, act-value reflection holds, every act maximizes every
installed vector (ties), `a^K = true` is `P`-optimal, the anti-choice `a*_i = !i` is an installed
maximizer at each outcome but not a function of the (constant) vector, and
`Val(accept) = 0 < 1/2 = Val(decline)`. So the note's "since `a*` is a function of the vector" is
the tie convention of F3 made a hypothesis, not a consequence of maximization, and the theorem
cannot be strengthened by dropping it.
Source: [[value-change-as-epistemic-update]] §2.7 ("since `a*` is a function of the vector");
audit r4 adversarial N1 (probe `ActValueHfacNeeded.lean`)
Kind: N+ (the hypothesis is necessary)
Fidelity: exact -/
theorem act_value_hfac_needed :
    ActValueReflection sharpJoint uniformInstalled uBet ∧
    (∀ i a, Vvec uniformInstalled uBet i a ≤ Vvec uniformInstalled uBet i (antiStar i)) ∧
    (∀ a, EU sharpJoint uBet a ≤ EU sharpJoint uBet true) ∧
    ¬ (∀ i j, Vvec uniformInstalled uBet i = Vvec uniformInstalled uBet j → antiStar i = antiStar j) ∧
    ValAccept sharpJoint uBet antiStar < ValDecline sharpJoint uBet true := by
  refine ⟨anti_actValueReflection, anti_hstar, anti_hK, anti_not_hfac, ?_⟩
  obtain ⟨h1, h2⟩ := anti_values
  rw [h1, h2]; norm_num

end

end Cleanroom.Corrigibility.CorrValueChange

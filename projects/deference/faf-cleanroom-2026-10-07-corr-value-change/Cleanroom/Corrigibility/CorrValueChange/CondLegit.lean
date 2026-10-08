import Cleanroom.Corrigibility.CorrValueChange.Variants
import Cleanroom.Corrigibility.CorrValueChange.AltForm

/-!
# corr-value-change — reflection conditional on legitimacy (T8)

Source: [[value-change-as-epistemic-update]] §2.3 (Conditional reflection), §2.6, §3.4. Under
(R⁺∣L) the installed state is `P(· ∣ E_i ∧ L)`; the current agent prices the `L`-part (where the
installed choice is the informed choice) and the `¬L`-part (where it is not). The display of §2.6
is `accept_split`; the λ-example (teacher with probability `λ = P(L)`, coin otherwise) gives the
numbers `Val(accept) = 1/2 + 2λ/5` against `3/5`, the threshold `λ > 1/4`, the hedged alternative,
and the refutation of §3.4's "each grade implies the next" (findings F4).
-/

namespace Cleanroom.Corrigibility.CorrValueChange

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω Θ I A : Type} [Fintype Ω] [Fintype Θ] [Fintype I] [Fintype A] [DecidableEq Ω]
  [DecidableEq Θ] [DecidableEq I] [DecidableEq A]

/-- The `L`-part of the branch value: `S_L(a, i) = ∑_x P(x,i)𝟙_L u_a(x) = P(E_i ∧ L) E[U_a ∣ E_i, L]`.
Source: [[value-change-as-epistemic-update]] §2.6 (the display)
Kind: D
Fidelity: exact -/
def SL (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (L : Finset ((Ω × Θ) × I)) (a : A) (i : I) : ℝ :=
  ∑ x, J.PL L x i * Uplus u a x

/-- The `¬L`-part: `S_{¬L}(a, i) = ∑_x (P(x,i) − P(x,i)𝟙_L) u_a(x) = P(E_i ∧ ¬L) E[U_a ∣ E_i, ¬L]`.
Source: [[value-change-as-epistemic-update]] §2.6
Kind: D
Fidelity: exact -/
def SnL (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (L : Finset ((Ω × Θ) × I)) (a : A) (i : I) : ℝ :=
  ∑ x, (J.P x i - J.PL L x i) * Uplus u a x

/-- `P(E_i ∧ ¬L) = π_i − P(E_i ∧ L)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def πnL (J : Joint (Ω × Θ) I) (L : Finset ((Ω × Θ) × I)) (i : I) : ℝ := J.π i - J.πL L i

/-- `S = S_L + S_{¬L}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem S_eq_SL_add_SnL (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (L : Finset ((Ω × Θ) × I))
    (a : A) (i : I) : S J u a i = SL J u L a i + SnL J u L a i := by
  unfold S SL SnL; rw [← sum_add_distrib]; refine sum_congr rfl fun x _ => ?_; ring

/-- Under (R⁺∣L), `S_L(a, i) = P(E_i ∧ L) · E_{Q_i}[U_a]` for every `i` (both sides vanish when
`P(E_i ∧ L) = 0`).
Source: [[value-change-as-epistemic-update]] §2.6
Kind: L
Fidelity: exact -/
theorem SL_eq_of_condReflection {J : Joint (Ω × Θ) I} {Q : Installed (Ω × Θ) I}
    {L : Finset ((Ω × Θ) × I)} (h : CondReflection J Q L) (u : Θ → A → Ω → ℝ) (a : A) (i : I) :
    SL J u L a i = J.πL L i * EQ Q u i a := by
  unfold SL EQ
  rcases (J.πL_nonneg L i).lt_or_eq with hpos | hzero
  · rw [mul_sum]; refine sum_congr rfl fun x _ => ?_; rw [h i hpos x]; ring
  · rw [← hzero, zero_mul]
    apply sum_eq_zero; intro x _
    have hle : J.PL L x i ≤ J.πL L i :=
      single_le_sum (f := fun x => J.PL L x i) (fun x _ => J.PL_nonneg L x i) (mem_univ x)
    have : J.PL L x i = 0 := le_antisymm (hzero ▸ hle) (J.PL_nonneg L x i)
    rw [this, zero_mul]

/-- **T8(b), the split of `Val(accept)` under (R⁺∣L)** (product form):
`Val(accept) = ∑_i [S_L(a*_i, i) + S_{¬L}(a*_i, i)]`, where the `L`-part is maximized by the installed
choice (`S_L(a, i) ≤ S_L(a*_i, i)` for every `a`: on `L` the installed agent is the informed agent)
and the `¬L`-part is whatever acting on `Q_i` costs there. The division form of §2.6's display is
`accept_split_div`.
Source: [[value-change-as-epistemic-update]] §2.6 (the display)
Kind: L (the first conjunct is `S_eq_SL_add_SnL` summed, the second one rewrite through
`SL_eq_of_condReflection`; audit r1 N3)
Fidelity: exact
Hyps: (a) `h : CondReflection`, `hstar` -/
theorem accept_split {J : Joint (Ω × Θ) I} {Q : Installed (Ω × Θ) I} {L : Finset ((Ω × Θ) × I)}
    (h : CondReflection J Q L) (u : Θ → A → Ω → ℝ) (astar : I → A)
    (hstar : ∀ i a, EQ Q u i a ≤ EQ Q u i (astar i)) :
    ValAccept J u astar = ∑ i, (SL J u L (astar i) i + SnL J u L (astar i) i) ∧
      ∀ i a, SL J u L a i ≤ SL J u L (astar i) i := by
  constructor
  · unfold ValAccept; refine sum_congr rfl fun i _ => S_eq_SL_add_SnL J u L _ i
  · intro i a
    rw [SL_eq_of_condReflection h, SL_eq_of_condReflection h]
    exact mul_le_mul_of_nonneg_left (hstar i a) (J.πL_nonneg L i)

/-- **T8(b), the display of §2.6**: when every `π_i`, `P(E_i ∧ L)`, `P(E_i ∧ ¬L)` is positive,
`Val(accept) = ∑_i π_i [P(L ∣ E_i) · max_a E[U_a ∣ E_i, L] + P(¬L ∣ E_i) · E[U_{a*_i} ∣ E_i, ¬L]]`,
with `max_a E[U_a ∣ E_i, L] = S_L(a*_i, i)/P(E_i ∧ L)` (`accept_split`).
Source: [[value-change-as-epistemic-update]] §2.6 (the display)
Kind: L
Fidelity: exact
Hyps: (a) `h`, `hstar`; positivity of the conditioning events (the display's own requirement) -/
theorem accept_split_div {J : Joint (Ω × Θ) I} {Q : Installed (Ω × Θ) I} {L : Finset ((Ω × Θ) × I)}
    (h : CondReflection J Q L) (u : Θ → A → Ω → ℝ) (astar : I → A)
    (hstar : ∀ i a, EQ Q u i a ≤ EQ Q u i (astar i)) (hπ : ∀ i, 0 < J.π i)
    (hL : ∀ i, 0 < J.πL L i) (hnL : ∀ i, 0 < πnL J L i) :
    ValAccept J u astar = ∑ i, J.π i * ((J.πL L i / J.π i) * (SL J u L (astar i) i / J.πL L i) +
      (πnL J L i / J.π i) * (SnL J u L (astar i) i / πnL J L i)) := by
  rw [(accept_split h u astar hstar).1]
  refine sum_congr rfl fun i _ => ?_
  have h1 := hπ i; have h2 := hL i; have h3 := hnL i
  field_simp

/-! ## The λ-example (§2.6, computed) -/

/-- The utilities of the example on worlds `(ℓ, θ)`: the legitimacy bit `ℓ` does not enter.
Source: [[value-change-as-epistemic-update]] §2.6
Kind: D
Fidelity: exact -/
def uL (s : ℝ) : Bool → Fin 3 → Bool → ℝ := fun θ a _ => ![if θ then 1 else 0, if θ then 0 else 1, s] a

/-- The joint of the λ-example: with probability `λ` the source is the teacher (`ℓ = true`,
`P(i = θ ∣ L) = 9/10`), otherwise the coin (`ℓ = false`, signal independent of `θ`), independently
of everything else; `θ` fair.
Source: [[value-change-as-epistemic-update]] §2.6 ("let the source be the teacher with probability
`λ = P(L)` and the coin otherwise, independently of everything else")
Kind: D
Fidelity: exact -/
def lamJoint (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) : Joint (Bool × Bool) Bool where
  P := fun x i => (if x.1 then lam else 1 - lam) * (1 / 2) *
    (if x.1 then (if x.2 = i then 9 / 10 else 1 / 10) else 1 / 2)
  nonneg := fun x i => by
    have : 0 ≤ 1 - lam := by linarith
    split_ifs <;> positivity
  sum_one := by simp [Fintype.sum_prod_type, Fintype.sum_bool]; ring

/-- The legitimacy event `L = {ℓ = true}`.
Source: [[value-change-as-epistemic-update]] §2.6
Kind: D
Fidelity: exact -/
def Lset : Finset ((Bool × Bool) × Bool) := univ.filter fun y => y.1.1 = true

/-- The unhedged installation: the `L`-conditional `Q_i = P(· ∣ E_i ∧ L)`, i.e. `(9/10, 1/10)` on
`θ` and certain of `ℓ = true`.
Source: [[value-change-as-epistemic-update]] §2.6 ("let the modification install the
`L`-conditional `Q_i = (0.9, 0.1)` regardless")
Kind: D
Fidelity: exact -/
def lamInstalled : Installed (Bool × Bool) Bool where
  Q := fun i x => if x.1 then (if x.2 = i then 9 / 10 else 1 / 10) else 0
  nonneg := fun i x => by split_ifs <;> norm_num
  sum_one := fun i => by cases i <;> simp [Fintype.sum_prod_type, Fintype.sum_bool] <;> norm_num

/-- `P(E_i ∧ L) = λ/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem lam_πL (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (i : Bool) :
    (lamJoint lam h0 h1).πL Lset i = lam / 2 := by
  cases i <;> simp [Joint.πL, Joint.PL, Lset, lamJoint, Fintype.sum_prod_type, Fintype.sum_bool] <;> ring

/-- `π_i = 1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem lam_π (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (i : Bool) :
    (lamJoint lam h0 h1).π i = 1 / 2 := by
  cases i <;> simp [Joint.π, lamJoint, Fintype.sum_prod_type, Fintype.sum_bool] <;> ring

/-- **(R⁺∣L) holds in the λ-example**: the installed state is the `L`-conditional. Stated for all
`λ ∈ [0, 1]`; it is a witness with content for `λ > 0` (`P(E_i ∧ L) = λ/2 > 0`, `lam_πL`), while at
`λ = 0` it is the vacuous case (`lam_zero_vacuous`: every installed family is `(R⁺∣L)`-reflected).
Source: [[value-change-as-epistemic-update]] §2.6
Kind: N+ (for `λ > 0`)
Fidelity: exact -/
theorem lam_condReflection (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    CondReflection (lamJoint lam h0 h1) lamInstalled Lset := by
  intro i _ x
  rw [lam_πL]
  rcases x with ⟨ℓ, θ⟩
  cases ℓ <;> cases θ <;> cases i <;> simp [Joint.PL, Lset, lamJoint, lamInstalled] <;> ring

/-- At `λ = 0` the event `L` is null and `(R⁺∣L)` is vacuous: every installed family satisfies it.
Source: none: infrastructure (audit r1, adversarial N1)
Kind: L
Fidelity: n/a -/
theorem lam_zero_vacuous (Q : Installed (Bool × Bool) Bool) :
    CondReflection (lamJoint 0 (by norm_num) (by norm_num)) Q Lset := by
  apply condReflection_of_massL_eq_zero
  unfold Joint.massL
  rw [Fintype.sum_bool, lam_πL, lam_πL]
  norm_num

/-- **(R⁺) fails in the λ-example for `λ < 1`**: `P(θ = A ∣ E_A) = 1/2 + 2λ/5 ≠ 9/10`, and the
installed state is certain of `L` while the agent is not.
Source: [[value-change-as-epistemic-update]] §2.6 ("The agent's own conditional is
`P(θ = i ∣ E_i) = 0.9λ + 0.5(1−λ)`")
Kind: N+
Fidelity: exact -/
theorem lam_not_reflection (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam < 1) :
    ¬ Reflection (lamJoint lam h0 h1.le) lamInstalled := by
  intro h
  have := h true (by rw [lam_π]; norm_num) (false, true)
  rw [lam_π] at this
  simp [lamJoint, lamInstalled] at this
  linarith

/-- The branch values of the λ-example:
`S(·, A) = (1/4 + λ/5, 1/4 − λ/5, 3/10)`, `S(·, B) = (1/4 − λ/5, 1/4 + λ/5, 3/10)`.
Source: [[value-change-as-epistemic-update]] §2.6
Kind: L
Fidelity: exact -/
theorem lam_S (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (a : Fin 3) (i : Bool) :
    S (lamJoint lam h0 h1) (uL (3 / 5)) a i =
      ![if i then 1 / 4 + lam / 5 else 1 / 4 - lam / 5,
        if i then 1 / 4 - lam / 5 else 1 / 4 + lam / 5, 3 / 10] a := by
  fin_cases a <;> cases i <;>
    simp [S, Uplus, uL, lamJoint, Fintype.sum_prod_type, Fintype.sum_bool] <;> ring

/-- The installed values `E_{Q_i}[U_a] = (9/10, 1/10, 3/5)` for `i = A` (and symmetrically).
Source: [[value-change-as-epistemic-update]] §2.6
Kind: L
Fidelity: exact -/
theorem lam_EQ (i : Bool) (a : Fin 3) :
    EQ lamInstalled (uL (3 / 5)) i a = ![if i then 9 / 10 else 1 / 10, if i then 1 / 10 else 9 / 10, 3 / 5] a := by
  fin_cases a <;> cases i <;> simp [EQ, Uplus, uL, lamInstalled, Fintype.sum_prod_type, Fintype.sum_bool]
    <;> norm_num

/-- The modified agent acts on the signal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem lam_actOnSignal_opt :
    ∀ i a, EQ lamInstalled (uL (3 / 5)) i a ≤ EQ lamInstalled (uL (3 / 5)) i (actOnSignal i) := by
  intro i a; rw [lam_EQ, lam_EQ]; cases i <;> fin_cases a <;> simp [actOnSignal] <;> norm_num

/-- **T8(d), the numbers**: `Val(accept) = 1/2 + 2λ/5`, `Val(decline) = 3/5` (the safe act is
`P`-optimal), and the agent accepts iff `λ > 1/4`; the threshold odds `(1/4)/(3/4)` equal the
loss/gain ratio `(3/5 − 1/2)/(9/10 − 3/5)`.
Source: [[value-change-as-epistemic-update]] §2.6 (Numbers, computed)
Kind: P (over all `λ ∈ [0,1]`) / N+
Fidelity: exact -/
theorem lam_numbers (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    ValAccept (lamJoint lam h0 h1) (uL (3 / 5)) actOnSignal = 1 / 2 + 2 * lam / 5 ∧
    (∀ a, EU (lamJoint lam h0 h1) (uL (3 / 5)) a ≤ EU (lamJoint lam h0 h1) (uL (3 / 5)) 2) ∧
    ValDecline (lamJoint lam h0 h1) (uL (3 / 5)) 2 = 3 / 5 ∧
    (ValDecline (lamJoint lam h0 h1) (uL (3 / 5)) 2 < ValAccept (lamJoint lam h0 h1) (uL (3 / 5)) actOnSignal
      ↔ 1 / 4 < lam) ∧
    (1 / 4 : ℝ) / (1 - 1 / 4) = (3 / 5 - 1 / 2) / (9 / 10 - 3 / 5) := by
  have hEU : ∀ a, EU (lamJoint lam h0 h1) (uL (3 / 5)) a = ![1 / 2, 1 / 2, 3 / 5] a := by
    intro a; unfold EU; rw [Fintype.sum_bool, lam_S, lam_S]; fin_cases a <;> simp <;> ring
  have hA : ValAccept (lamJoint lam h0 h1) (uL (3 / 5)) actOnSignal = 1 / 2 + 2 * lam / 5 := by
    unfold ValAccept; rw [Fintype.sum_bool, lam_S, lam_S]; simp [actOnSignal]; ring
  have hD : ValDecline (lamJoint lam h0 h1) (uL (3 / 5)) 2 = 3 / 5 := by
    unfold ValDecline; rw [hEU]; simp
  refine ⟨hA, ?_, hD, ?_, by norm_num⟩
  · intro a; rw [hEU, hEU]; fin_cases a <;> simp <;> norm_num
  · rw [hA, hD]; constructor <;> intro h <;> linarith

/-- **T8(c) and F4, the residual pill is real**: at `λ = 1/8`, (R⁺∣L) holds, the informed old-`U`
choice is the safe act in both branches, and (A) = `−1/20 < 0`; moreover
`Val(accept) = 11/20 < 3/5 = Val(decline)`. So conditional reflection implies neither (A) = 0 nor
net-positivity: §3.4's "each implies the next" fails at its second link. The last clause says the
signal-following choices are the installed maximizers of `lamInstalled` (`lam_actOnSignal_opt`),
so the refutation is about the modification, not a bare choice function (audit r2).
Source: [[value-change-as-epistemic-update]] §2.6 ("(A) is now generically negative"), §3.4;
findings F4
Kind: N+ (refutation of §3.4's chain)
Fidelity: exact -/
theorem cond_reflection_not_imp_A_zero :
    CondReflection (lamJoint (1 / 8) (by norm_num) (by norm_num)) lamInstalled Lset ∧
    (∀ i a, S (lamJoint (1 / 8) (by norm_num) (by norm_num)) (uL (3 / 5)) a i ≤
      S (lamJoint (1 / 8) (by norm_num) (by norm_num)) (uL (3 / 5)) 2 i) ∧
    termAep (lamJoint (1 / 8) (by norm_num) (by norm_num)) (uL (3 / 5)) actOnSignal (fun _ => 2) = -1 / 20 ∧
    ValAccept (lamJoint (1 / 8) (by norm_num) (by norm_num)) (uL (3 / 5)) actOnSignal <
      ValDecline (lamJoint (1 / 8) (by norm_num) (by norm_num)) (uL (3 / 5)) 2 ∧
    (∀ i a, EQ lamInstalled (uL (3 / 5)) i a ≤ EQ lamInstalled (uL (3 / 5)) i (actOnSignal i)) := by
  refine ⟨lam_condReflection _ _ _, ?_, ?_, ?_, lam_actOnSignal_opt⟩
  · intro i a; rw [lam_S, lam_S]; cases i <;> fin_cases a <;> simp <;> norm_num
  · unfold termAep; rw [Fintype.sum_bool, lam_S, lam_S, lam_S, lam_S]; simp [actOnSignal]; norm_num
  · obtain ⟨hA, _, hD, _, _⟩ := lam_numbers (1 / 8) (by norm_num) (by norm_num)
    rw [hA, hD]; norm_num

/-- **S6, the second grade separated from the first**: at `λ = 1/2`, (R⁺∣L) holds, (R⁺) fails,
and (A) = 0 (the signal act is the informed old-`U` choice since `1/4 + λ/5 ≥ 3/10`); the last
clause says the signal-following choices are the installed maximizers of `lamInstalled`.
Source: [[value-change-as-epistemic-update]] §3.4 (the grades); mandate S6
Kind: N+
Fidelity: exact -/
theorem grade_two_separated :
    CondReflection (lamJoint (1 / 2) (by norm_num) (by norm_num)) lamInstalled Lset ∧
    ¬ Reflection (lamJoint (1 / 2) (by norm_num) (by norm_num)) lamInstalled ∧
    (∀ i a, S (lamJoint (1 / 2) (by norm_num) (by norm_num)) (uL (3 / 5)) a i ≤
      S (lamJoint (1 / 2) (by norm_num) (by norm_num)) (uL (3 / 5)) (actOnSignal i) i) ∧
    termAep (lamJoint (1 / 2) (by norm_num) (by norm_num)) (uL (3 / 5)) actOnSignal actOnSignal = 0 ∧
    (∀ i a, EQ lamInstalled (uL (3 / 5)) i a ≤ EQ lamInstalled (uL (3 / 5)) i (actOnSignal i)) := by
  refine ⟨lam_condReflection _ _ _, lam_not_reflection _ _ (by norm_num), ?_, ?_, lam_actOnSignal_opt⟩
  · intro i a; rw [lam_S, lam_S]; cases i <;> fin_cases a <;> simp [actOnSignal] <;> norm_num
  · unfold termAep; simp

/-! ## The hedged installation -/

/-- The hedged installation `Q'_i = P(· ∣ E_i)`: `2 P(x, i)` since `π_i = 1/2`.
Source: [[value-change-as-epistemic-update]] §2.6 ("If instead the modification installed the
hedged state `Q'_i = P(· ∣ E_i)`")
Kind: D
Fidelity: exact -/
def hedgedInstalled (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) : Installed (Bool × Bool) Bool where
  Q := fun i x => 2 * (lamJoint lam h0 h1).P x i
  nonneg := fun i x => by have := (lamJoint lam h0 h1).nonneg x i; linarith
  sum_one := fun i => by
    rw [← mul_sum]
    have := lam_π lam h0 h1 i
    unfold Joint.π at this
    rw [this]; norm_num

/-- The hedged installation is reflected (unconditional reflection by construction).
Source: [[value-change-as-epistemic-update]] §2.6 ("which is unconditional reflection")
Kind: L
Fidelity: exact -/
theorem hedged_reflection (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    Reflection (lamJoint lam h0 h1) (hedgedInstalled lam h0 h1) := by
  intro i _ x; rw [lam_π]; simp [hedgedInstalled]

/-- **The hedged installation inhabits the three clauses of the alternative formalization** with
`L = Lset`, at every `λ ∈ [0, 1]` (through `hedged_reflection` and the converse
`alternative_formalization_iff`): the witness for `alternative_formalization`'s hypothesis package.
Source: [[value-change-as-epistemic-update]] §2.6; audit r1 (B3)
Kind: N+
Fidelity: exact -/
theorem hedged_alternative_clauses (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    (∀ i, 0 < (lamJoint lam h0 h1).π i → ∀ w ∈ Lslice Lset i,
      (hedgedInstalled lam h0 h1).Q i w * (lamJoint lam h0 h1).πL Lset i =
        QL (hedgedInstalled lam h0 h1) Lset i * (lamJoint lam h0 h1).P w i) ∧
    (∀ i, 0 < (lamJoint lam h0 h1).π i →
      QL (hedgedInstalled lam h0 h1) Lset i * (lamJoint lam h0 h1).π i =
        (lamJoint lam h0 h1).πL Lset i) ∧
    (∀ i, 0 < (lamJoint lam h0 h1).π i → ∀ w ∉ Lslice Lset i,
      (hedgedInstalled lam h0 h1).Q i w * ((lamJoint lam h0 h1).π i - (lamJoint lam h0 h1).πL Lset i) =
        (1 - QL (hedgedInstalled lam h0 h1) Lset i) * (lamJoint lam h0 h1).P w i) :=
  (alternative_formalization_iff _ _ _).1 (hedged_reflection lam h0 h1)

/-- **T8(d), `hedged_never_worse`**: installing `P(· ∣ E_i)` gives, for every family of installed
maximizers, `Val(accept) = max(3/5, 1/2 + 2λ/5) ≥ 3/5 = Val(decline)`: (A) = 0 and Good's theorem
is unconditional again.
Source: [[value-change-as-epistemic-update]] §2.6 ("`Val(accept) = max(0.6, 0.5 + 0.4λ)`, and
accepting would never be worse than declining")
Kind: P
Fidelity: exact
Hyps: (a) `hstar` -/
theorem hedged_never_worse (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (astar : Bool → Fin 3)
    (hstar : ∀ i a, EQ (hedgedInstalled lam h0 h1) (uL (3 / 5)) i a ≤
      EQ (hedgedInstalled lam h0 h1) (uL (3 / 5)) i (astar i)) :
    ValAccept (lamJoint lam h0 h1) (uL (3 / 5)) astar = max (3 / 5) (1 / 2 + 2 * lam / 5) ∧
    3 / 5 ≤ ValAccept (lamJoint lam h0 h1) (uL (3 / 5)) astar := by
  have hb := branch_opt_of_reflection (hedged_reflection lam h0 h1) (uL (3 / 5)) astar hstar
  have hbr : ∀ i, S (lamJoint lam h0 h1) (uL (3 / 5)) (astar i) i = max (3 / 10) (1 / 4 + lam / 5) := by
    intro i
    have ha := hb i 0; have hb' := hb i 1; have hc := hb i 2
    rw [lam_S] at ha hb' hc
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at ha hb' hc
    have hmem : S (lamJoint lam h0 h1) (uL (3 / 5)) (astar i) i = (1 / 4 + lam / 5) ∨
        S (lamJoint lam h0 h1) (uL (3 / 5)) (astar i) i = (1 / 4 - lam / 5) ∨
        S (lamJoint lam h0 h1) (uL (3 / 5)) (astar i) i = 3 / 10 := by
      rw [lam_S]; generalize astar i = b; cases i <;> fin_cases b <;> simp
    apply le_antisymm
    · rcases hmem with h | h | h <;> rw [h]
      · exact le_max_right _ _
      · exact le_trans (by linarith) (le_max_right _ _)
      · exact le_max_left _ _
    · cases i
      · simp only [Bool.false_eq_true, if_false] at ha hb' hc; exact max_le hc hb'
      · simp only [if_true] at ha hb' hc; exact max_le hc ha
  have hV : ValAccept (lamJoint lam h0 h1) (uL (3 / 5)) astar = max (3 / 5) (1 / 2 + 2 * lam / 5) := by
    unfold ValAccept
    rw [Fintype.sum_bool, hbr, hbr, ← two_mul, mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
    congr 1 <;> ring
  exact ⟨hV, hV ▸ le_max_left _ _⟩

end

end Cleanroom.Corrigibility.CorrValueChange

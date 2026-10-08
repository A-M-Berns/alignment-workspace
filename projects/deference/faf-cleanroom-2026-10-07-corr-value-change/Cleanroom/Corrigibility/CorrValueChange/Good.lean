import Cleanroom.Corrigibility.CorrValueChange.Epist

/-!
# corr-value-change — Good's theorem for value change (T6, T9(a)(b), T10(e))

Source: [[value-change-as-epistemic-update]] §2.4 (Theorem 2.4, Claims 1–3), §2.7 (the act-value
form and the one-sided form), §3.4 (the grades). The two-step problem on `Ω × Θ × I`: the agent's
joint `J : Joint (Ω × Θ) I`, the installed states `Q : Installed (Ω × Θ) I`, the candidate
utilities `u`, and the acts. **Acts are independent of `(ω, θ, i)`** — the note's assumption,
stated as `act_independent_condExp` below: with the self-model `σ(a) > 0` and the joint
`P(x, a) = P(x) σ(a)`, `E[U ∣ a ∧ E] = E[U_a ∣ E]`, so every value below is written with `U_a`
and the act coordinate dropped.

Product forms: the **branch value** `S(a, i) = ∑_x P(x, i) u_{θ,a}(ω) = π_i · E[U_a ∣ E_i]`; then
`Val(decline) = ∑_i S(a^K, i) = E_P[U_{a^K}]` with `a^K` a `P`-maximizer, and
`Val(accept) = ∑_i S(a*_i, i) = ∑_i π_i E[U_{a*_i} ∣ E_i]` with `a*_i` a `Q_i`-maximizer. No
division appears in a headline; `branch_div` gives the division form on `π_i > 0`.
-/

namespace Cleanroom.Corrigibility.CorrValueChange

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω Θ I A : Type} [Fintype Ω] [Fintype Θ] [Fintype I] [Fintype A] [DecidableEq Ω]
  [DecidableEq Θ] [DecidableEq I] [DecidableEq A]

/-! ## The act-independence bridge -/

/-- The joint with an independent act coordinate: `P(x, a) = P(x) · σ(a)`.
Source: [[value-change-as-epistemic-update]] §2.4 ("we assume they are independent of
`(ω, θ, i)` under `P`")
Kind: D
Fidelity: exact -/
def withActs {X : Type} [Fintype X] (P : Prob X) (σ : A → ℝ) (hσ : ∀ a, 0 < σ a)
    (hσ1 : ∑ a, σ a = 1) : Prob (X × A) where
  p := fun y => P.p y.1 * σ y.2
  nonneg := fun y => mul_nonneg (P.nonneg y.1) (hσ y.2).le
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← mul_sum, hσ1, mul_one]
    exact P.sum_one

/-- **Acts carry no information** (the note's assumption, as a theorem about the product joint):
for the event "the agent does `a`" and any event `E` of the act-free worlds,
`E[U ∣ a ∧ E] = E[U_a ∣ E]`, i.e. `(∑_{x∈E} P(x) σ(a) U_a(x)) / (∑_{x∈E} P(x) σ(a)) =
(∑_{x∈E} P(x) U_a(x)) / P(E)`. Everything below is stated in the right-hand form.
Source: [[value-change-as-epistemic-update]] §2.4 ("so that `E_P[U ∣ a ∧ E] = E_P[U_a ∣ E]`")
Kind: P
Fidelity: exact
Hyps: (a) the product form of the joint (the independence assumption itself) -/
theorem act_independent_condExp {X : Type} [Fintype X] [DecidableEq X] (P : Prob X) (σ : A → ℝ)
    (hσ : ∀ a, 0 < σ a) (hσ1 : ∑ a, σ a = 1) (Ua : A → X → ℝ) (a : A) (E : Finset X) :
    (withActs P σ hσ hσ1).condExp (fun y => Ua y.2 y.1)
        ((univ.filter fun y : X × A => y.2 = a) ∩ (E ×ˢ univ)) =
      P.condExp (Ua a) E := by
  unfold Prob.condExp Prob.integral Prob.mass
  have hset : ((univ.filter fun y : X × A => y.2 = a) ∩ (E ×ˢ univ)) =
      (E ×ˢ univ).filter fun y : X × A => y.2 = a := by
    ext y; simp [and_comm]
  rw [hset, sum_filter, sum_filter, sum_product, sum_product]
  simp only [withActs]
  have h1 : ∀ x, (∑ b, if b = a then P.p x * σ b * Ua b x else 0) = σ a * (P.p x * Ua a x) := by
    intro x; rw [sum_ite_eq']; simp; ring
  have h2 : ∀ x, (∑ b, if b = a then P.p x * σ b else 0) = σ a * P.p x := by
    intro x; rw [sum_ite_eq']; simp; ring
  simp_rw [h1, h2]
  rw [← mul_sum, ← mul_sum, mul_div_mul_left _ _ (hσ a).ne']

/-! ## The decision model -/

/-- The **branch value** `S(a, i) = ∑_{(ω,θ)} P(ω, θ, i) u_{θ,a}(ω) = π_i · E_P[U_a ∣ E_i]`.
Source: [[value-change-as-epistemic-update]] §2.4 (`E_P[U_a ∣ E_i]`, product form)
Kind: D
Fidelity: exact -/
def S (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (a : A) (i : I) : ℝ :=
  ∑ x, J.P x i * Uplus u a x

/-- `E_P[U_a] = ∑_i S(a, i)`.
Source: [[value-change-as-epistemic-update]] §2.4
Kind: D
Fidelity: exact -/
def EU (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (a : A) : ℝ := ∑ i, S J u a i

/-- The installed agent's value of `a` in outcome `i`: `E_{Q_i}[U_a] = ∑_x Q_i(x) u_{θ,a}(ω)`.
Source: [[value-change-as-epistemic-update]] §2.4 (`a*_i ∈ argmax_a E_{Q_i}[U_a]`)
Kind: D
Fidelity: exact -/
def EQ (Q : Installed (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (i : I) (a : A) : ℝ :=
  ∑ x, Q.Q i x * Uplus u a x

/-- `Val(decline) = E_P[U_{a^K}]`, with `a^K` a `P`-maximizer (hypothesis-bearing).
Source: [[value-change-as-epistemic-update]] §2.4 (`Val(decline) = max_a E_P[U_a]`)
Kind: D
Fidelity: exact -/
def ValDecline (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (aK : A) : ℝ := EU J u aK

/-- `Val(accept) = ∑_i π_i E_P[U_{a*_i} ∣ E_i] = ∑_i S(a*_i, i)`.
Source: [[value-change-as-epistemic-update]] §2.4 (`Val(accept)` display)
Kind: D
Fidelity: exact -/
def ValAccept (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (astar : I → A) : ℝ :=
  ∑ i, S J u (astar i) i

/-- `E_P[U_a] = ∑_x P⁺(x) U_a(x)` (the marginal form).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem EU_eq_marg (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (a : A) :
    EU J u a = ∑ x, J.marg x * Uplus u a x := by
  unfold EU S Joint.marg
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_mul]

/-- **T6(b), the division form**: on `π_i > 0`, `S(a, i) = π_i · E[U_a ∣ E_i]` with
`E[U_a ∣ E_i] = S(a, i) / π_i`, so `Val(accept) = ∑_i π_i (S(a*_i, i)/π_i)` as displayed.
Source: [[value-change-as-epistemic-update]] §2.4
Kind: L
Fidelity: exact -/
theorem ValAccept_div (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (astar : I → A)
    (hπ : ∀ i, 0 < J.π i) :
    ValAccept J u astar = ∑ i, J.π i * (S J u (astar i) i / J.π i) := by
  unfold ValAccept
  refine sum_congr rfl fun i _ => ?_
  have := hπ i; field_simp

/-- Under (R⁺), the branch value is `π_i` times the installed value: `S(a, i) = π_i E_{Q_i}[U_a]`.
Source: [[value-change-as-epistemic-update]] §2.4 Claim 2 (first equality of the display)
Kind: L
Fidelity: exact -/
theorem S_eq_of_reflection {J : Joint (Ω × Θ) I} {Q : Installed (Ω × Θ) I}
    (h : Reflection J Q) (u : Θ → A → Ω → ℝ) (a : A) (i : I) :
    S J u a i = J.π i * EQ Q u i a := by
  unfold S EQ
  rcases (J.π_nonneg i).lt_or_eq with hpos | hzero
  · rw [mul_sum]; refine sum_congr rfl fun x _ => ?_; rw [h i hpos x]; ring
  · rw [← hzero, zero_mul]
    exact sum_eq_zero fun x _ => by rw [J.P_eq_zero_of_π_eq_zero hzero.symm x, zero_mul]

/-- Under (R⁺) the installed choice is branch-optimal: `S(a, i) ≤ S(a*_i, i)` for every `a`.
(This is "`Val(accept) = ∑_i π_i max_a E[U_a ∣ E_i]`".)
Source: [[value-change-as-epistemic-update]] §2.4 Claim 2
Kind: L
Fidelity: exact -/
theorem branch_opt_of_reflection {J : Joint (Ω × Θ) I} {Q : Installed (Ω × Θ) I}
    (h : Reflection J Q) (u : Θ → A → Ω → ℝ) (astar : I → A)
    (hstar : ∀ i a, EQ Q u i a ≤ EQ Q u i (astar i)) (i : I) (a : A) :
    S J u a i ≤ S J u (astar i) i := by
  rw [S_eq_of_reflection h, S_eq_of_reflection h]
  exact mul_le_mul_of_nonneg_left (hstar i a) (J.π_nonneg i)

/-- **Claim 2, Good's theorem for value change**: under (R⁺), `Val(accept) ≥ Val(decline)` —
`∑_i π_i max_a E[U_a ∣ E_i] ≥ max_a ∑_i π_i E[U_a ∣ E_i]`, proved as the note does: condition on
`E_i` (`S_eq_of_reflection`, `branch_opt_of_reflection`), then sum.
Source: [[value-change-as-epistemic-update]] §2.4 Claim 2
Kind: P
Fidelity: exact (stronger: the inequality holds for every `a^K`, not only `E_P`-maximizers — `hK` is
carried for the statement's reading and not used)
Hyps: (a) `h : Reflection`, `hstar : a*_i` maximizes `E_{Q_i}`, `hK : a^K` maximizes `E_P` (unused) -/
theorem good_theorem {J : Joint (Ω × Θ) I} {Q : Installed (Ω × Θ) I} (h : Reflection J Q)
    (u : Θ → A → Ω → ℝ) (astar : I → A) (aK : A)
    (hstar : ∀ i a, EQ Q u i a ≤ EQ Q u i (astar i)) (_hK : ∀ a, EU J u a ≤ EU J u aK) :
    ValDecline J u aK ≤ ValAccept J u astar := by
  unfold ValDecline ValAccept EU
  exact sum_le_sum fun i _ => branch_opt_of_reflection h u astar hstar i aK

/-- A sum of termwise-dominated reals is strictly dominated iff some term is.
Source: none: infrastructure (audit r3 adversarial N2)
Kind: L
Fidelity: n/a -/
theorem sum_lt_sum_iff_of_le {ι : Type} [Fintype ι] (x y : ι → ℝ) (h : ∀ i, x i ≤ y i) :
    ∑ i, x i < ∑ i, y i ↔ ∃ i, x i < y i := by
  constructor
  · intro hlt
    by_contra hall
    push_neg at hall
    exact absurd hlt (not_lt.2 (sum_le_sum fun i _ => hall i))
  · rintro ⟨i, hi⟩
    exact sum_lt_sum (fun j _ => h j) ⟨i, mem_univ i, hi⟩

/-- **Claim 2, strictness (corrected)**: under (R⁺), `Val(accept) > Val(decline)` **iff the
status-quo act `a^K` fails to be branch-optimal in some outcome**, `S(a^K, i) < S(a*_i, i)` for
some `i` (equivalently `E[U_{a^K} ∣ E_i] < E[U_{a*_i} ∣ E_i]` with `π_i > 0`). The note's clause
"iff the acts `a*_i` are not all optimal under `P`" is false in both directions with ties
(findings F2; `strict_clause_left_fails`, `strict_clause_right_fails` in `Variants.lean`); it holds
under uniqueness of maximizers (`good_theorem_strict_iff_of_unique`).
Source: [[value-change-as-epistemic-update]] §2.4 Claim 2 ("with strict inequality iff …")
Kind: C (reflection enters only through branch optimality, `branch_opt_of_reflection`; given that,
the iff is the arithmetic `sum_lt_sum_iff_of_le`: audit r3 adversarial N2)
Fidelity: variant: the clause corrected (the note's is refuted)
Hyps: (a) `h`, `hstar`, `hK` (unused: the equivalence holds for every `a^K`) -/
theorem good_theorem_strict_iff {J : Joint (Ω × Θ) I} {Q : Installed (Ω × Θ) I}
    (h : Reflection J Q) (u : Θ → A → Ω → ℝ) (astar : I → A) (aK : A)
    (hstar : ∀ i a, EQ Q u i a ≤ EQ Q u i (astar i)) (_hK : ∀ a, EU J u a ≤ EU J u aK) :
    ValDecline J u aK < ValAccept J u astar ↔ ∃ i, S J u aK i < S J u (astar i) i := by
  unfold ValDecline ValAccept EU
  exact sum_lt_sum_iff_of_le _ _ fun i => branch_opt_of_reflection h u astar hstar i aK

/-- **The note's strictness clause, under uniqueness of maximizers**: if the `P`-maximizer is
unique and the branch maximizers are unique on positive-probability outcomes, then under (R⁺)
`Val(accept) > Val(decline)` iff some `a*_i` with `π_i > 0` is not `P`-optimal. (The restriction to
`π_i > 0` is also needed: on a null outcome `a*_i` is unconstrained.)
Source: [[value-change-as-epistemic-update]] §2.4 Claim 2
Kind: P
Fidelity: weaker: the note's clause under added uniqueness hypotheses
Hyps: (a) `h`, `hstar`, `hK`; `hUK`, `hUB`: uniqueness of maximizers (not in the note) -/
theorem good_theorem_strict_iff_of_unique {J : Joint (Ω × Θ) I} {Q : Installed (Ω × Θ) I}
    (h : Reflection J Q) (u : Θ → A → Ω → ℝ) (astar : I → A) (aK : A)
    (hstar : ∀ i a, EQ Q u i a ≤ EQ Q u i (astar i)) (hK : ∀ a, EU J u a ≤ EU J u aK)
    (hUK : ∀ a, EU J u a = EU J u aK → a = aK)
    (hUB : ∀ i a, 0 < J.π i → S J u a i = S J u (astar i) i → a = astar i) :
    ValDecline J u aK < ValAccept J u astar ↔
      ∃ i, 0 < J.π i ∧ ¬ ∀ a, EU J u a ≤ EU J u (astar i) := by
  rw [good_theorem_strict_iff h u astar aK hstar hK]
  constructor
  · rintro ⟨i, hi⟩
    have hπ : 0 < J.π i := by
      rcases (J.π_nonneg i).lt_or_eq with hp | hz
      · exact hp
      · exfalso
        have h0 : ∀ a, S J u a i = 0 := fun a =>
          sum_eq_zero fun x _ => by rw [J.P_eq_zero_of_π_eq_zero hz.symm x, zero_mul]
        rw [h0, h0] at hi; exact lt_irrefl 0 hi
    refine ⟨i, hπ, fun hopt => ?_⟩
    have hne : astar i ≠ aK := fun heq => by rw [heq] at hi; exact lt_irrefl _ hi
    have heq : EU J u (astar i) = EU J u aK := le_antisymm (hK _) (hopt aK)
    exact hne (hUK _ heq)
  · rintro ⟨i, hπ, hnot⟩
    have hne : astar i ≠ aK := fun heq => hnot (by rw [heq]; exact hK)
    refine ⟨i, lt_of_le_of_ne (branch_opt_of_reflection h u astar hstar i aK) fun heq => ?_⟩
    exact hne (hUB i aK hπ heq).symm

/-- **Claim 1, known target (first half)**: if the installed choice is one fixed act `a*` (in the
note, the maximizer of the one installed state `Q`; the statement carries no `Q` — nothing about
it could matter), then `Val(accept) = E_P[U_{a*}] ≤ Val(decline)`, whatever the agent thinks of the
source (no reflection assumed). The content is the note's own one-liner: `Val(accept)` is a plain
expectation and `a^K` maximizes those. The constancy of the choice is the tie convention the note
leaves implicit (F3); the second half (`known_target_reflection`) is where the content lies.
Source: [[value-change-as-epistemic-update]] §2.4 Claim 1
Kind: L (the first conjunct is definitional, the second is `hK` at `a*`; audit r1, N3)
Fidelity: exact (with the choice constant, as the note says "one fixed act")
Hyps: (a) `hK : a^K` maximizes `E_P` -/
theorem known_target (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (astar aK : A)
    (hK : ∀ a, EU J u a ≤ EU J u aK) :
    ValAccept J u (fun _ => astar) = EU J u astar ∧ ValAccept J u (fun _ => astar) ≤ ValDecline J u aK := by
  unfold ValAccept ValDecline EU
  exact ⟨rfl, hK astar⟩

/-- **Claim 1, second half**: with a constant installed state `Q₀` and (R⁺), the marginal `P⁺`
*is* `Q₀` (literally, on `Ω⁺`: `Reflection.marg_eq_of_const`), so `E_P[U_a] = E_{Q₀}[U_a]`, a
`Q₀`-maximizer is a `P`-maximizer, and `Val(accept) = Val(decline)`: the modification is null.
Source: [[value-change-as-epistemic-update]] §2.4 Claim 1 ("(R⁺) with a constant target gives
`P = Q` and the modification is null"); mandate Known issues 2
Kind: P
Fidelity: exact
Hyps: (a) `h : Reflection`, `hc : Q_i = Q₀`, `hstar : a*` maximizes `E_{Q₀}`, `hK` -/
theorem known_target_reflection {J : Joint (Ω × Θ) I} {Q : Installed (Ω × Θ) I}
    (h : Reflection J Q) (u : Θ → A → Ω → ℝ) (Q₀ : Ω × Θ → ℝ) (hc : ∀ i x, Q.Q i x = Q₀ x)
    (astar aK : A) (hstar : ∀ a, ∑ x, Q₀ x * Uplus u a x ≤ ∑ x, Q₀ x * Uplus u astar x)
    (hK : ∀ a, EU J u a ≤ EU J u aK) :
    (∀ x, J.marg x = Q₀ x) ∧ ValAccept J u (fun _ => astar) = ValDecline J u aK := by
  have hm := h.marg_eq_of_const Q₀ hc
  refine ⟨hm, ?_⟩
  have hEU : ∀ a, EU J u a = ∑ x, Q₀ x * Uplus u a x := by
    intro a; rw [EU_eq_marg]; simp_rw [hm]
  unfold ValAccept ValDecline
  show ∑ i, S J u astar i = EU J u aK
  change EU J u astar = EU J u aK
  apply le_antisymm (hK astar)
  rw [hEU, hEU]; exact hstar aK

/-! ## The choice term (A) and the grades -/

/-- Term **(A)** in the epistemic model: `∑_i [S(a*_i, i) − S(â_i, i)]` with `â_i` branch-optimal
— the §1.4 choice term with `p_j = π_i` and `v_j = E[U_· ∣ E_i]`, times `P(C) = 1` here.
Source: [[value-change-as-epistemic-update]] §2.4 ("In the terms of §1.4: (R⁺) makes term (A)
vanish"), §3.4
Kind: D
Fidelity: exact -/
def termAep (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (astar ahat : I → A) : ℝ :=
  ∑ i, (S J u (astar i) i - S J u (ahat i) i)

/-- (A) ≤ 0 from `â_i` branch-optimal.
Source: [[value-change-as-epistemic-update]] §1.4, §2.6
Kind: P
Fidelity: exact
Hyps: (a) `hhat` -/
theorem termAep_nonpos (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (astar ahat : I → A)
    (hhat : ∀ i a, S J u a i ≤ S J u (ahat i) i) : termAep J u astar ahat ≤ 0 :=
  sum_nonpos fun i _ => by linarith [hhat i (astar i)]

/-- (A) = 0 iff every installed choice is branch-optimal.
Source: [[value-change-as-epistemic-update]] §3.4
Kind: P
Fidelity: exact
Hyps: (a) `hhat` -/
theorem termAep_eq_zero_iff (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (astar ahat : I → A)
    (hhat : ∀ i a, S J u a i ≤ S J u (ahat i) i) :
    termAep J u astar ahat = 0 ↔ ∀ i a, S J u a i ≤ S J u (astar i) i := by
  unfold termAep
  have hnn : ∀ i ∈ (univ : Finset I), 0 ≤ S J u (ahat i) i - S J u (astar i) i :=
    fun i _ => by linarith [hhat i (astar i)]
  have hneg : ∑ i, (S J u (astar i) i - S J u (ahat i) i) =
      -∑ i, (S J u (ahat i) i - S J u (astar i) i) := by
    rw [← sum_neg_distrib]; refine sum_congr rfl fun i _ => ?_; ring
  rw [hneg, neg_eq_zero, sum_eq_zero_iff_of_nonneg hnn]
  constructor
  · intro h i a
    have := h i (mem_univ i)
    linarith [hhat i a]
  · intro h i _
    linarith [h i (ahat i), hhat i (astar i)]

/-- **(R⁺) ⇒ (A) = 0**: under reflection the installed choice is the informed old-`U` choice.
Source: [[value-change-as-epistemic-update]] §2.4 ("(R⁺) makes term (A) vanish"), §3.4
Kind: P
Fidelity: exact
Hyps: (a) `h`, `hstar`, `hhat` -/
theorem reflection_imp_termAep_zero {J : Joint (Ω × Θ) I} {Q : Installed (Ω × Θ) I}
    (h : Reflection J Q) (u : Θ → A → Ω → ℝ) (astar ahat : I → A)
    (hstar : ∀ i a, EQ Q u i a ≤ EQ Q u i (astar i))
    (hhat : ∀ i a, S J u a i ≤ S J u (ahat i) i) : termAep J u astar ahat = 0 :=
  (termAep_eq_zero_iff J u astar ahat hhat).2 (branch_opt_of_reflection h u astar hstar)

/-- **`Val(accept) − Val(decline) = (A) + gain`** with `gain = ∑_i S(â_i, i) − E_P[U_{a^K}] ≥ 0`
(Good's theorem for the informed old-`U` choices); so (A) = 0 ⇒ net-positive.
Source: [[value-change-as-epistemic-update]] §3.4 ("(A) vanishes … and (B) is Good's theorem")
Kind: P
Fidelity: exact
Hyps: (a) `hhat` -/
theorem ValAccept_sub_ValDecline (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (astar ahat : I → A)
    (aK : A) (hhat : ∀ i a, S J u a i ≤ S J u (ahat i) i) :
    ValAccept J u astar - ValDecline J u aK =
        termAep J u astar ahat + ((∑ i, S J u (ahat i) i) - ValDecline J u aK) ∧
      0 ≤ (∑ i, S J u (ahat i) i) - ValDecline J u aK := by
  constructor
  · unfold termAep ValAccept; rw [sum_sub_distrib]; ring
  · unfold ValDecline EU
    have := sum_le_sum fun i (_ : i ∈ univ) => hhat i aK
    linarith

/-- **(A) = 0 ⇒ net-positive.**
Source: [[value-change-as-epistemic-update]] §3.4
Kind: C
Fidelity: exact
Hyps: (a) `hhat`, `hA` -/
theorem net_nonneg_of_termAep_zero (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (astar ahat : I → A)
    (aK : A) (hhat : ∀ i a, S J u a i ≤ S J u (ahat i) i) (hA : termAep J u astar ahat = 0) :
    ValDecline J u aK ≤ ValAccept J u astar := by
  obtain ⟨h1, h2⟩ := ValAccept_sub_ValDecline J u astar ahat aK hhat
  linarith

/-- **T10(e), the grades as four implications** (the mandate's chain): (R⁺) ⇒ (R⁺∣⊤) ⇒ (A) = 0 ⇒
net-positive. (The note's §3.4 chain, with "(R⁺∣L)" for a general `L` as the second grade, is
false at that link: findings F4, `CondLegit.lean`.)
Source: [[value-change-as-epistemic-update]] §3.4; mandate T10(e)
Kind: C
Fidelity: exact for the chain as the mandate states it
Hyps: (a) `hstar`, `hhat` -/
theorem grades_chain {J : Joint (Ω × Θ) I} {Q : Installed (Ω × Θ) I} (u : Θ → A → Ω → ℝ)
    (astar ahat : I → A) (aK : A) (hstar : ∀ i a, EQ Q u i a ≤ EQ Q u i (astar i))
    (hhat : ∀ i a, S J u a i ≤ S J u (ahat i) i) :
    (Reflection J Q → CondReflection J Q univ) ∧
    (CondReflection J Q univ → termAep J u astar ahat = 0) ∧
    (termAep J u astar ahat = 0 → ValDecline J u aK ≤ ValAccept J u astar) :=
  ⟨fun h => (condReflection_univ_iff J Q).2 h,
   fun h => reflection_imp_termAep_zero ((condReflection_univ_iff J Q).1 h) u astar ahat hstar hhat,
   fun h => net_nonneg_of_termAep_zero J u astar ahat aK hhat h⟩

/-! ## T9(a): the act-value form of Good's theorem -/

/-- The installed act-value vector `V(i) = (E_{Q_i}[U_a])_a`, a random variable of the outcome.
Source: [[value-change-as-epistemic-update]] §2.7 (`V_a := E_1[U_a]`)
Kind: D
Fidelity: exact -/
def Vvec (Q : Installed (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (i : I) : A → ℝ := fun a => EQ Q u i a

/-- The cell of the partition of `I` generated by the act-value vector: `{j ∣ V(j) = V(i)}`.
Source: [[value-change-as-epistemic-update]] §2.7 ("conditioning on `(V_b)_b`")
Kind: D
Fidelity: exact (conditioning on the partition generated by the finitely many values) -/
def Vcell (Q : Installed (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (i : I) : Finset I :=
  univ.filter fun j => Vvec Q u j = Vvec Q u i

/-- **Act-value reflection**: `E_0[U_a ∣ (V_b)_b] = V_a` for every `a`, i.e. on every cell of the
partition generated by the vector, in product form:
`∑_{j ∈ cell(i)} S(a, j) = V_a(i) · ∑_{j ∈ cell(i)} π_j`. (On a null cell both sides are `0`, so
no positivity guard is needed.)
Source: [[value-change-as-epistemic-update]] §2.7 ("reflection holds for the act values jointly")
Kind: D
Fidelity: exact -/
def ActValueReflection (J : Joint (Ω × Θ) I) (Q : Installed (Ω × Θ) I) (u : Θ → A → Ω → ℝ) :
    Prop :=
  ∀ a i, ∑ j ∈ Vcell Q u i, S J u a j = Vvec Q u i a * ∑ j ∈ Vcell Q u i, J.π j

/-- **(R⁺) implies act-value reflection**: under reflection `S(a, j) = π_j V_a(j)`
(`S_eq_of_reflection`), and on the cell of `i` every `V_a(j)` equals `V_a(i)`, so
`∑_{j ∈ cell(i)} S(a, j) = V_a(i) ∑_{j ∈ cell(i)} π_j`. With `act_value_beyond_reflection`
(`Modest.lean`: act-value reflection with (R⁺) and (M⁺) both failing) this makes act-value
reflection a *strictly* weaker hypothesis than (R⁺), so `act_value_good` strictly generalizes
`good_theorem` whenever the installed choice is a function of the value vector.
Source: [[value-change-as-epistemic-update]] §2.7 (the act-value form is offered as the weaker
condition "with no mention of the installed state"); repair r3
Kind: P
Fidelity: exact
Hyps: (a) `h : Reflection` -/
theorem actValueReflection_of_reflection {J : Joint (Ω × Θ) I} {Q : Installed (Ω × Θ) I}
    (h : Reflection J Q) (u : Θ → A → Ω → ℝ) : ActValueReflection J Q u := by
  intro a i
  rw [mul_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [S_eq_of_reflection h u a j]
  have hv : Vvec Q u j = Vvec Q u i := (mem_filter.1 hj).2
  rw [← hv]
  unfold Vvec
  ring

/-- **T9(a), the act-value form of Good's theorem**: if act-value reflection holds and the
installed choice `a*` is a function of the vector (`V(i) = V(j) ⇒ a*_i = a*_j`, the note's "since
`a*` is a function of the vector"; with ties this is a convention, cf. F3) maximizing it, then
`E_0[U_{a*}] = Val(accept) ≥ max_a E_0[U_a] = Val(decline)`. `hfac` is load-bearing, not
decoration: `act_value_hfac_needed` (`Modest.lean`) has every other hypothesis and the
conclusion false, so the note's "since" is the tie convention, not a consequence. Proved by conditioning on the
`V`-cells and the tower property, as the note does, from reflection on `|𝒜|` expected values and
no mention of the installed state.
Source: [[value-change-as-epistemic-update]] §2.7 (the display)
Kind: P
Fidelity: exact
Hyps: (a) `hR : ActValueReflection`, `hfac`, `hstar`, `hK` -/
theorem act_value_good (J : Joint (Ω × Θ) I) (Q : Installed (Ω × Θ) I) (u : Θ → A → Ω → ℝ)
    (astar : I → A) (aK : A) (hR : ActValueReflection J Q u)
    (hfac : ∀ i j, Vvec Q u i = Vvec Q u j → astar i = astar j)
    (hstar : ∀ i a, Vvec Q u i a ≤ Vvec Q u i (astar i)) (_hK : ∀ a, EU J u a ≤ EU J u aK) :
    ValDecline J u aK ≤ ValAccept J u astar := by
  unfold ValDecline ValAccept EU
  -- group both sums by the cells of the vector
  have hgroup : ∀ f : I → ℝ, ∑ i, f i =
      ∑ v ∈ univ.image (Vvec Q u), ∑ i ∈ univ.filter (fun i => Vvec Q u i = v), f i := by
    intro f
    rw [sum_fiberwise_of_maps_to (g := Vvec Q u) (t := univ.image (Vvec Q u))]
    intro i _; exact mem_image_of_mem _ (mem_univ i)
  rw [hgroup, hgroup (fun i => S J u (astar i) i)]
  apply sum_le_sum
  intro v hv
  obtain ⟨i₀, _, hi₀⟩ := mem_image.1 hv
  have hcell : (univ.filter fun i => Vvec Q u i = v) = Vcell Q u i₀ := by
    unfold Vcell; rw [hi₀]
  rw [hcell]
  -- on the cell, `a*` is constant
  have hconst : ∀ j ∈ Vcell Q u i₀, astar j = astar i₀ := by
    intro j hj
    have : Vvec Q u j = Vvec Q u i₀ := by simpa [Vcell] using hj
    exact hfac j i₀ this
  have hc : ∑ j ∈ Vcell Q u i₀, S J u (astar j) j = ∑ j ∈ Vcell Q u i₀, S J u (astar i₀) j :=
    sum_congr rfl fun j hj => by rw [hconst j hj]
  rw [hc, hR (astar i₀) i₀, hR aK i₀]
  apply mul_le_mul_of_nonneg_right (hstar i₀ aK)
  exact sum_nonneg fun j _ => J.π_nonneg j

/-! ## T9(b): the one-sided form conditions on the sure event (F10) -/

/-- `X = U_{a*} − U_{a^K}` as a random variable of `(x, i)`.
Source: [[value-change-as-epistemic-update]] §2.7 (the one-sided form)
Kind: D
Fidelity: exact -/
def Xdiff (u : Θ → A → Ω → ℝ) (astar : I → A) (aK : A) (x : Ω × Θ) (i : I) : ℝ :=
  Uplus u (astar i) x - Uplus u aK x

/-- `E_1 X ≥ 0` in **every** outcome by the choice of `a*_i`: the conditioning event
`{E_1 X ≥ 0}` of the one-sided form is the sure event.
Source: [[value-change-as-epistemic-update]] §2.7 ("`E_1[U_{a*} − U_b] ≥ 0` for every `b` by
construction"); findings F10
Kind: L
Fidelity: exact -/
theorem one_sided_event_univ (Q : Installed (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (astar : I → A)
    (aK : A) (hstar : ∀ i a, EQ Q u i a ≤ EQ Q u i (astar i)) :
    (univ.filter fun i => 0 ≤ ∑ x, Q.Q i x * Xdiff u astar aK x i) = univ := by
  ext i; simp only [mem_filter, mem_univ, true_and, iff_true]
  unfold Xdiff
  have : ∑ x, Q.Q i x * (Uplus u (astar i) x - Uplus u aK x) = EQ Q u i (astar i) - EQ Q u i aK := by
    unfold EQ; rw [← sum_sub_distrib]; refine sum_congr rfl fun x _ => ?_; ring
  rw [this]; linarith [hstar i aK]

/-- **F10: the one-sided condition is the conclusion.** `E_0[X ∣ E_1 X ≥ 0] ≥ 0`, with the event
the sure event, is `E_0[X] ≥ 0`, which is `Val(accept) ≥ Val(decline)` by rearrangement. Kind S
by design: the theorem records that the note's sentence restates its conclusion rather than
deriving it from a trust principle.
Source: [[value-change-as-epistemic-update]] §2.7 ("is exactly `Val(accept) ≥ Val(decline)`")
Kind: S
Fidelity: exact (and that is the finding)
Hyps: (a) `hstar` -/
theorem one_sided_is_conclusion (J : Joint (Ω × Θ) I) (Q : Installed (Ω × Θ) I)
    (u : Θ → A → Ω → ℝ) (astar : I → A) (aK : A)
    (hstar : ∀ i a, EQ Q u i a ≤ EQ Q u i (astar i)) :
    (0 ≤ ∑ i ∈ univ.filter (fun i => 0 ≤ ∑ x, Q.Q i x * Xdiff u astar aK x i),
        ∑ x, J.P x i * Xdiff u astar aK x i) ↔
      ValDecline J u aK ≤ ValAccept J u astar := by
  rw [one_sided_event_univ Q u astar aK hstar]
  unfold ValDecline ValAccept EU S Xdiff
  have : ∑ i, ∑ x, J.P x i * (Uplus u (astar i) x - Uplus u aK x) =
      ∑ i, ∑ x, J.P x i * Uplus u (astar i) x - ∑ i, ∑ x, J.P x i * Uplus u aK x := by
    rw [← sum_sub_distrib]; refine sum_congr rfl fun i _ => ?_
    rw [← sum_sub_distrib]; refine sum_congr rfl fun x _ => ?_; ring
  rw [this]; constructor <;> intro h <;> linarith

end

end Cleanroom.Corrigibility.CorrValueChange

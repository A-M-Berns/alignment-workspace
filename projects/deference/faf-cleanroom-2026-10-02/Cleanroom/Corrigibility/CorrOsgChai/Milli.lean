import Cleanroom.Corrigibility.CorrOsgChai.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# Milli et al. 2017, "Should robots be obedient?" — the finite supervision model (D6, T5(a)–(d))

Package `corr-osg-chai`. **D6**: a finite `Θ` with a prior (FAF's `Distr`), finite actions `A`, a
reward `R : Θ → A → ℝ` (the paper's `θᵀφ(a)` is the linear special case; nothing here needs
linearity), and a human kernel `πH : Θ → Distr A` producing the order. The posterior after one
order is kept in product form (`post θ o = prior θ · πH θ o`, unnormalised); the posterior-mean
objective is `Q o a = ∑ θ, post θ o · R θ a`. Obedience `O = ∑ θ o, post θ o · 𝟙[πR o = o]`;
autonomy advantage `Δ = ∑ θ o, post θ o · (R θ (πR o) − R θ o)`.

The paper's `π^R_*(h) = argmax` is a `Classical.choice` junk value on ties, so every obedience
statement here is "the order is a maximiser of the posterior objective"; "`π^R_* = π^R_O`"
follows only under Theorem 2's explicit tie-break (`TieBreakObedient`: R picks the order when
the order is optimal), stated as the hypothesis it is.

* **Remark 1** (`advantage_eq_zero_of_obedience_eq_one`, `obedience_lt_one_of_advantage_pos`):
  `O = 1 → Δ = 0`, hence `0 < Δ → O < 1`.
* **Theorem 1** (`advantage_nonneg`, `advantage_eq_zero_iff`): the posterior-mean robot has
  `Δ ≥ 0` — each order's summand `Q o (πR o) − Q o o ≥ 0` because `πR o` maximises `Q o` (the
  tower); `Δ = 0` iff every order is a maximiser of its posterior objective (positive-mass or
  not — a null order's objective is identically `0`), which is `π^R_* = π^R_O` under the
  tie-break (`advantage_eq_zero_iff_obedient_of_tieBreak`).
* **Theorem 3 (⇐)** (`order_maximises_of_rational`, `blindlyObedient_of_rational`): a rational
  human (every positive-probability order maximises `R θ`) makes every order a maximiser of the
  posterior objective (the support argument), so under the tie-break the optimal robot is
  blindly obedient (`O = 1`). The (⇒) direction rests on Diaconis–Freedman consistency and is
  recorded, not stated (mandate T5(e), stretch).
* **Lemma 1** (`undominated_of_isIRL`): an IRL robot executes `o` only if `o` is undominated
  (kind L: the definitions coincide), with the paper's three-action `(−1,−1), (0,0), (1,1)`
  example as N+ (`milliExample_middle_dominated`: the middle order is dominated for every
  `θ ∈ {(1,0), (−1,0)}`, so no IRL robot executes it).

Sources: `04-chai/milli-2017-should-robots-be-obedient.md` l. 75 (obedience), 145 (advantage,
Remark 1, Theorem 1), 151 (Theorem 2's tie-break), 157 (Theorem 3), 187 (Lemma 1).
-/

namespace Cleanroom.Corrigibility.CorrOsgChai

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

set_option linter.unusedSectionVars false

/-- **D6: the finite supervision model.** A prior on the reward parameter, a reward `R θ a`, and
the human's order kernel `πH θ`.
Source: Milli et al. 2017 §2 (the finite shadow; `θᵀφ(a)` is the linear special case)
Kind: D
Fidelity: variant: general `R : Θ → A → ℝ` in place of `θᵀφ(a)` (nothing below needs linearity)
Hyps: n/a (definition) -/
structure Supervision (Θ A : Type) [Fintype Θ] [Fintype A] where
  /-- the prior over `Θ` -/
  prior : Distr Θ
  /-- the reward of action `a` under parameter `θ` -/
  R : Θ → A → ℝ
  /-- the human's order kernel -/
  πH : Θ → Distr A

namespace Supervision

variable {Θ A : Type} [Fintype Θ] [Fintype A] [DecidableEq A] (M : Supervision Θ A)

/-- The unnormalised posterior after order `o`: `prior θ · πH θ o` (product form).
Source: Milli et al. 2017 §2 (`P(θ | h)` after one order)
Kind: D
Fidelity: exact (unnormalised) -/
noncomputable def post (θ : Θ) (o : A) : ℝ := M.prior.mass θ * (M.πH θ).mass o

/-- The posterior-mean objective `Q o a = ∑ θ, post θ o · R θ a` (`E[φ(a)ᵀθ | h]` times the
order's mass).
Source: Milli et al. 2017 Theorem 1's proof (`max_a E[φ_n(a)ᵀθ | h]`)
Kind: D
Fidelity: exact (unnormalised) -/
noncomputable def Q (o a : A) : ℝ := ∑ θ, M.post θ o * M.R θ a

/-- **Obedience** `O = P(πR(o) = o) = ∑ θ o, post θ o · 𝟙[πR o = o]`.
Source: Milli et al. 2017 l. 75 (`O_n = P(π_R(h) = o_n)`)
Kind: D
Fidelity: exact -/
noncomputable def obedience (πR : A → A) : ℝ :=
  ∑ θ, ∑ o, M.post θ o * (if πR o = o then 1 else 0)

/-- **Autonomy advantage** `Δ = E[R(πR(o)) − R(o)] = ∑ θ o, post θ o · (R θ (πR o) − R θ o)`.
Source: Milli et al. 2017 l. 145 (`Δ_n = E[R(s_n, π_R(h)) − R(s_n, o_n)]`)
Kind: D
Fidelity: exact -/
noncomputable def advantage (πR : A → A) : ℝ :=
  ∑ θ, ∑ o, M.post θ o * (M.R θ (πR o) - M.R θ o)

/-- **The posterior-mean robot**: `πR o` maximises the posterior objective `Q o`.
Source: Milli et al. 2017 Theorem 1 (`π^R_*`)
Kind: D
Fidelity: exact (as a predicate, not an `argmax` junk value) -/
def IsPosteriorMean (πR : A → A) : Prop := ∀ o a, M.Q o a ≤ M.Q o (πR o)

/-- **Theorem 2's tie-break**: the robot picks the order whenever the order is optimal.
Source: Milli et al. 2017 Theorem 2 ("when there are multiple optimal actions R picks H's order
if it is optimal")
Kind: D
Fidelity: exact -/
def TieBreakObedient (πR : A → A) : Prop := ∀ o, (∀ a, M.Q o a ≤ M.Q o o) → πR o = o

/-- **A rational human**: every order of positive probability under `θ` maximises `R θ`.
Source: Milli et al. 2017 §2 (`π_H^*`, the rational human)
Kind: D
Fidelity: exact -/
def Rational : Prop := ∀ θ o, (M.πH θ).mass o ≠ 0 → ∀ a, M.R θ a ≤ M.R θ o

/-- **Undominated** (Lemma 1): some `θ` makes `o` optimal.
Source: Milli et al. 2017 Lemma 1 (l. 187)
Kind: D
Fidelity: exact -/
def Undominated (o : A) : Prop := ∃ θ, ∀ a, M.R θ a ≤ M.R θ o

/-- **An IRL robot** (Lemma 1's class): each executed action is optimal for some estimate `θ̂`.
Source: Milli et al. 2017 Eq. 2 / Lemma 1
Kind: D
Fidelity: exact -/
def IsIRL (πR : A → A) : Prop := ∀ o, ∃ θh, ∀ a, M.R θh a ≤ M.R θh (πR o)

/-- The posterior masses sum to one. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_post (M : Supervision Θ A) : ∑ θ, ∑ o, M.post θ o = 1 := by
  simp only [post, ← mul_sum, Distr.sum_eq_one, mul_one]

/-- Posterior masses are nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma post_nonneg (θ : Θ) (o : A) : 0 ≤ M.post θ o :=
  mul_nonneg (M.prior.nonneg θ) ((M.πH θ).nonneg o)

/-- **Remark 1: a fully obedient robot has no advantage.** `O = 1` means the disobedient orders
carry no mass, and on obedient orders the advantage summand is `0`.
Source: Milli et al. 2017 Remark 1 (l. 145, "whenever R is obedient Δ = 0")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem advantage_eq_zero_of_obedience_eq_one (πR : A → A) (h : M.obedience πR = 1) :
    M.advantage πR = 0 := by
  -- the mass on disobedient orders is zero
  have hdis : ∑ θ, ∑ o, M.post θ o * (if πR o = o then 0 else 1) = 0 := by
    have h1 : ∑ θ, ∑ o, M.post θ o * (if πR o = o then 1 else 0) +
        ∑ θ, ∑ o, M.post θ o * (if πR o = o then 0 else 1) = 1 := by
      calc _ = ∑ θ, ∑ o, M.post θ o := by
            rw [← sum_add_distrib]
            refine sum_congr rfl fun θ _ => ?_
            rw [← sum_add_distrib]
            refine sum_congr rfl fun o _ => ?_
            split_ifs <;> ring
        _ = 1 := M.sum_post
    rw [obedience] at h
    linarith
  have hterm : ∀ θ ∈ (univ : Finset Θ), ∀ o ∈ (univ : Finset A),
      M.post θ o * (if πR o = o then 0 else 1) = 0 := by
    intro θ _ o _
    have := (sum_eq_zero_iff_of_nonneg fun θ _ => sum_nonneg fun o _ =>
      mul_nonneg (M.post_nonneg θ o) (by split_ifs <;> norm_num)).mp hdis θ (mem_univ θ)
    exact (sum_eq_zero_iff_of_nonneg fun o _ =>
      mul_nonneg (M.post_nonneg θ o) (by split_ifs <;> norm_num)).mp this o (mem_univ o)
  unfold advantage
  refine sum_eq_zero fun θ hθ => sum_eq_zero fun o ho => ?_
  have := hterm θ hθ o ho
  by_cases hob : πR o = o
  · rw [hob, sub_self, mul_zero]
  · rw [if_neg hob, mul_one] at this
    rw [this, zero_mul]

/-- **Remark 1, contrapositive**: any advantage requires some disobedience.
Source: Milli et al. 2017 Remark 1 (`Δ > 0 ⟹ O < 1`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem obedience_lt_one_of_advantage_pos (πR : A → A) (h : 0 < M.advantage πR) :
    M.obedience πR < 1 := by
  by_contra hle
  push Not at hle
  have hle1 : M.obedience πR ≤ 1 := by
    unfold obedience
    calc ∑ θ, ∑ o, M.post θ o * (if πR o = o then 1 else 0) ≤ ∑ θ, ∑ o, M.post θ o :=
          sum_le_sum fun θ _ => sum_le_sum fun o _ => by
            have := M.post_nonneg θ o
            split_ifs <;> nlinarith
      _ = 1 := M.sum_post
  have := M.advantage_eq_zero_of_obedience_eq_one πR (le_antisymm hle1 hle)
  linarith

/-- The advantage is the sum over orders of `Q o (πR o) − Q o o` (the tower).
Source: Milli et al. 2017 Theorem 1's proof
Kind: L
Fidelity: exact -/
lemma advantage_eq_sum_Q (πR : A → A) :
    M.advantage πR = ∑ o, (M.Q o (πR o) - M.Q o o) := by
  unfold advantage Q
  rw [sum_comm]
  refine sum_congr rfl fun o _ => ?_
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun θ _ => by ring

/-- **Theorem 1: the posterior-mean robot has nonnegative advantage.** Each order's summand
`Q o (πR o) − Q o o` is `≥ 0` because `πR o` maximises `Q o`.
Source: Milli et al. 2017 Theorem 1 (l. 145, `∀n Δ_n ≥ 0`)
Kind: L (one `sum_nonneg` after the tower identity `advantage_eq_sum_Q`; the mandate pre-graded
it P (small), relabelled on audit r1 — the content of Theorem 1 is the equality clause)
Fidelity: exact
Hyps: (a) `h : IsPosteriorMean πR` (the definition of `π^R_*`) -/
theorem advantage_nonneg (πR : A → A) (h : M.IsPosteriorMean πR) : 0 ≤ M.advantage πR := by
  rw [advantage_eq_sum_Q]
  exact sum_nonneg fun o _ => sub_nonneg.mpr (h o o)

/-- **Theorem 1, the equality clause**: `Δ = 0` iff every order maximises its own posterior
objective (a null order's objective is `0` everywhere, so it counts as a maximiser).
Source: Milli et al. 2017 Theorem 1 ("with equality iff `π^R_* = π^R_O`")
Kind: P
Fidelity: variant: "every order is a maximiser" in place of "`π^R_* = π^R_O`", which is the
same only under the tie-break (`advantage_eq_zero_iff_obedient_of_tieBreak`)
Hyps: (a) `h : IsPosteriorMean πR` -/
theorem advantage_eq_zero_iff (πR : A → A) (h : M.IsPosteriorMean πR) :
    M.advantage πR = 0 ↔ ∀ o a, M.Q o a ≤ M.Q o o := by
  rw [advantage_eq_sum_Q]
  constructor
  · intro h0 o a
    have := (sum_eq_zero_iff_of_nonneg fun o _ => sub_nonneg.mpr (h o o)).mp h0 o (mem_univ o)
    have := h o a
    linarith
  · intro hmax
    exact sum_eq_zero fun o _ => by linarith [h o o, hmax o (πR o)]

/-- **Theorem 1's "iff `π^R_* = π^R_O`", under Theorem 2's tie-break.**
Source: Milli et al. 2017 Theorem 1 and Theorem 2's tie-break
Kind: C
Fidelity: exact (the clause as the paper states it, with the tie-break made explicit)
Hyps: (a) `h`, `htb` -/
theorem advantage_eq_zero_iff_obedient_of_tieBreak (πR : A → A) (h : M.IsPosteriorMean πR)
    (htb : M.TieBreakObedient πR) : M.advantage πR = 0 ↔ ∀ o, πR o = o := by
  rw [advantage_eq_zero_iff M πR h]
  constructor
  · intro hmax o
    exact htb o (hmax o)
  · intro hob o a
    have := h o a
    rw [hob o] at this
    exact this

/-- **Theorem 3 (⇐), the support argument**: under a rational human every order maximises its
posterior objective — `Q o a = ∑ θ, prior θ · πH θ o · R θ a`, and wherever `πH θ o ≠ 0`,
`R θ a ≤ R θ o`.
Source: Milli et al. 2017 Theorem 3, the "if" direction (l. 157, "R's posterior only has support
over `O(h)`")
Kind: P (small)
Fidelity: exact
Hyps: (a) `hr : Rational` -/
theorem order_maximises_of_rational (hr : M.Rational) (o a : A) : M.Q o a ≤ M.Q o o := by
  unfold Q
  refine sum_le_sum fun θ _ => ?_
  by_cases hπ : (M.πH θ).mass o = 0
  · simp [post, hπ]
  · exact mul_le_mul_of_nonneg_left (hr θ o hπ a) (M.post_nonneg θ o)

/-- **Theorem 3 (⇐): with a rational human the optimal robot is blindly obedient** (under the
tie-break): `πR = id` and `O = 1`.
Source: Milli et al. 2017 Theorem 3 (⇐)
Kind: C
Fidelity: stronger (⇐ only; ⇒ rests on Diaconis–Freedman consistency, recorded): no
posterior-mean hypothesis is needed — any tie-break-obedient robot is forced to `id` by
`order_maximises_of_rational`, the paper's statement being about the optimal robot (audit r1)
Hyps: (a) `hr`, `htb` -/
theorem blindlyObedient_of_rational (πR : A → A) (hr : M.Rational) (htb : M.TieBreakObedient πR) :
    (∀ o, πR o = o) ∧ M.obedience πR = 1 := by
  have hob : ∀ o, πR o = o := fun o => htb o (M.order_maximises_of_rational hr o)
  refine ⟨hob, ?_⟩
  unfold obedience
  calc ∑ θ, ∑ o, M.post θ o * (if πR o = o then 1 else 0) = ∑ θ, ∑ o, M.post θ o :=
        sum_congr rfl fun θ _ => sum_congr rfl fun o _ => by rw [if_pos (hob o), mul_one]
    _ = 1 := M.sum_post

/-- **Lemma 1 (undominated necessary)**: an IRL robot executes `o` only if `o` is undominated.
Source: Milli et al. 2017 Lemma 1 (l. 187)
Kind: L (the two definitions coincide at `o = πR o'`)
Fidelity: exact
Hyps: (a) `h : IsIRL πR` -/
theorem undominated_of_isIRL (πR : A → A) (h : M.IsIRL πR) (o : A) : M.Undominated (πR o) :=
  h o

end Supervision

/-! ## Lemma 1's example: the dominated middle order -/

/-- The paper's three-action example: `φ(a) ∈ {(−1,−1), (0,0), (1,1)}` with `θ ∈ {(1,0), (−1,0)}`,
so `R = ![![−1, 0, 1], ![1, 0, −1]]`; the middle action `(0,0)` is dominated for every `θ`.
Source: Milli et al. 2017 Lemma 1's example (l. 187)
Kind: D
Fidelity: exact (the linear rewards written out) -/
noncomputable def milliExample : Supervision (Fin 2) (Fin 3) where
  prior := Distr.uniform
  R := ![![-1, 0, 1], ![1, 0, -1]]
  πH := fun _ => Distr.uniform

/-- **The middle order is dominated**, so no IRL robot executes it (Lemma 1, N+).
Source: Milli et al. 2017 Lemma 1's example
Kind: N+
Fidelity: exact -/
theorem milliExample_middle_dominated :
    ¬ milliExample.Undominated 1 ∧ ∀ πR, milliExample.IsIRL πR → ∀ o, πR o ≠ 1 := by
  have hnd : ¬ milliExample.Undominated 1 := by
    rintro ⟨θ, hθ⟩
    fin_cases θ
    · have := hθ 2; simp [milliExample] at this; norm_num at this
    · have := hθ 0; simp [milliExample] at this; norm_num at this
  refine ⟨hnd, fun πR h o hcon => hnd ?_⟩
  rw [← hcon]
  exact milliExample.undominated_of_isIRL πR h o

end Cleanroom.Corrigibility.CorrOsgChai

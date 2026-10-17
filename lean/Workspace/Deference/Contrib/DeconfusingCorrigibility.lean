/-
# "Deconfusing Corrigibility" — the post's formal content

Round `prompts/2026-10-17-post-companion-formalization/`.  The companion page, which maps
each item of the post to its declaration here, is `wiki/Deconfusing-Corrigibility-Companion.md`.

The post's sections "Definitions" through "Learning with logical induction", stated and
proved in the post's own numbering.  Parameters keep the post's names — `δ`, `τ`, `κ`, `θ`,
`ε`, `R`, `T`, `t` — except the weight `λ`, a reserved word in Lean, which is `lam`.

**Definitions** (`Params`, `Scoring`): histories `H`, a legitimacy predicate `Legit : H → Prop`
taken as an abstract input, a violation count `N : H → ℕ`, an evaluation `V : H → ℝ` in
`[0, 1]` on legitimate histories and in `[−δ, 0)` on illegitimate ones, a parameter `δ > 0`,
a weight `λ > 1 + δ`, and the score `S h = V h − λ N h`.

**Theorem 1** (`Scoring.theorem1`, three ranges): a violated history scores at most
`1 − λ`, and `1 − λ < −δ`; a violation-free illegitimate history scores in `[−δ, 0)`; a
violation-free legitimate history scores in `[0, 1]`.

**Single decision** (`Decision`): a finite state space `Ω` with a credence `μ` — the
workspace's finite credence, `LICorrigibility.expectR`, with `μ ≥ 0` summing to one —
actions with continuation histories `hist a ω`, `U a = E_μ[S(hist a ·)]`,
`v a = P_μ[N(hist a ·) ≥ 1]`, an authority-respecting alternative (`Respects`: no violation
in any state), the asking cost `κ`, and `τ = (1 + δ)/λ`.

**Theorem 2** (`Decision.theorem2a`, `theorem2b`, `theorem2b_strict`, `theorem2c`,
`theorem2c_tau`): (a) a sure violation loses at least `λ − (1 + δ) > 0` to the respecting
alternative; (b) `U a* − U a ≥ (λ − (1 + δ)) v a − κ`, so `U a* > U a` once
`v a > κ/(λ − (1 + δ))`; (c) `v a > (1 − U a*)/λ` forces `U a* > U a`, and
`(1 − U a*)/λ ≤ τ`.

**Sequential setting** (`Sequential`): realized scores `S_k = V_k − λ N_k` with `V_k ≤ 1`,
per-decision estimates `U_k`, the chosen `a_k`, an available authority-respecting `a_k*`
with `U_k a_k* ∈ [−δ, 1]` (a hypothesis), the tolerance `t_k = (1 − U_k a_k*)/λ`, the
realized rate `R_K`, the average tolerance `T_K`, maximization (`Maximizes`), and
**Unbiasedness From Feedback** (`UnbiasedFromFeedback`), a named hypothesis on the estimate
and score sequences: `∀ γ > 0, ∃ N₀, ∀ K ≥ N₀, (1/K) Σ_{k<K} (U_k a_k − S_k) ≤ γ`.  It is not
derived here.  The post obtains it from Theorem 4.8.16 of the Logical Induction paper; in
this workspace that theorem is pinned as `thm:wubexp` /
`LogicalInduction.lic_not_frequently_positive_feedback_return` in the def-lattice ledger,
`projects/deference/faf-cleanroom-2026-10-02/packages/def-lattice/def-lattice-report.md`.
That pointer is documentation; no declaration here cites it.  The workspace's weighted,
absolute-value form of the same fact, `BRIAFollowup.UnbiasedFromFeedback`, at the uniform
weighting and for every `γ > 0`, implies the post's form (`Sequential.unbiased_of_weighted`).

**Theorem 3** (`Sequential.theorem3a`, `theorem3a_rate`, `theorem3b`): under maximization
and Unbiasedness From Feedback, `limsup_K (R_K − T_K) ≤ 0`, hence `limsup_K R_K ≤ τ`; and
for any available sequence `a'_k`, `limsup_K (1/K) Σ_{k<K} (U_k a'_k − S_k) ≤ 0`.  Every
limsup is in the eventual form `LimsupLE x c`: `∀ γ > 0, ∃ N₀, ∀ K ≥ N₀, x K ≤ c + γ`.

**Corollary (Exploration)** (`Exploration`, `corollary_a`, `corollary_b`,
`corollary_limit`): with `0 ≤ θ < 1`, an exploration set `E`, `ε_K` its density in
`{0, …, K−1}`, maximization off `E`, on `E` the hypothesis `U_k a_k ≥ −δ − λ θ` (the post
derives it from an estimated violation count at most `θ` and linearity of the inductor's
expectation; it is taken directly here), and the estimate bound `U_k a' ≤ 1` on available
options: `limsup_K (R_K − T_K − ε_K (τ + θ)) ≤ 0`,
`limsup_K ((1/K) Σ_{k<K} (U_k a'_k − S_k) − ε_K λ (τ + θ)) ≤ 0`, and if `ε_K → 0` both
conclusions of Theorem 3 hold unchanged.

**Witnesses** (`Witness`): a two-state, three-action decision inhabiting every hypothesis
package of Theorems 1 and 2 at `δ = 1`, `λ = 3`; a sequence with estimates equal to
realized scores inhabiting Theorem 3's package; the same sequence exploring at `k = 0`
inhabiting the Corollary's package, with `ε_K → 0`.

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Deference.Contrib.LICorrigibility
import Workspace.Deference.Contrib.BRIAFollowup

namespace Workspace.Deference.Contrib.DeconfusingCorrigibility

open Finset
open Workspace.Deference.Contrib.LICorrigibility (expectR)

/-! ## Definitions -/

/-- The post's parameters: `δ > 0` and the weight `λ > 1 + δ` (`lam`). -/
structure Params where
  /-- the illegitimacy floor `δ` -/
  δ : ℝ
  /-- the post's `λ` -/
  lam : ℝ
  δ_pos : 0 < δ
  lam_gt : 1 + δ < lam

namespace Params

variable (P : Params)

/-- `τ = (1 + δ)/λ`. -/
noncomputable def τ : ℝ := (1 + P.δ) / P.lam

theorem lam_pos : 0 < P.lam := by linarith [P.δ_pos, P.lam_gt]

theorem lam_ne : P.lam ≠ 0 := P.lam_pos.ne'

theorem gap_pos : 0 < P.lam - (1 + P.δ) := by linarith [P.lam_gt]

theorem τ_pos : 0 < P.τ := div_pos (by linarith [P.δ_pos]) P.lam_pos

theorem lam_mul_τ : P.lam * P.τ = 1 + P.δ := by
  unfold τ
  rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self P.lam_ne, mul_one]

end Params

/-- Dividing both sides of an inequality by a nonnegative real. -/
theorem div_le_div_same_denom {a b c : ℝ} (h : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hc)

/-- **The post's definitions.**  A legitimacy predicate on histories, taken as an abstract
input; a violation count; an evaluation in `[0, 1]` on legitimate histories and in `[−δ, 0)`
on illegitimate ones. -/
structure Scoring (H : Type*) extends Params where
  /-- legitimacy, assumed nothing about beyond the bounds below -/
  Legit : H → Prop
  /-- the violation count -/
  N : H → ℕ
  /-- the evaluation -/
  V : H → ℝ
  V_legit : ∀ h, Legit h → 0 ≤ V h ∧ V h ≤ 1
  V_illegit : ∀ h, ¬ Legit h → -δ ≤ V h ∧ V h < 0

namespace Scoring

variable {H : Type*} (Sc : Scoring H)

/-- The score `S h = V h − λ N h`. -/
noncomputable def S (h : H) : ℝ := Sc.V h - Sc.lam * Sc.N h

theorem V_le_one (h : H) : Sc.V h ≤ 1 := by
  by_cases hl : Sc.Legit h
  · exact (Sc.V_legit h hl).2
  · linarith [(Sc.V_illegit h hl).2]

theorem neg_δ_le_V (h : H) : -Sc.δ ≤ Sc.V h := by
  by_cases hl : Sc.Legit h
  · linarith [(Sc.V_legit h hl).1, Sc.δ_pos]
  · exact (Sc.V_illegit h hl).1

theorem S_le_one (h : H) : Sc.S h ≤ 1 := by
  have hN : (0 : ℝ) ≤ Sc.N h := Nat.cast_nonneg _
  have := mul_nonneg Sc.toParams.lam_pos.le hN
  unfold S
  linarith [Sc.V_le_one h]

theorem S_eq_of_N_zero (h : H) (hN : Sc.N h = 0) : Sc.S h = Sc.V h := by
  unfold S
  rw [hN]
  simp

theorem neg_δ_le_S_of_N_zero (h : H) (hN : Sc.N h = 0) : -Sc.δ ≤ Sc.S h := by
  rw [Sc.S_eq_of_N_zero h hN]
  exact Sc.neg_δ_le_V h

/-! ## Theorem 1 (three ranges) -/

/-- **Theorem 1, violated**: `N h ≥ 1 → S h ≤ 1 − λ`. -/
theorem theorem1_violated (h : H) (hN : 1 ≤ Sc.N h) : Sc.S h ≤ 1 - Sc.lam := by
  have h1 : (1 : ℝ) ≤ Sc.N h := by exact_mod_cast hN
  have hl := mul_le_mul_of_nonneg_left h1 Sc.toParams.lam_pos.le
  unfold S
  linarith [Sc.V_le_one h]

/-- **Theorem 1, the gap**: `1 − λ < −δ`. -/
theorem theorem1_gap : 1 - Sc.lam < -Sc.δ := by linarith [Sc.lam_gt]

/-- **Theorem 1, violation-free and illegitimate**: `−δ ≤ S h < 0`. -/
theorem theorem1_illegitimate (h : H) (hN : Sc.N h = 0) (hl : ¬ Sc.Legit h) :
    -Sc.δ ≤ Sc.S h ∧ Sc.S h < 0 := by
  rw [Sc.S_eq_of_N_zero h hN]
  exact Sc.V_illegit h hl

/-- **Theorem 1, violation-free and legitimate**: `0 ≤ S h ≤ 1`. -/
theorem theorem1_legitimate (h : H) (hN : Sc.N h = 0) (hl : Sc.Legit h) :
    0 ≤ Sc.S h ∧ Sc.S h ≤ 1 := by
  rw [Sc.S_eq_of_N_zero h hN]
  exact Sc.V_legit h hl

/-- **Theorem 1 (three ranges).**  For every history `h`: if `N h ≥ 1` then `S h ≤ 1 − λ`,
and `1 − λ < −δ`; if `N h = 0` and `h` is illegitimate then `−δ ≤ S h < 0`; if `N h = 0` and
`h` is legitimate then `0 ≤ S h ≤ 1`. -/
theorem theorem1 (h : H) :
    ((1 ≤ Sc.N h → Sc.S h ≤ 1 - Sc.lam) ∧ 1 - Sc.lam < -Sc.δ) ∧
      (Sc.N h = 0 ∧ ¬ Sc.Legit h → -Sc.δ ≤ Sc.S h ∧ Sc.S h < 0) ∧
      (Sc.N h = 0 ∧ Sc.Legit h → 0 ≤ Sc.S h ∧ Sc.S h ≤ 1) :=
  ⟨⟨Sc.theorem1_violated h, Sc.theorem1_gap⟩,
    fun hh => Sc.theorem1_illegitimate h hh.1 hh.2,
    fun hh => Sc.theorem1_legitimate h hh.1 hh.2⟩

end Scoring

/-! ## Finite expectation -/

/-- The indicator `1{p}` of a decidable proposition, as a real. -/
noncomputable def ind (p : Prop) [Decidable p] : ℝ := if p then 1 else 0

theorem ind_pos {p : Prop} [Decidable p] (h : p) : ind p = 1 := by
  unfold ind
  exact if_pos h

theorem ind_neg {p : Prop} [Decidable p] (h : ¬ p) : ind p = 0 := by
  unfold ind
  exact if_neg h

section Expectation

variable {X : Type*} [Fintype X] (μ : X → ℝ)

/-- Monotonicity of the finite expectation under a nonnegative credence. -/
theorem expectR_mono (hμ : ∀ x, 0 ≤ μ x) {f g : X → ℝ} (h : ∀ x, f x ≤ g x) :
    expectR μ f ≤ expectR μ g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (hμ x)

/-- Expectation of a difference. -/
theorem expectR_sub (f g : X → ℝ) :
    expectR μ (fun x => f x - g x) = expectR μ f - expectR μ g := by
  unfold expectR
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- Expectation of a scalar multiple. -/
theorem expectR_const_mul (c : ℝ) (f : X → ℝ) :
    expectR μ (fun x => c * f x) = c * expectR μ f := by
  unfold expectR
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- Expectation of a constant under a credence summing to one. -/
theorem expectR_const (hsum : ∑ x, μ x = 1) (c : ℝ) : expectR μ (fun _ => c) = c := by
  unfold expectR
  rw [← Finset.sum_mul, hsum, one_mul]

end Expectation

/-! ## The single-decision setting -/

/-- **The single-decision setting.**  A finite state space `Ω` with a credence `μ` — the
workspace's finite credence (`LICorrigibility.expectR`): nonnegative weights summing to
one — and, for each action `a`, its continuation history `hist a ω` in each state. -/
structure Decision (H Ω A : Type*) [Fintype Ω] extends Scoring H where
  /-- the credence -/
  μ : Ω → ℝ
  μ_nonneg : ∀ ω, 0 ≤ μ ω
  μ_sum : ∑ ω, μ ω = 1
  /-- the post's `h a ω`: the continuation history of action `a` in state `ω` -/
  hist : A → Ω → H

namespace Decision

variable {H Ω A : Type*} [Fintype Ω] (D : Decision H Ω A)

/-- `U a = E_μ[S(h a ·)]`. -/
noncomputable def U (a : A) : ℝ := expectR D.μ fun ω => D.S (D.hist a ω)

/-- `v a = P_μ[N(h a ·) ≥ 1]`. -/
noncomputable def v (a : A) : ℝ := expectR D.μ fun ω => ind (1 ≤ D.N (D.hist a ω))

/-- An authority-respecting alternative: `∀ ω, N(h a* ω) = 0`. -/
def Respects (astar : A) : Prop := ∀ ω, D.N (D.hist astar ω) = 0

/-- The asking cost `κ = E_μ[(S(h a ·) − S(h a* ·)) · 1{N(h a ·) = 0}]`. -/
noncomputable def κ (a astar : A) : ℝ :=
  expectR D.μ fun ω => (D.S (D.hist a ω) - D.S (D.hist astar ω)) * ind (D.N (D.hist a ω) = 0)

/-- Pointwise: `S(h a ω) ≤ 1 − λ · 1{N(h a ω) ≥ 1}`. -/
theorem S_le_one_sub (a : A) (ω : Ω) :
    D.S (D.hist a ω) ≤ 1 - D.lam * ind (1 ≤ D.N (D.hist a ω)) := by
  by_cases hN : 1 ≤ D.N (D.hist a ω)
  · rw [ind_pos hN, mul_one]
    exact D.theorem1_violated _ hN
  · rw [ind_neg hN, mul_zero, sub_zero]
    exact D.S_le_one _

/-- `U a ≤ 1 − λ v a`. -/
theorem U_le (a : A) : D.U a ≤ 1 - D.lam * D.v a := by
  have h := expectR_mono D.μ D.μ_nonneg fun ω => D.S_le_one_sub a ω
  have e : expectR D.μ (fun ω => 1 - D.lam * ind (1 ≤ D.N (D.hist a ω)))
      = 1 - D.lam * D.v a := by
    rw [expectR_sub, expectR_const D.μ D.μ_sum, expectR_const_mul]
    rfl
  unfold U
  linarith

/-- An authority-respecting alternative is worth at least `−δ`. -/
theorem neg_δ_le_U (astar : A) (hstar : D.Respects astar) : -D.δ ≤ D.U astar := by
  have h := expectR_mono D.μ D.μ_nonneg
    fun ω => D.neg_δ_le_S_of_N_zero (D.hist astar ω) (hstar ω)
  rw [expectR_const D.μ D.μ_sum] at h
  exact h

/-! ## Theorem 2 -/

/-- **Theorem 2(a).**  If `v a = 1` then `U a* − U a ≥ λ − (1 + δ)`. -/
theorem theorem2a (a astar : A) (hstar : D.Respects astar) (hv : D.v a = 1) :
    D.U astar - D.U a ≥ D.lam - (1 + D.δ) := by
  have h1 := D.U_le a
  have h2 := D.neg_δ_le_U astar hstar
  rw [hv] at h1
  linarith

/-- **Theorem 2(a), the margin is positive**: `λ − (1 + δ) > 0`. -/
theorem theorem2a_pos : D.lam - (1 + D.δ) > 0 := D.toParams.gap_pos

/-- **Theorem 2(b).**  `U a* − U a ≥ (λ − (1 + δ)) · v a − κ`. -/
theorem theorem2b (a astar : A) (hstar : D.Respects astar) :
    D.U astar - D.U a ≥ (D.lam - (1 + D.δ)) * D.v a - D.κ a astar := by
  have hpt : ∀ ω, (D.lam - (1 + D.δ)) * ind (1 ≤ D.N (D.hist a ω))
      - (D.S (D.hist a ω) - D.S (D.hist astar ω)) * ind (D.N (D.hist a ω) = 0)
      ≤ D.S (D.hist astar ω) - D.S (D.hist a ω) := by
    intro ω
    by_cases hN : 1 ≤ D.N (D.hist a ω)
    · have hN0 : D.N (D.hist a ω) ≠ 0 := by omega
      rw [ind_pos hN, ind_neg hN0, mul_one, mul_zero, sub_zero]
      have h1 := D.theorem1_violated _ hN
      have h2 := D.neg_δ_le_S_of_N_zero (D.hist astar ω) (hstar ω)
      linarith
    · have hN0 : D.N (D.hist a ω) = 0 := by omega
      rw [ind_neg hN, ind_pos hN0, mul_zero, mul_one]
      linarith
  have h := expectR_mono D.μ D.μ_nonneg hpt
  rw [expectR_sub, expectR_sub, expectR_const_mul] at h
  exact h

/-- **Theorem 2(b), the consequence.**  `U a* > U a` whenever `v a > κ/(λ − (1 + δ))`. -/
theorem theorem2b_strict (a astar : A) (hstar : D.Respects astar)
    (hv : D.v a > D.κ a astar / (D.lam - (1 + D.δ))) : D.U astar > D.U a := by
  have hgap := D.toParams.gap_pos
  have h := D.theorem2b a astar hstar
  have h' : D.κ a astar < D.v a * (D.lam - (1 + D.δ)) := (div_lt_iff₀ hgap).mp hv
  linarith

/-- **Theorem 2(c).**  `v a > (1 − U a*)/λ` forces `U a* > U a`.  The clause holds for any
alternative `a*`; the post's authority-respecting hypothesis is not needed for it (it is
needed for `theorem2c_tau`). -/
theorem theorem2c (a astar : A) (hv : D.v a > (1 - D.U astar) / D.lam) :
    D.U astar > D.U a := by
  have hlam := D.toParams.lam_pos
  have h1 := D.U_le a
  have h' : 1 - D.U astar < D.v a * D.lam := (div_lt_iff₀ hlam).mp hv
  linarith

/-- **Theorem 2(c), the threshold is at most `τ`**: `(1 − U a*)/λ ≤ τ`. -/
theorem theorem2c_tau (astar : A) (hstar : D.Respects astar) :
    (1 - D.U astar) / D.lam ≤ D.τ := by
  have hlam := D.toParams.lam_pos
  have h := D.neg_δ_le_U astar hstar
  unfold Params.τ
  exact div_le_div_same_denom (by linarith) hlam.le

end Decision

/-! ## The sequential setting -/

/-- `limsup_K x_K ≤ c`, in the eventual form used throughout this file:
for every `γ > 0` there is `N₀` with `x_K ≤ c + γ` for all `K ≥ N₀`. -/
def LimsupLE (x : ℕ → ℝ) (c : ℝ) : Prop := ∀ γ > 0, ∃ N₀, ∀ K ≥ N₀, x K ≤ c + γ

namespace LimsupLE

theorem of_le {x y : ℕ → ℝ} {c : ℝ} (h : ∀ K, x K ≤ y K) (hy : LimsupLE y c) :
    LimsupLE x c := by
  intro γ hγ
  obtain ⟨N₀, hN₀⟩ := hy γ hγ
  exact ⟨N₀, fun K hK => (h K).trans (hN₀ K hK)⟩

theorem add {x y : ℕ → ℝ} {c d : ℝ} (hx : LimsupLE x c) (hy : LimsupLE y d) :
    LimsupLE (fun K => x K + y K) (c + d) := by
  intro γ hγ
  obtain ⟨N₁, h₁⟩ := hx (γ / 2) (by linarith)
  obtain ⟨N₂, h₂⟩ := hy (γ / 2) (by linarith)
  refine ⟨max N₁ N₂, fun K hK => ?_⟩
  have e₁ := h₁ K (le_of_max_le_left hK)
  have e₂ := h₂ K (le_of_max_le_right hK)
  linarith

theorem add_const {x : ℕ → ℝ} {c : ℝ} (hx : LimsupLE x c) (d : ℝ) :
    LimsupLE (fun K => x K + d) (c + d) := by
  intro γ hγ
  obtain ⟨N₀, hN₀⟩ := hx γ hγ
  exact ⟨N₀, fun K hK => by linarith [hN₀ K hK]⟩

theorem mul_const {y : ℕ → ℝ} (hy : LimsupLE y 0) {C : ℝ} (hC : 0 ≤ C) :
    LimsupLE (fun K => y K * C) 0 := by
  intro γ hγ
  rcases hC.lt_or_eq with hC' | hC'
  · obtain ⟨N₀, hN₀⟩ := hy (γ / C) (div_pos hγ hC')
    refine ⟨N₀, fun K hK => ?_⟩
    have h := hN₀ K hK
    rw [zero_add] at h ⊢
    exact (le_div_iff₀ hC').mp h
  · refine ⟨0, fun K _ => ?_⟩
    show y K * C ≤ 0 + γ
    rw [← hC', mul_zero, zero_add]
    exact hγ.le

end LimsupLE

/-- **The sequential setting.**  Decisions `k : ℕ`; realized evaluations `V_k ≤ 1` and
violation counts `N_k`; per-decision estimates `U_k` over the actions available at `k`; the
chosen action `a_k`; an authority-respecting alternative `a_k*` available at each `k`, with
`−δ ≤ U_k a_k* ≤ 1` as a hypothesis. -/
structure Sequential (A : Type*) extends Params where
  /-- the realized evaluation `V_k` -/
  V : ℕ → ℝ
  /-- the realized violation count `N_k` -/
  N : ℕ → ℕ
  V_le_one : ∀ k, V k ≤ 1
  /-- availability of an action at decision `k` -/
  avail : ℕ → A → Prop
  /-- the estimate `U_k` -/
  U : ℕ → A → ℝ
  /-- the chosen action `a_k` -/
  a : ℕ → A
  /-- the authority-respecting alternative `a_k*` -/
  astar : ℕ → A
  astar_avail : ∀ k, avail k (astar k)
  astar_range : ∀ k, -δ ≤ U k (astar k) ∧ U k (astar k) ≤ 1

namespace Sequential

variable {A : Type*} (Q : Sequential A)

/-- The realized score `S_k = V_k − λ N_k`. -/
noncomputable def S (k : ℕ) : ℝ := Q.V k - Q.lam * Q.N k

/-- The tolerance `t_k = (1 − U_k a_k*)/λ`. -/
noncomputable def t (k : ℕ) : ℝ := (1 - Q.U k (Q.astar k)) / Q.lam

/-- The realized rate `R_K = (1/K) Σ_{k<K} N_k`. -/
noncomputable def R (K : ℕ) : ℝ := (∑ k ∈ range K, (Q.N k : ℝ)) / (K : ℝ)

/-- The average tolerance `T_K = (1/K) Σ_{k<K} t_k`. -/
noncomputable def T (K : ℕ) : ℝ := (∑ k ∈ range K, Q.t k) / (K : ℝ)

/-- The average excess of estimate over realized score along a sequence `a'`:
`(1/K) Σ_{k<K} (U_k a'_k − S_k)`. -/
noncomputable def excess (a' : ℕ → A) (K : ℕ) : ℝ :=
  (∑ k ∈ range K, (Q.U k (a' k) - Q.S k)) / (K : ℝ)

/-- **Maximization**: at every `k`, the chosen action maximizes the estimate over the
available actions. -/
def Maximizes : Prop := ∀ k a', Q.avail k a' → Q.U k a' ≤ Q.U k (Q.a k)

/-- **Unbiasedness From Feedback**, the post's named hypothesis on the estimate and score
sequences: `∀ γ > 0, ∃ N₀, ∀ K ≥ N₀, (1/K) Σ_{k<K} (U_k a_k − S_k) ≤ γ`.  The post derives it
from Theorem 4.8.16 of the Logical Induction paper (pinned in this workspace as
`thm:wubexp` / `LogicalInduction.lic_not_frequently_positive_feedback_return`, in the
def-lattice ledger); here it is assumed, not derived. -/
def UnbiasedFromFeedback : Prop := ∀ γ > 0, ∃ N₀, ∀ K ≥ N₀, Q.excess Q.a K ≤ γ

/-- The workspace's weighted form of unbiasedness from feedback
(`BRIAFollowup.UnbiasedFromFeedback W bias γ N`: `|Σ_{k<K} W_k bias_k| ≤ γ Σ_{k<K} W_k` for
`K ≥ N`), at the uniform weighting `W = 1` with `bias_k = U_k a_k − S_k`, holding for every
`γ > 0` from some `N₀`, gives the post's one-sided form. -/
theorem unbiased_of_weighted
    (h : ∀ γ > 0, ∃ N₀, Workspace.Deference.Contrib.BRIAFollowup.UnbiasedFromFeedback
      (fun _ => 1) (fun k => Q.U k (Q.a k) - Q.S k) γ N₀) :
    Q.UnbiasedFromFeedback := by
  intro γ hγ
  obtain ⟨N₀, hN₀⟩ := h γ hγ
  refine ⟨N₀, fun K hK => ?_⟩
  have hb := hN₀ K hK
  simp only [one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hb
  unfold excess
  rcases Nat.eq_zero_or_pos K with hK0 | hK0
  · subst hK0
    rw [Finset.range_zero, Finset.sum_empty, zero_div]
    exact hγ.le
  · have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
    rw [div_le_iff₀ hKr]
    exact (le_abs_self _).trans (by linarith [hb])

theorem limsup_of_unbiased (huff : Q.UnbiasedFromFeedback) : LimsupLE (Q.excess Q.a) 0 := by
  intro γ hγ
  obtain ⟨N₀, hN₀⟩ := huff γ hγ
  exact ⟨N₀, fun K hK => by rw [zero_add]; exact hN₀ K hK⟩

/-- Under Unbiasedness From Feedback the excess over `λ` is eventually below any `γ > 0`. -/
theorem limsup_excess_div (huff : Q.UnbiasedFromFeedback) :
    LimsupLE (fun K => Q.excess Q.a K / Q.lam) 0 := by
  intro γ hγ
  have hlam := Q.toParams.lam_pos
  obtain ⟨N₀, hN₀⟩ := huff (Q.lam * γ) (mul_pos hlam hγ)
  refine ⟨N₀, fun K hK => ?_⟩
  rw [zero_add, div_le_iff₀ hlam]
  linarith [hN₀ K hK]

/-- Pointwise: `N_k − t_k ≤ (U_k a_k* − S_k)/λ`, from `V_k ≤ 1`. -/
theorem N_sub_t_le (k : ℕ) : (Q.N k : ℝ) - Q.t k ≤ (Q.U k (Q.astar k) - Q.S k) / Q.lam := by
  have hlam := Q.toParams.lam_pos
  have hne := Q.toParams.lam_ne
  have ht : Q.t k * Q.lam = 1 - Q.U k (Q.astar k) := by
    unfold t
    field_simp
  have hV := Q.V_le_one k
  rw [le_div_iff₀ hlam]
  unfold S
  linarith

/-- Each tolerance is at most `τ`, from `U_k a_k* ≥ −δ`. -/
theorem t_le_τ (k : ℕ) : Q.t k ≤ Q.τ := by
  have hlam := Q.toParams.lam_pos
  unfold t Params.τ
  exact div_le_div_same_denom (by linarith [(Q.astar_range k).1]) hlam.le

/-- The average tolerance is at most `τ`. -/
theorem T_le_τ (K : ℕ) : Q.T K ≤ Q.τ := by
  unfold T
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    rw [Finset.range_zero, Finset.sum_empty, zero_div]
    exact Q.toParams.τ_pos.le
  · have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    rw [div_le_iff₀ hK']
    calc ∑ k ∈ range K, Q.t k ≤ ∑ _k ∈ range K, Q.τ := Finset.sum_le_sum fun k _ => Q.t_le_τ k
      _ = Q.τ * K := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]

/-- Under maximization, `R_K − T_K ≤ ((1/K) Σ_{k<K} (U_k a_k − S_k)) / λ`. -/
theorem rate_le_excess (hmax : Q.Maximizes) (K : ℕ) :
    Q.R K - Q.T K ≤ Q.excess Q.a K / Q.lam := by
  have hlam := Q.toParams.lam_pos
  have hpt : ∀ k, (Q.N k : ℝ) - Q.t k ≤ (Q.U k (Q.a k) - Q.S k) / Q.lam := by
    intro k
    exact (Q.N_sub_t_le k).trans
      (div_le_div_same_denom (by linarith [hmax k _ (Q.astar_avail k)]) hlam.le)
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ range K) => hpt k
  have e1 : Q.R K - Q.T K = (∑ k ∈ range K, ((Q.N k : ℝ) - Q.t k)) / (K : ℝ) := by
    unfold R T
    rw [Finset.sum_sub_distrib, sub_div]
  have e2 : Q.excess Q.a K / Q.lam
      = (∑ k ∈ range K, (Q.U k (Q.a k) - Q.S k) / Q.lam) / (K : ℝ) := by
    unfold excess
    rw [div_right_comm, Finset.sum_div]
  rw [e1, e2]
  exact div_le_div_same_denom hsum (Nat.cast_nonneg K)

/-- Under maximization, any available sequence's excess is at most the chosen sequence's. -/
theorem excess_le_excess (hmax : Q.Maximizes) (a' : ℕ → A) (ha' : ∀ k, Q.avail k (a' k))
    (K : ℕ) : Q.excess a' K ≤ Q.excess Q.a K := by
  unfold excess
  exact div_le_div_same_denom (Finset.sum_le_sum fun k _ => by linarith [hmax k _ (ha' k)])
    (Nat.cast_nonneg K)

/-! ## Theorem 3 -/

/-- **Theorem 3(a), Authority.**  Under maximization and Unbiasedness From Feedback,
`limsup_K (R_K − T_K) ≤ 0`. -/
theorem theorem3a (hmax : Q.Maximizes) (huff : Q.UnbiasedFromFeedback) :
    LimsupLE (fun K => Q.R K - Q.T K) 0 :=
  LimsupLE.of_le (Q.rate_le_excess hmax) (Q.limsup_excess_div huff)

/-- **Theorem 3(a), in particular**: `limsup_K R_K ≤ τ`. -/
theorem theorem3a_rate (hmax : Q.Maximizes) (huff : Q.UnbiasedFromFeedback) :
    LimsupLE Q.R Q.τ := by
  have h := (Q.theorem3a hmax huff).add_const Q.τ
  rw [zero_add] at h
  exact LimsupLE.of_le (fun K => by linarith [Q.T_le_τ K]) h

/-- **Theorem 3(b), Best Interests.**  Under maximization and Unbiasedness From Feedback,
for any sequence `a'_k` with `a'_k` available at `k`,
`limsup_K (1/K) Σ_{k<K} (U_k a'_k − S_k) ≤ 0`. -/
theorem theorem3b (hmax : Q.Maximizes) (huff : Q.UnbiasedFromFeedback) (a' : ℕ → A)
    (ha' : ∀ k, Q.avail k (a' k)) : LimsupLE (Q.excess a') 0 :=
  LimsupLE.of_le (Q.excess_le_excess hmax a' ha') (Q.limsup_of_unbiased huff)

end Sequential

/-! ## Corollary (Exploration) -/

/-- **The exploration hypotheses.**  An exploration set `E` (as a Boolean predicate on
decisions), `0 ≤ θ < 1`, maximization off `E`, on `E` the bound `U_k a_k ≥ −δ − λ θ` — the
post derives it from an estimated violation count at most `θ` and linearity of the
inductor's expectation; it is taken directly here — and the estimate bound `U_k a' ≤ 1` on
every available option. -/
structure Exploration (A : Type*) extends Sequential A where
  /-- the exploration cap `θ` -/
  θ : ℝ
  θ_nonneg : 0 ≤ θ
  θ_lt_one : θ < 1
  /-- the exploration set: `k ∈ E` iff `E k = true` -/
  E : ℕ → Bool
  maximizes_off : ∀ k, E k = false → ∀ a', avail k a' → U k a' ≤ U k (a k)
  explore_bound : ∀ k, E k = true → U k (a k) ≥ -δ - lam * θ
  U_le_one : ∀ k a', avail k a' → U k a' ≤ 1

namespace Exploration

variable {A : Type*} (X : Exploration A)

/-- The exploration density `ε_K = |E ∩ {0, …, K−1}| / K`. -/
noncomputable def ε (K : ℕ) : ℝ := (((range K).filter fun k => X.E k = true).card : ℝ) / (K : ℝ)

/-- Pointwise: `N_k − t_k ≤ (U_k a_k − S_k)/λ + (τ + θ) · 1{k ∈ E}`. -/
theorem N_sub_t_le_expl (k : ℕ) :
    (X.N k : ℝ) - X.t k
      ≤ (X.U k (X.a k) - X.S k) / X.lam + (X.τ + X.θ) * (if X.E k = true then 1 else 0) := by
  have hlam := X.toParams.lam_pos
  have hne := X.toParams.lam_ne
  have h0 := X.toSequential.N_sub_t_le k
  by_cases hE : X.E k = true
  · rw [if_pos hE, mul_one]
    have hb := X.explore_bound k hE
    have hU1 := (X.astar_range k).2
    have hτ := X.toParams.lam_mul_τ
    have hgap : X.U k (X.astar k) - X.S k
        ≤ (X.U k (X.a k) - X.S k) + X.lam * (X.τ + X.θ) := by linarith
    have e : ((X.U k (X.a k) - X.S k) + X.lam * (X.τ + X.θ)) / X.lam
        = (X.U k (X.a k) - X.S k) / X.lam + (X.τ + X.θ) := by
      rw [add_div, mul_comm X.lam, mul_div_assoc, div_self hne, mul_one]
    calc (X.N k : ℝ) - X.t k ≤ (X.U k (X.astar k) - X.S k) / X.lam := h0
      _ ≤ ((X.U k (X.a k) - X.S k) + X.lam * (X.τ + X.θ)) / X.lam :=
          div_le_div_same_denom hgap hlam.le
      _ = _ := e
  · have hE' : X.E k = false := by simpa using hE
    rw [if_neg hE, mul_zero, add_zero]
    exact h0.trans
      (div_le_div_same_denom (by linarith [X.maximizes_off k hE' _ (X.astar_avail k)]) hlam.le)

/-- Pointwise: for an available `a'_k`,
`U_k a'_k − S_k ≤ (U_k a_k − S_k) + λ (τ + θ) · 1{k ∈ E}`. -/
theorem excess_pt (a' : ℕ → A) (ha' : ∀ k, X.avail k (a' k)) (k : ℕ) :
    X.U k (a' k) - X.S k
      ≤ (X.U k (X.a k) - X.S k) + X.lam * (X.τ + X.θ) * (if X.E k = true then 1 else 0) := by
  by_cases hE : X.E k = true
  · rw [if_pos hE, mul_one]
    have h1 := X.U_le_one k _ (ha' k)
    have h2 := X.explore_bound k hE
    have h3 := X.toParams.lam_mul_τ
    linarith
  · have hE' : X.E k = false := by simpa using hE
    rw [if_neg hE, mul_zero, add_zero]
    linarith [X.maximizes_off k hE' _ (ha' k)]

/-- `R_K − T_K ≤ ((1/K) Σ_{k<K} (U_k a_k − S_k))/λ + ε_K (τ + θ)`. -/
theorem rate_le_expl (K : ℕ) :
    X.R K - X.T K ≤ X.excess X.a K / X.lam + X.ε K * (X.τ + X.θ) := by
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ range K) => X.N_sub_t_le_expl k
  have e1 : X.R K - X.T K = (∑ k ∈ range K, ((X.N k : ℝ) - X.t k)) / (K : ℝ) := by
    unfold Sequential.R Sequential.T
    rw [Finset.sum_sub_distrib, sub_div]
  have e2 : X.excess X.a K / X.lam + X.ε K * (X.τ + X.θ)
      = (∑ k ∈ range K, ((X.U k (X.a k) - X.S k) / X.lam
          + (X.τ + X.θ) * (if X.E k = true then 1 else 0))) / (K : ℝ) := by
    unfold Sequential.excess ε
    rw [Finset.sum_add_distrib, add_div, ← Finset.sum_div, ← Finset.mul_sum, Finset.sum_boole]
    ring
  rw [e1, e2]
  exact div_le_div_same_denom hsum (Nat.cast_nonneg K)

/-- For an available sequence, `(1/K) Σ_{k<K} (U_k a'_k − S_k) ≤ (1/K) Σ_{k<K} (U_k a_k − S_k)
+ ε_K λ (τ + θ)`. -/
theorem excess_le_expl (a' : ℕ → A) (ha' : ∀ k, X.avail k (a' k)) (K : ℕ) :
    X.excess a' K ≤ X.excess X.a K + X.ε K * (X.lam * (X.τ + X.θ)) := by
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ range K) => X.excess_pt a' ha' k
  have e2 : X.excess X.a K + X.ε K * (X.lam * (X.τ + X.θ))
      = (∑ k ∈ range K, ((X.U k (X.a k) - X.S k)
          + X.lam * (X.τ + X.θ) * (if X.E k = true then 1 else 0))) / (K : ℝ) := by
    unfold Sequential.excess ε
    rw [Finset.sum_add_distrib, add_div, ← Finset.mul_sum, Finset.sum_boole]
    ring
  rw [e2]
  unfold Sequential.excess
  exact div_le_div_same_denom hsum (Nat.cast_nonneg K)

/-- **Corollary (a).**  Under Unbiasedness From Feedback,
`limsup_K (R_K − T_K − ε_K (τ + θ)) ≤ 0`. -/
theorem corollary_a (huff : X.UnbiasedFromFeedback) :
    LimsupLE (fun K => X.R K - X.T K - X.ε K * (X.τ + X.θ)) 0 :=
  LimsupLE.of_le (fun K => by linarith [X.rate_le_expl K])
    (X.toSequential.limsup_excess_div huff)

/-- **Corollary (b).**  Under Unbiasedness From Feedback, for any available `a'_k`,
`limsup_K ((1/K) Σ_{k<K} (U_k a'_k − S_k) − ε_K λ (τ + θ)) ≤ 0`. -/
theorem corollary_b (huff : X.UnbiasedFromFeedback) (a' : ℕ → A)
    (ha' : ∀ k, X.avail k (a' k)) :
    LimsupLE (fun K => X.excess a' K - X.ε K * (X.lam * (X.τ + X.θ))) 0 :=
  LimsupLE.of_le (fun K => by linarith [X.excess_le_expl a' ha' K])
    (X.toSequential.limsup_of_unbiased huff)

/-- **Corollary, the specialization.**  If `ε_K → 0` (eventually below any `γ > 0`), both
conclusions of Theorem 3 hold unchanged: `limsup_K (R_K − T_K) ≤ 0`, `limsup_K R_K ≤ τ`,
and `limsup_K (1/K) Σ_{k<K} (U_k a'_k − S_k) ≤ 0` for every available `a'`. -/
theorem corollary_limit (huff : X.UnbiasedFromFeedback) (hε : LimsupLE X.ε 0) :
    LimsupLE (fun K => X.R K - X.T K) 0 ∧ LimsupLE X.R X.τ ∧
      ∀ a' : ℕ → A, (∀ k, X.avail k (a' k)) → LimsupLE (X.excess a') 0 := by
  have hc : 0 ≤ X.τ + X.θ := by linarith [X.toParams.τ_pos, X.θ_nonneg]
  have ha : LimsupLE (fun K => X.R K - X.T K) 0 := by
    have h := (X.corollary_a huff).add (hε.mul_const hc)
    rw [zero_add] at h
    exact LimsupLE.of_le (fun K => by linarith) h
  refine ⟨ha, ?_, ?_⟩
  · have h := ha.add_const X.τ
    rw [zero_add] at h
    exact LimsupLE.of_le (fun K => by linarith [X.toSequential.T_le_τ K]) h
  · intro a' ha'
    have hc' : 0 ≤ X.lam * (X.τ + X.θ) := mul_nonneg X.toParams.lam_pos.le hc
    have h := (X.corollary_b huff a' ha').add (hε.mul_const hc')
    rw [zero_add] at h
    exact LimsupLE.of_le (fun K => by linarith) h

end Exploration

/-! ## Witnesses -/

namespace Witness

/-- Histories: a legitimacy flag and a violation count.  `δ = 1`, `λ = 3`. -/
noncomputable def scoring : Scoring (Bool × ℕ) where
  δ := 1
  lam := 3
  δ_pos := by norm_num
  lam_gt := by norm_num
  Legit h := h.1 = true
  N h := h.2
  V h := if h.1 = true then 1 / 2 else -(1 / 2)
  V_legit h hl := by
    rw [show h.1 = true from hl]
    norm_num
  V_illegit h hl := by
    have hl' : h.1 = false := by simpa using hl
    rw [hl']
    norm_num

/-- **Theorem 1 is inhabited** in each of its three ranges: a violated history, a
violation-free illegitimate one, a violation-free legitimate one. -/
theorem theorem1_instance :
    scoring.S (true, 1) ≤ 1 - scoring.lam ∧
      (-scoring.δ ≤ scoring.S (false, 0) ∧ scoring.S (false, 0) < 0) ∧
      (0 ≤ scoring.S (true, 0) ∧ scoring.S (true, 0) ≤ 1) :=
  ⟨scoring.theorem1_violated (true, 1) le_rfl,
    scoring.theorem1_illegitimate (false, 0) rfl (by simp [scoring]),
    scoring.theorem1_legitimate (true, 0) rfl rfl⟩

/-- Three actions: the respecting one, a risky one, a surely violating one. -/
inductive Act
  | respecting
  | risky
  | violating

/-- Continuation histories over a two-state space: the respecting action never violates,
the risky one violates in state `true`, the violating one always. -/
def hist : Act → Bool → Bool × ℕ
  | .respecting, _ => (true, 0)
  | .risky, ω => (true, if ω = true then 1 else 0)
  | .violating, _ => (true, 1)

/-- The decision: a fair coin over `Bool` and the three actions. -/
noncomputable def decision : Decision (Bool × ℕ) Bool Act where
  toScoring := scoring
  μ _ := 1 / 2
  μ_nonneg _ := by norm_num
  μ_sum := by norm_num [Fintype.sum_bool]
  hist := hist

theorem respects : decision.Respects .respecting := by
  intro ω
  simp [decision, scoring, hist]

theorem v_violating : decision.v .violating = 1 := by
  norm_num [Decision.v, expectR, decision, scoring, hist, ind, Fintype.sum_bool]

theorem v_risky : decision.v .risky = 1 / 2 := by
  norm_num [Decision.v, expectR, decision, scoring, hist, ind, Fintype.sum_bool]

theorem U_respecting : decision.U .respecting = 1 / 2 := by
  norm_num [Decision.U, Scoring.S, expectR, decision, scoring, hist, Fintype.sum_bool]

theorem κ_risky : decision.κ .risky .respecting = 0 := by
  norm_num [Decision.κ, Scoring.S, expectR, decision, scoring, hist, ind, Fintype.sum_bool]

/-- **Theorem 2(a)'s hypotheses are inhabited**: the respecting action respects authority
and the violating action violates with probability one. -/
theorem theorem2a_package : decision.Respects .respecting ∧ decision.v .violating = 1 :=
  ⟨respects, v_violating⟩

/-- **Theorem 2(b)'s strict hypothesis is inhabited**: `v a > κ/(λ − (1 + δ))` for the
risky action against the respecting one (`1/2 > 0`). -/
theorem theorem2b_package :
    decision.Respects .respecting ∧
      decision.v .risky > decision.κ .risky .respecting / (decision.lam - (1 + decision.δ)) :=
  ⟨respects, by rw [v_risky, κ_risky]; norm_num [decision, scoring]⟩

/-- **Theorem 2(c)'s hypothesis is inhabited**: `v a > (1 − U a*)/λ` for the risky action
(`1/2 > 1/6`). -/
theorem theorem2c_package :
    decision.Respects .respecting ∧
      decision.v .risky > (1 - decision.U .respecting) / decision.lam :=
  ⟨respects, by rw [v_risky, U_respecting]; norm_num [decision, scoring]⟩

/-- **Theorem 2 on the instance**: the respecting action beats the risky one, and beats the
violating one by at least `λ − (1 + δ) = 1`. -/
theorem theorem2_instance :
    decision.U .respecting > decision.U .risky ∧
      decision.U .respecting - decision.U .violating ≥ decision.lam - (1 + decision.δ) :=
  ⟨decision.theorem2c _ _ theorem2c_package.2,
    decision.theorem2a _ _ theorem2a_package.1 theorem2a_package.2⟩

/-- **Theorem 2(b), strict form, on the instance**, through its own hypothesis package. -/
theorem theorem2b_instance : decision.U .respecting > decision.U .risky :=
  decision.theorem2b_strict _ _ theorem2b_package.1 theorem2b_package.2

/-- A sequence with estimates equal to realized scores: every action available, the
estimate `1/2` everywhere, the realized evaluation `1/2`, no violations, `δ = 1`, `λ = 3`. -/
noncomputable def sequential : Sequential Bool where
  δ := 1
  lam := 3
  δ_pos := by norm_num
  lam_gt := by norm_num
  V _ := 1 / 2
  N _ := 0
  V_le_one _ := by norm_num
  avail _ _ := True
  U _ _ := 1 / 2
  a _ := true
  astar _ := false
  astar_avail _ := trivial
  astar_range _ := by norm_num

theorem sequential_maximizes : sequential.Maximizes := by
  intro k a' _
  simp [sequential]

theorem sequential_excess (K : ℕ) : sequential.excess sequential.a K = 0 := by
  simp [Sequential.excess, Sequential.S, sequential]

/-- **Unbiasedness From Feedback holds** on the sequence: every excess is zero. -/
theorem sequential_unbiased : sequential.UnbiasedFromFeedback := by
  intro γ hγ
  exact ⟨0, fun K _ => by rw [sequential_excess]; exact hγ.le⟩

/-- **Theorem 3's hypothesis package is inhabited**, and its conclusions hold on the
instance. -/
theorem theorem3_instance :
    sequential.Maximizes ∧ sequential.UnbiasedFromFeedback ∧
      LimsupLE (fun K => sequential.R K - sequential.T K) 0 ∧
      LimsupLE sequential.R sequential.τ ∧
      LimsupLE (sequential.excess fun _ => false) 0 :=
  ⟨sequential_maximizes, sequential_unbiased,
    sequential.theorem3a sequential_maximizes sequential_unbiased,
    sequential.theorem3a_rate sequential_maximizes sequential_unbiased,
    sequential.theorem3b sequential_maximizes sequential_unbiased _ fun _ => trivial⟩

/-- The same sequence exploring at `k = 0`, with `θ = 1/10`. -/
noncomputable def exploration : Exploration Bool where
  toSequential := sequential
  θ := 1 / 10
  θ_nonneg := by norm_num
  θ_lt_one := by norm_num
  E k := decide (k = 0)
  maximizes_off _ _ _ _ := by simp [sequential]
  explore_bound _ _ := by norm_num [sequential]
  U_le_one _ _ _ := by norm_num [sequential]

theorem exploration_E (k : ℕ) : exploration.E k = decide (k = 0) := rfl

theorem exploration_explores : exploration.E 0 = true := rfl

theorem exploration_unbiased : exploration.UnbiasedFromFeedback := sequential_unbiased

theorem exploration_ε_le (K : ℕ) : exploration.ε K ≤ 1 / (K : ℝ) := by
  unfold Exploration.ε
  have hsub : ((range K).filter fun k => exploration.E k = true) ⊆ {0} := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_singleton]
    have h := hx.2
    rw [exploration_E, decide_eq_true_eq] at h
    exact h
  have hcard : ((range K).filter fun k => exploration.E k = true).card ≤ 1 :=
    (Finset.card_le_card hsub).trans (by simp)
  have hcard' : (((range K).filter fun k => exploration.E k = true).card : ℝ) ≤ 1 := by
    exact_mod_cast hcard
  exact div_le_div_same_denom hcard' (Nat.cast_nonneg K)

/-- **`ε_K → 0`** on the exploring sequence. -/
theorem exploration_ε_limsup : LimsupLE exploration.ε 0 := by
  intro γ hγ
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hγ
  refine ⟨n + 1, fun K hK => ?_⟩
  have hK' : ((n : ℝ) + 1) ≤ K := by exact_mod_cast hK
  have h1 : 1 / (K : ℝ) ≤ 1 / ((n : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) hK'
  have h2 := exploration_ε_le K
  rw [zero_add]
  linarith

/-- **The Corollary's hypothesis package is inhabited**, with exploration occurring at
`k = 0` and `ε_K → 0`; its conclusions, and the specialization, hold on the instance. -/
theorem corollary_instance :
    exploration.E 0 = true ∧ exploration.UnbiasedFromFeedback ∧ LimsupLE exploration.ε 0 ∧
      LimsupLE (fun K => exploration.R K - exploration.T K
        - exploration.ε K * (exploration.τ + exploration.θ)) 0 ∧
      LimsupLE (fun K => exploration.excess (fun _ => false) K
        - exploration.ε K * (exploration.lam * (exploration.τ + exploration.θ))) 0 ∧
      LimsupLE (fun K => exploration.R K - exploration.T K) 0 :=
  ⟨exploration_explores, exploration_unbiased, exploration_ε_limsup,
    exploration.corollary_a exploration_unbiased,
    exploration.corollary_b exploration_unbiased _ fun _ => trivial,
    (exploration.corollary_limit exploration_unbiased exploration_ε_limsup).1⟩

end Witness

end Workspace.Deference.Contrib.DeconfusingCorrigibility

#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Params.lam_mul_τ
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.div_le_div_same_denom
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Scoring.theorem1_violated
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Scoring.theorem1_gap
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Scoring.theorem1_illegitimate
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Scoring.theorem1_legitimate
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Scoring.theorem1
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.expectR_mono
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.expectR_sub
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.expectR_const_mul
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.expectR_const
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Decision.U_le
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Decision.neg_δ_le_U
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Decision.theorem2a
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Decision.theorem2a_pos
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Decision.theorem2b
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Decision.theorem2b_strict
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Decision.theorem2c
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Decision.theorem2c_tau
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.LimsupLE.of_le
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.LimsupLE.add
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.LimsupLE.add_const
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.LimsupLE.mul_const
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Sequential.unbiased_of_weighted
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Sequential.limsup_of_unbiased
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Sequential.limsup_excess_div
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Sequential.N_sub_t_le
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Sequential.t_le_τ
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Sequential.T_le_τ
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Sequential.rate_le_excess
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Sequential.excess_le_excess
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Sequential.theorem3a
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Sequential.theorem3a_rate
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Sequential.theorem3b
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Exploration.N_sub_t_le_expl
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Exploration.excess_pt
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Exploration.rate_le_expl
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Exploration.excess_le_expl
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Exploration.corollary_a
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Exploration.corollary_b
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Exploration.corollary_limit
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Witness.scoring
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Witness.theorem1_instance
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Witness.decision
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Witness.respects
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Witness.v_violating
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Witness.v_risky
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Witness.U_respecting
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Witness.κ_risky
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Witness.theorem2a_package
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Witness.theorem2b_package
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Witness.theorem2c_package
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Witness.theorem2_instance
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Witness.theorem2b_instance
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Witness.sequential
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Witness.sequential_maximizes
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Witness.sequential_unbiased
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Witness.theorem3_instance
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Witness.exploration
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Witness.exploration_E
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Witness.exploration_explores
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Witness.exploration_unbiased
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Witness.exploration_ε_le
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Witness.exploration_ε_limsup
#print axioms Workspace.Deference.Contrib.DeconfusingCorrigibility.Witness.corollary_instance

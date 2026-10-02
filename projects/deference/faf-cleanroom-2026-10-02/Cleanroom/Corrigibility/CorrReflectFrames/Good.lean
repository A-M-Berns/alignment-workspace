import Cleanroom.Corrigibility.CorrReflectFrames.Selection

/-!
# corr-reflect-frames — T10: Good's theorem for refinements; VOI convexity (Prop 5′)

Finite Jensen for `max` (`sup'_sum_le_sum_sup'`); Good's theorem for every estimate-matching
frame (refinements in particular): the expected best action under the future rows is at least
the best action under the prior; joint-final Prop 5′: under a martingale family of posteriors
the expected residual value of information is at most the prior's ("legitimate feedback" *means*
the martingale identity here, nothing else). Witnesses in `Witnesses.lean`.
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- **Finite Jensen for `max`**: for nonnegative weights `p` on a finite `S` and a finite nonempty
menu `A`, `max_a ∑_s p s · v s a ≤ ∑_s p s · max_a v s a`.
Source: [[armstrong]] I6.2 l. 143 ("Jensen on the convex function `max_a`"); [[joint-final]]
P.5′ l. 176
Kind: P
Fidelity: exact
Hyps: (a) `0 ≤ p` only (no normalization needed) -/
theorem sup'_sum_le_sum_sup' {S A : Type} [Fintype S] [Fintype A] (hA : (univ : Finset A).Nonempty)
    {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (v : S → A → ℝ) :
    univ.sup' hA (fun a => ∑ s, p s * v s a) ≤ ∑ s, p s * univ.sup' hA (fun a => v s a) := by
  rw [sup'_le_iff]
  intro a _
  apply sum_le_sum
  intro s _
  exact mul_le_mul_of_nonneg_left (le_sup' (fun a => v s a) (mem_univ a)) (hp s)

/-- **Good's theorem for estimate-matching frames** (refinements included): for a menu
`u : A → W → ℝ`, `max_a E_π(u a) ≤ ∑ w, π w · max_a E_{P_w}(u a)` — the expected value of
choosing after the transition is at least the value of choosing now.
Source: [[armstrong]] I6.2 l. 143 (`E_{ρ_i}(max_a E_{ρ_j}(u_a)) ≥ max_a E_{ρ_i}(u_a)`);
[[joint-final]] Prop 5′ l. 112 (Good)
Kind: P
Fidelity: exact (stated for every estimate-matching frame; refinements by
`refineFrame_estimateMatching`)
Hyps: (a) `0 ≤ π`, estimate matching -/
theorem good_of_estimateMatching {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    (h : EstimateMatching π F) {A : Type} [Fintype A] (hA : (univ : Finset A).Nonempty)
    (u : A → W → ℝ) :
    univ.sup' hA (fun a => E π (u a)) ≤ ∑ w, π w * univ.sup' hA (fun a => E (F.P w) (u a)) := by
  have e : (fun a => E π (u a)) = fun a => ∑ w, π w * E (F.P w) (u a) := by
    funext a; rw [h (u a)]
  rw [e]
  exact sup'_sum_le_sum_sup' hA hπ (fun w a => E (F.P w) (u a))

/-- **Good's theorem for Bayesian refinements**, explicit form.
Source: [[armstrong]] I6.2 l. 143
Kind: C
Fidelity: exact
Hyps: (a) `0 ≤ π` only -/
theorem good_refineFrame {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {S : Type} [DecidableEq S] (f : W → S)
    {A : Type} [Fintype A] (hA : (univ : Finset A).Nonempty) (u : A → W → ℝ) :
    univ.sup' hA (fun a => E π (u a)) ≤
      ∑ w, π w * univ.sup' hA (fun a => E ((refineFrame π hπ f).P w) (u a)) :=
  good_of_estimateMatching hπ (refineFrame_estimateMatching hπ f) hA u

/-- **Refinements are valued** (Good's theorem in DDB's Value form): `Value π (refineFrame π f)`.
Source: [[armstrong]] I6.2 l. 143; DDB Theorem 2.2 via `lit-ddb-frames`
Kind: C
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` only -/
theorem refineFrame_value {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {S : Type} [DecidableEq S]
    (f : W → S) : Value π (refineFrame π hπ.1 f) :=
  (value_iff_totalTrust hπ _).2 (refineFrame_totalTrust hπ.1 f)

/-! ## Prop 5′: legitimate feedback lowers the expected residual value of information -/

/-- **Value of information** of learning `θ` under a posterior `π`, for a menu `V : K → Θ → ℝ`:
`∑_θ π θ · max_k V k θ − max_k ∑_θ π θ · V k θ`.
Source: [[joint-final]] P.5′ l. 176
Kind: D
Fidelity: exact -/
def voi {Θ K : Type} [Fintype Θ] [Fintype K] (hK : (univ : Finset K).Nonempty) (π : Θ → ℝ)
    (V : K → Θ → ℝ) : ℝ :=
  ∑ θ, π θ * univ.sup' hK (fun k => V k θ) - univ.sup' hK (fun k => ∑ θ, π θ * V k θ)

/-- **Prop 5′.** For posteriors `πₛ` with weights `p` forming a martingale
(`∑_s p s · πₛ s θ = π θ` for every `θ` — this is what "legitimate feedback" means here, and
nothing else), the expected residual VOI is at most the prior's:
`∑_s p s · voi (πₛ s) V ≤ voi π V`. The first term of `voi` is linear in the posterior (equality),
the second is `max` of linear (Jensen, `sup'_sum_le_sum_sup'`).
Source: [[joint-final]] Prop 5′ l. 112, P.5′ ll. 176–178
Kind: P
Fidelity: exact (finite; in expectation over the signal — a single signal can raise the residual,
`Witnesses`)
Hyps: (a) `0 ≤ p`, the martingale identity; no normalization of `π` or `πₛ` is needed -/
theorem sum_voi_le_voi {Θ K S : Type} [Fintype Θ] [Fintype K] [Fintype S]
    (hK : (univ : Finset K).Nonempty) (π : Θ → ℝ) (V : K → Θ → ℝ) {p : S → ℝ}
    (hp : ∀ s, 0 ≤ p s) (πₛ : S → Θ → ℝ) (hmart : ∀ θ, ∑ s, p s * πₛ s θ = π θ) :
    ∑ s, p s * voi hK (πₛ s) V ≤ voi hK π V := by
  unfold voi
  simp only [mul_sub, sum_sub_distrib]
  have e1 : ∑ s, p s * ∑ θ, πₛ s θ * univ.sup' hK (fun k => V k θ) =
      ∑ θ, π θ * univ.sup' hK (fun k => V k θ) := by
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro θ _
    rw [← hmart θ, sum_mul]
    apply sum_congr rfl; intro s _; ring
  have e2 : univ.sup' hK (fun k => ∑ θ, π θ * V k θ) =
      univ.sup' hK (fun k => ∑ s, p s * ∑ θ, πₛ s θ * V k θ) := by
    congr 1; funext k
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro θ _
    rw [← hmart θ, sum_mul]
    apply sum_congr rfl; intro s _; ring
  rw [e1, e2]
  have key : univ.sup' hK (fun k => ∑ s, p s * ∑ θ, πₛ s θ * V k θ) ≤
      ∑ s, p s * univ.sup' hK (fun k => ∑ θ, πₛ s θ * V k θ) :=
    sup'_sum_le_sum_sup' hK hp (fun s k => ∑ θ, πₛ s θ * V k θ)
  linarith

end

end Cleanroom.Corrigibility.CorrReflectFrames

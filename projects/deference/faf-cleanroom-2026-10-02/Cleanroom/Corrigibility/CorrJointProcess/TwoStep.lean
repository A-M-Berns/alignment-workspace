import Cleanroom.Corrigibility.CorrJointProcess.Contents

/-!
# T16(c) — one-step welcome does not compose: the dogmatic content over two steps

`anticipatory-final` Statement 3(b), adv (B): add a third overseer signal `h₃` (likelihoods
`(1/5, 4/5)`) observed before a decision at `t+2`. The successor installed with a *dogmatic*
content `Q_deq ∈ {0, 1}` cannot update on `h₃` (`bayesUpdate_zero`, `bayesUpdate_one`), so its
two-step forced value equals the opaque value — two-step `Δ₋(Q_deq) = 0` — while the refining
content's two-step `Δ₋(Q_post) = 18/625` at `ε = 1/10`, and listening strictly beats the forced
dogmatic content by the same `18/625` (`twoStep_witness`). One-step welcome (`Twists.converse_fails`:
`Δ₋(Q_deq) = 9/500 > 0`) composes into two-step resistance relative to listening — the
counterexample to "non-resistance composes" (open problem 5).

Objects: `pushWorld3` on `World × Bool × Bool × Bool` (`θ, h₁, h₂, h₃`); the two-step cells
`cell3 k₂ k₃` (pushed, `h₂ = k₂`, `h₃ = k₃`) and `cellH3 k₃` (pushed, `h₃ = k₃`); the Bayes update
of a forced belief on `h₃` (`bayesUpdate`); `twoStepForced` (the forced successor updates its
installed belief on `h₃` and decides), `twoStepListen` (best response on `(h₂, h₃)`),
`twoStepOpaque` (best response on `h₃` alone, the push noticed), `twoStepMarginMinus`.

Sources: anticipatory-final.md Statement 3(b), P4 (adv (B), re-run); anticipatory.md Contents (A).
-/

namespace Cleanroom.Corrigibility.CorrJointProcess

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

set_option linter.unusedSectionVars false

/-- The three-signal push-world: `θ` with `P(wrong) = ε`, independent binary signals `h₁ (α, β)`,
`h₂ (a₂, b₂)`, `h₃ (a₃, b₃)` given `θ`.
Source: [[corr-wf14b-inventory]] 019 / anticipatory-final.md P4 (adv (B))
Kind: D
Fidelity: exact -/
noncomputable def pushWorld3 (ε α β a₂ b₂ a₃ b₃ : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (ha₂ : a₂ ∈ Set.Icc (0 : ℝ) 1) (hb₂ : b₂ ∈ Set.Icc (0 : ℝ) 1)
    (ha₃ : a₃ ∈ Set.Icc (0 : ℝ) 1) (hb₃ : b₃ ∈ Set.Icc (0 : ℝ) 1) : Distr (World × Bool × Bool × Bool) where
  mass ω := (twoPoint ε hε).mass ω.1 * sigRate (twoPress α β ω.1) ω.2.1 * sigRate (twoPress a₂ b₂ ω.1) ω.2.2.1 *
    sigRate (twoPress a₃ b₃ ω.1) ω.2.2.2
  nonneg ω := by
    obtain ⟨θ, b₁, b₂', b₃'⟩ := ω
    refine mul_nonneg (mul_nonneg (mul_nonneg ((twoPoint ε hε).nonneg _) ?_) ?_) ?_
    · cases θ <;> cases b₁ <;> simp [sigRate, twoPress] <;> linarith [hα.1, hα.2, hβ.1, hβ.2]
    · cases θ <;> cases b₂' <;> simp [sigRate, twoPress] <;> linarith [ha₂.1, ha₂.2, hb₂.1, hb₂.2]
    · cases θ <;> cases b₃' <;> simp [sigRate, twoPress] <;> linarith [ha₃.1, ha₃.2, hb₃.1, hb₃.2]
  sum_eq_one := by
    simp [Fintype.sum_prod_type, World.sum_eq, sigRate, twoPress]
    ring

/-- The pushed worlds with `h₂ = k₂`, `h₃ = k₃`. Source: adv (B). Kind: D. Fidelity: exact -/
def cell3 (k₂ k₃ : Bool) : Finset (World × Bool × Bool × Bool) :=
  univ.filter fun ω => ω.2.1 = true ∧ ω.2.2.1 = k₂ ∧ ω.2.2.2 = k₃

/-- The pushed worlds with `h₃ = k₃` (the opaque successor's information at `t+2`).
Source: adv (B). Kind: D. Fidelity: exact -/
def cellH3 (k₃ : Bool) : Finset (World × Bool × Bool × Bool) :=
  univ.filter fun ω => ω.2.1 = true ∧ ω.2.2.2 = k₃

/-- A sum over `cell3 k₂ k₃`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_cell3 (F : World × Bool × Bool × Bool → ℝ) (k₂ k₃ : Bool) :
    ∑ ω ∈ cell3 k₂ k₃, F ω = F (.right, true, k₂, k₃) + F (.wrong, true, k₂, k₃) := by
  have h : cell3 k₂ k₃ = {(.right, true, k₂, k₃), (.wrong, true, k₂, k₃)} := by
    ext ⟨θ, b₁, b₂, b₃⟩
    cases θ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> cases k₂ <;> cases k₃ <;> simp [cell3]
  rw [h, sum_pair (by simp)]

/-- A sum over `cellH3 k₃`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_cellH3 (F : World × Bool × Bool × Bool → ℝ) (k₃ : Bool) :
    ∑ ω ∈ cellH3 k₃, F ω = (F (.right, true, true, k₃) + F (.wrong, true, true, k₃)) +
      (F (.right, true, false, k₃) + F (.wrong, true, false, k₃)) := by
  have h : cellH3 k₃ = cell3 true k₃ ∪ cell3 false k₃ := by
    ext ⟨θ, b₁, b₂, b₃⟩; cases b₂ <;> simp [cellH3, cell3]
  rw [h, sum_union, sum_cell3, sum_cell3]
  rw [cell3, cell3, disjoint_filter]
  intro ω _ h1 h2; rw [h1.2.1] at h2; exact Bool.noConfusion h2.2.1

/-- **The Bayes update of a forced belief `q = P(W)` on the signal `h₃ = k₃`** with likelihoods
`(a₃, b₃)`: `q ℓ_W/(q ℓ_W + (1−q) ℓ_R)` (junk at a null denominator; the dogmatic values `0`, `1`
are fixed points wherever `ℓ ≠ 0`).
Source: [[corr-wf14b-inventory]] 019 / anticipatory-final.md P4 ("the dogmatic successor cannot move")
Kind: D
Fidelity: exact -/
noncomputable def bayesUpdate (a₃ b₃ q : ℝ) (k₃ : Bool) : ℝ :=
  q * sigRate b₃ k₃ / (q * sigRate b₃ k₃ + (1 - q) * sigRate a₃ k₃)

/-- A dogmatic `0` does not move. Source: adv (B). Kind: L. Fidelity: exact -/
lemma bayesUpdate_zero (a₃ b₃ : ℝ) (k₃ : Bool) : bayesUpdate a₃ b₃ 0 k₃ = 0 := by
  simp [bayesUpdate]

/-- A dogmatic `1` does not move (positive likelihood). Source: adv (B). Kind: L. Fidelity: exact -/
lemma bayesUpdate_one (a₃ b₃ : ℝ) (k₃ : Bool) (hl : sigRate b₃ k₃ ≠ 0) : bayesUpdate a₃ b₃ 1 k₃ = 1 := by
  simp [bayesUpdate, hl]

/-- **The two-step forced value**: on each `(h₂, h₃)` cell the installed belief `belief h₂` is
updated on `h₃` and the argmax taken.
Source: [[corr-wf14b-inventory]] 019 / anticipatory-final.md P4
Kind: D
Fidelity: exact -/
noncomputable def twoStepForced (P : Distr (World × Bool × Bool × Bool)) (c h a₃ b₃ : ℝ) (belief : Bool → ℝ) : ℝ :=
  ∑ k₂, ∑ k₃, ∑ ω ∈ cell3 k₂ k₃, P.mass ω * twoValue c h (actOfBelief c h (bayesUpdate a₃ b₃ (belief k₂) k₃)) ω.1

/-- **The two-step listening value**: the best response on `(h₂, h₃)`.
Source: anticipatory-final.md P4. Kind: D. Fidelity: exact -/
noncomputable def twoStepListen (P : Distr (World × Bool × Bool × Bool)) (c h : ℝ) : ℝ :=
  ∑ k₂, ∑ k₃, max (∑ ω ∈ cell3 k₂ k₃, P.mass ω * twoValue c h .cont ω.1) 0

/-- **The two-step opaque value**: the push noticed, the best response on `h₃` alone.
Source: anticipatory-final.md P4. Kind: D. Fidelity: exact -/
noncomputable def twoStepOpaque (P : Distr (World × Bool × Bool × Bool)) (c h : ℝ) : ℝ :=
  ∑ k₃, max (∑ ω ∈ cellH3 k₃, P.mass ω * twoValue c h .cont ω.1) 0

/-- **The two-step margin** `Δ₋ = V_P − V^op`. Source: anticipatory-final.md P4. Kind: D. Fidelity: exact -/
noncomputable def twoStepMarginMinus (P : Distr (World × Bool × Bool × Bool)) (c h a₃ b₃ : ℝ) (belief : Bool → ℝ) : ℝ :=
  twoStepForced P c h a₃ b₃ belief - twoStepOpaque P c h

/-- **Listening weakly dominates any forced belief over two steps** (T13(a) on the finer partition).
Source: anticipatory-final.md Statement 2(a), P4
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoStepForced_le_twoStepListen (P : Distr (World × Bool × Bool × Bool)) (c h a₃ b₃ : ℝ)
    (belief : Bool → ℝ) : twoStepForced P c h a₃ b₃ belief ≤ twoStepListen P c h := by
  unfold twoStepForced twoStepListen
  refine sum_le_sum fun k₂ _ => sum_le_sum fun k₃ _ => ?_
  unfold actOfBelief
  split_ifs
  · exact le_max_left _ _
  · simp [twoValue]

/-- The witness world: `ε = 1/10`, `(1/10, 9/10)`, `(1/5, 4/5)`, `(1/5, 4/5)`.
Source: anticipatory-final.md P4 (adv (B)). Kind: D. Fidelity: exact -/
noncomputable def w3 : Distr (World × Bool × Bool × Bool) :=
  pushWorld3 (1 / 10) (1 / 10) (9 / 10) (1 / 5) (4 / 5) (1 / 5) (4 / 5) mem_Icc_1_10 mem_Icc_1_10
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩

/-- The one-step posteriors `Q_post(h₂)` are `1/5` and `4/5` (as in `Twists.twist_post`), so the
dogmatic content is `Q_deq(false) = 0`, `Q_deq(true) = 1`.
Source: anticipatory.md Contents (A). Kind: D. Fidelity: exact -/
noncomputable def qPost3 : Bool → ℝ := fun k => if k then 4 / 5 else 1 / 5

/-- The dogmatic content carrying `Q_post`'s verdict. Source: anticipatory.md Contents (A). Kind: D. Fidelity: exact -/
noncomputable def qDeq3 : Bool → ℝ := fun k => if actOfBelief 1 3 (qPost3 k) = .stop then 1 else 0

/-- **T16(c) (Statement 3(b), adv (B)): one-step welcome does not compose.** At `ε = 1/10`,
`c = 1`, `h = 3`: two-step `Δ₋(Q_deq) = 0` while `Δ₋(Q_post) = 18/625`, and listening beats the
forced dogmatic content by `18/625` — the dogmatic successor cannot use `h₃`.
Source: [[corr-wf14b-inventory]] 019 / anticipatory-final.md Statement 3(b), P4 (row `ε = 1/10`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem twoStep_witness :
    twoStepMarginMinus w3 1 3 (1 / 5) (4 / 5) qDeq3 = 0 ∧
      twoStepMarginMinus w3 1 3 (1 / 5) (4 / 5) qPost3 = 18 / 625 ∧
      twoStepListen w3 1 3 - twoStepForced w3 1 3 (1 / 5) (4 / 5) qDeq3 = 18 / 625 := by
  simp only [twoStepMarginMinus, twoStepForced, twoStepListen, twoStepOpaque, Fintype.sum_bool, sum_cell3,
    sum_cellH3]
  norm_num [w3, pushWorld3, sigRate, twoPress, twoValue, actOfBelief, bayesUpdate, qPost3, qDeq3]

end Cleanroom.Corrigibility.CorrJointProcess

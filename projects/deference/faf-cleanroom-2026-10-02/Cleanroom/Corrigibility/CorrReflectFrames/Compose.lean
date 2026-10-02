import Cleanroom.Corrigibility.CorrReflectFrames.Legit

/-!
# corr-reflect-frames — T7: legitimacy composes at function-form grade

Three-time setting on one `W`: `π` (`t₁`), `F₂` (`t₂`), `F₃` (`t₃`). Function-form reflection
conditional on `L₁₂` at the first step and value-form legitimacy of `L₂₃` by each `t₂`-state's
lights at the second step give value-form legitimacy of `L₁₂ ∩ L₂₃` across the two steps
(radical I5.6(c), joint-final Prop 7). The value-form-only hypothesis at step one does **not**
compose: `Witnesses` (the `s5` frame). The mechanism is `mass_eq_sum_cells`: under Reflection
the deferrer is the mixture of its candidates weighted by their cells.
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W] {π : W → ℝ}

/-- **The mixture identity under Reflection.** A reflecting deferrer is the cell-weighted mixture
of the rows: `π(A) = ∑_ρ π(P = ρ) · ρ(A)` for every event `A`.
Source: [[radical]] Theorem I3.3(a) l. 107 (total probability over the meta-belief events),
I5.6(c) proof ("average over `ρ`")
Kind: P
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem mass_eq_sum_cells (hπ : ∀ w, 0 ≤ π w) {F : Frame W} (h : Reflects π F) (A : Finset W) :
    mass π A = ∑ ρ ∈ univ.image F.P, mass π (F.cell ρ) * mass ρ A := by
  show ∑ w ∈ A, π w = _
  rw [sum_eq_sum_mul_ind π A, sum_rowClosed F (fun _ _ _ _ => mem_univ _) (fun w => π w * ind A w)]
  apply sum_congr rfl
  intro ρ _
  rw [reflects_cell_sum hπ h ρ (ind A), E_ind]

/-- **I5.6(c) / Prop 7: function form composes.** If `π` reflects `F₂` conditional on `L₁₂`
(function form) and every `t₂`-candidate `ρ` of the restricted deferrer has `L₂₃`
legitimizing for `φ` toward `F₃` (value form, by `ρ`'s own lights), then `L₁₂ ∩ L₂₃` is
legitimizing for `φ` from `t₁` to `t₃`.
Source: [[radical]] Theorem I5.6(c) l. 175; [[joint-final]] Prop 7 l. 128; [[joint]] P.8 l. 217
Kind: P
Fidelity: exact
Scope: no introspection hypothesis — INT at the `t₂`-candidates of the restricted deferrer is a
consequence of the step-one Reflection hypothesis (Theorem A(c),
`candsIntrospective_of_reflects`), not an assumption; positive witness with proper `L₁₂`, `L₂₃`
and strictly finer `F₃`: `Witnesses.compose_positive_witness`; negative: `s5`
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem legitimizingVal_compose (hπ : ∀ w, 0 ≤ π w) {F₂ F₃ : Frame W} {φ L₁₂ L₂₃ : Finset W}
    (h₁₂ : Reflects (restrict π L₁₂) F₂)
    (h₂₃ : ∀ ρ ∈ F₂.cands (restrict π L₁₂), LegitimizingVal ρ F₃ φ L₂₃) :
    LegitimizingVal π F₃ φ (L₁₂ ∩ L₂₃) := by
  intro c
  have hπ' := restrict_nonneg hπ L₁₂
  have e1 : mass π (φ ∩ (L₁₂ ∩ L₂₃) ∩ valCell F₃ φ c) =
      mass (restrict π L₁₂) (φ ∩ L₂₃ ∩ valCell F₃ φ c) := by
    rw [mass_restrict]; congr 1; ext w; simp only [mem_inter]; tauto
  have e2 : mass π ((L₁₂ ∩ L₂₃) ∩ valCell F₃ φ c) =
      mass (restrict π L₁₂) (L₂₃ ∩ valCell F₃ φ c) := by
    rw [mass_restrict]; congr 1; ext w; simp only [mem_inter]; tauto
  rw [e1, e2, mass_eq_sum_cells hπ' h₁₂, mass_eq_sum_cells hπ' h₁₂, mul_sum]
  apply sum_congr rfl
  intro ρ _
  by_cases hρ : ρ ∈ F₂.cands (restrict π L₁₂)
  · rw [h₂₃ ρ hρ c]; ring
  · rw [mass_cell_eq_zero_of_not_mem_cands hπ' F₂ hρ]; ring

/-- **Composition with `L₁₂ = L₂₃ = Ω`.** Reflection at step one and value-form reflection for
`φ` by every candidate's lights at step two give unconditional value-form reflection for `φ`
across the two steps.
Source: [[radical]] Theorem I5.6(c) l. 175 (unconditional instance)
Kind: C
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem valueReflectsOn_compose (hπ : ∀ w, 0 ≤ π w) {F₂ F₃ : Frame W} {φ : Finset W}
    (h₁₂ : Reflects π F₂) (h₂₃ : ∀ ρ ∈ F₂.cands π, ValueReflectsOn ρ F₃ φ) :
    ValueReflectsOn π F₃ φ := by
  rw [← legitimizingVal_univ_iff, ← univ_inter univ]
  apply legitimizingVal_compose hπ
  · rw [restrict_univ]; exact h₁₂
  · intro ρ hρ
    rw [restrict_univ] at hρ
    rw [legitimizingVal_univ_iff]
    exact h₂₃ ρ hρ

/-- **Transport of a conditional expectation under function form (T16(a)'s mechanism).** Under
Reflection conditional on `L`, for a candidate `ρ` and any event `Pr`,
`∑_{[P = ρ] ∩ L ∩ Pr} π w · X w = π([P = ρ] ∩ L) · ∑_{Pr} ρ w · X w` — the conditional of `π`
on `[P = ρ] ∩ L` *is* `ρ`, so `E_π[X | cell ρ ∩ L ∩ Pr] ≤ 0 ↔ E_ρ[X | Pr] ≤ 0` once both
conditioning events are positive.
Source: [[joint-adversary]] A.13.1 l. 107; [[joint]] P.7 l. 211
Kind: L
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem reflects_restrict_cell_sum (hπ : ∀ w, 0 ≤ π w) {F : Frame W} {L : Finset W}
    (h : Reflects (restrict π L) F) {ρ : W → ℝ} (hρ : ρ ∈ F.cands (restrict π L))
    (Pr : Finset W) (X : W → ℝ) :
    ∑ w ∈ F.cell ρ ∩ L ∩ Pr, π w * X w =
      mass π (F.cell ρ ∩ L) * ∑ w ∈ Pr, ρ w * X w := by
  have hπ' := restrict_nonneg hπ L
  have key := reflects_cell_sum hπ' h ρ (fun w => X w * ind Pr w)
  rw [mass_restrict] at key
  have e1 : ∑ w ∈ F.cell ρ, restrict π L w * (X w * ind Pr w) =
      ∑ w ∈ F.cell ρ ∩ L ∩ Pr, π w * X w := by
    simp only [restrict_apply, ind, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    rw [← sum_filter, ← sum_filter, filter_mem_eq_inter, filter_mem_eq_inter]
    apply sum_congr _ (fun _ _ => rfl)
    ext w; simp only [mem_inter]; tauto
  have e2 : E ρ (fun w => X w * ind Pr w) = ∑ w ∈ Pr, ρ w * X w := by
    unfold E
    simp only [ind, mul_ite, mul_one, mul_zero]
    rw [sum_ite_mem, univ_inter]
  rw [e1, e2] at key
  exact key

/-- **Conditioning on a `t₂`-measurable event preserves function form.** If `π` reflects `F` and
`L` is a union of cells of `F` (every cell that meets `L` lies inside it), then the restricted
deferrer `π · 𝟙_L` reflects `F` too: a candidate of the restriction has its cell inside `L`, so
both sides of the product identity are unchanged by the restriction. This is the step-one
hypothesis of `legitimizingVal_compose` for a proper `L₁₂` (positive witness, `WitnessesE`).
Source: [[radical]] I5.6(c) l. 175 ("function form conditional on `L₁₂`"); mandate T7
Kind: P
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w`, `Reflects π F`, `L` a union of cells -/
theorem reflects_restrict_of_cells_subset (hπ : ∀ w, 0 ≤ π w) {F : Frame W} (h : Reflects π F)
    {L : Finset W} (hL : ∀ w ∈ L, F.cell (F.P w) ⊆ L) : Reflects (restrict π L) F := by
  intro ρ hρ w
  obtain ⟨w₀, hw₀, rfl⟩ := Frame.mem_cands.1 hρ
  have hw₀L : w₀ ∈ L := by
    by_contra hn
    rw [restrict_apply, if_neg hn] at hw₀
    exact lt_irrefl _ hw₀
  have hπw₀ : 0 < π w₀ := by rw [restrict_apply, if_pos hw₀L] at hw₀; exact hw₀
  have hsub := hL w₀ hw₀L
  have key := h _ (Frame.P_mem_cands F hπw₀) w
  rw [mass_restrict, inter_eq_left.2 hsub]
  by_cases hw : w ∈ F.cell (F.P w₀)
  · rw [restrict_apply, if_pos (hsub hw)]
    exact key
  · have hz : ind (F.cell (F.P w₀)) w = 0 := by simp [ind, hw]
    rw [hz, mul_zero] at key ⊢
    exact key

end

end Cleanroom.Corrigibility.CorrReflectFrames

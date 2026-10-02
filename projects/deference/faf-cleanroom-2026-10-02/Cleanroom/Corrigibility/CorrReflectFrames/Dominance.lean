import Cleanroom.Corrigibility.CorrReflectFrames.Twist
import Cleanroom.Corrigibility.CorrReflectFrames.Good

/-!
# corr-reflect-frames — T9(e): the twisted successor is weakly dominated by the refinement

corr-wf14-051 / selection.md R2.4 ("Armstrong's `E`-channel is closed"): for a world-indexed
payoff `u : A → W → ℝ`, any successor whose rows are constant on the cells of a partition `f`
(the twisted estimators are; so is any function of the refinement's rows) chooses, under any
tie-break, an action that is constant on the positive part of each cell, and its `π`-expected
payoff is at most the refinement's `∑ w, π w · max_a E_{π(·|f w)}(u a)` — which the refinement's
own cellwise maximizer attains. The mechanism: on each positive cell the choice's payoff is the
cell mass times the conditional expectation of its payoff, and the conditional expectation is at
most the cellwise maximum. Belief-indexed payoffs (where the twisted successor can strictly win,
`65/24` vs `5/12`) are outside this statement (stretch, not built).
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W] {S : Type} [DecidableEq S] {π : W → ℝ}

/-- Expectation under a positive conditional row, product form: `E_{π(·|f w)}(X) · π(f = f w) =
∑_{f v = f w} π v · X v`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condRow_E_mul {f : W → S} {w : W} (h : 0 < mass π (fibre f w)) (X : W → ℝ) :
    E (condRow π f w) X * mass π (fibre f w) = ∑ v ∈ fibre f w, π v * X v := by
  have e : ∑ v ∈ fibre f w, π v * X v = ∑ v, ind (fibre f w) v * (π v * X v) := by
    simp only [ind, ite_mul, one_mul, zero_mul]
    rw [sum_ite_mem, univ_inter]
  rw [e]
  unfold E
  rw [sum_mul]
  apply sum_congr rfl
  intro v _
  rw [condRow_apply_of_pos h]
  have hne := h.ne'
  field_simp

/-- On a positive cell, a choice constant on the cell's positive worlds (value `a₀`) scores the
cell mass times the conditional expectation of `u a₀`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_fibre_choice_eq (hπ : ∀ w, 0 ≤ π w) {f : W → S} {w₀ : W}
    (h : 0 < mass π (fibre f w₀)) {A : Type} (u : A → W → ℝ) {act : W → A} {a₀ : A}
    (hact : ∀ v ∈ fibre f w₀, 0 < π v → act v = a₀) :
    ∑ v ∈ fibre f w₀, π v * u (act v) v = mass π (fibre f w₀) * E (condRow π f w₀) (u a₀) := by
  rw [mul_comm, condRow_E_mul h]
  apply sum_congr rfl
  intro v hv
  by_cases hv0 : 0 < π v
  · rw [hact v hv hv0]
  · have hz : π v = 0 := le_antisymm (not_lt.1 hv0) (hπ v)
    simp [hz]

/-- Grouping a sum over `W` by the cells of `f`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_eq_sum_fibres (f : W → S) (g : W → ℝ) :
    ∑ w, g w = ∑ x ∈ univ.image f, ∑ w ∈ univ.filter (fun w => f w = x), g w :=
  (sum_fiberwise_of_maps_to (fun w _ => mem_image_of_mem f (mem_univ w)) g).symm

/-- **Cell-constant choices are weakly dominated by the refinement** (corr-wf14-051, R2.4): for
a world-indexed payoff `u`, any action rule `act` that is constant on the `π`-positive part of
each `f`-cell has expected payoff at most `∑ w, π w · max_a E_{π(·|f w)}(u a)`, the value of
choosing after the Bayesian refinement.
Source: [[selection]] R2.4 l. 55 (twisted successor weakly dominated); [[armstrong]] I6.2
l. 143; corr-wf14-051
Kind: P
Fidelity: exact (constancy required only on positive worlds; null worlds contribute nothing)
Hyps: (a) `∀ w, 0 ≤ π w`, cell-constancy of the rule -/
theorem cellConstant_choice_le_refineFrame_value (hπ : ∀ w, 0 ≤ π w) (f : W → S) {A : Type}
    [Fintype A] (hA : (univ : Finset A).Nonempty) (u : A → W → ℝ) (act : W → A)
    (hact : ∀ v w, f v = f w → 0 < π v → 0 < π w → act v = act w) :
    ∑ w, π w * u (act w) w ≤
      ∑ w, π w * univ.sup' hA (fun a => E ((refineFrame π hπ f).P w) (u a)) := by
  rw [sum_eq_sum_fibres f (fun w => π w * u (act w) w),
    sum_eq_sum_fibres f (fun w => π w * univ.sup' hA (fun a => E ((refineFrame π hπ f).P w) (u a)))]
  apply sum_le_sum
  intro x hx
  obtain ⟨w₀, _, rfl⟩ := mem_image.1 hx
  change ∑ v ∈ fibre f w₀, _ ≤ ∑ v ∈ fibre f w₀, _
  by_cases hpos : 0 < mass π (fibre f w₀)
  · obtain ⟨v₀, hv₀, hv₀pos⟩ := (mass_pos_iff hπ).1 hpos
    have hrow : ∀ v ∈ fibre f w₀, (refineFrame π hπ f).P v = condRow π f w₀ :=
      fun v hv => condRow_eq_of_mem hpos hv
    have hconst : ∀ v ∈ fibre f w₀, 0 < π v → act v = act v₀ := fun v hv hvpos =>
      hact v v₀ ((mem_fibre.1 hv).trans (mem_fibre.1 hv₀).symm) hvpos hv₀pos
    rw [sum_fibre_choice_eq hπ hpos u hconst]
    have e : ∑ v ∈ fibre f w₀, π v * univ.sup' hA (fun a => E ((refineFrame π hπ f).P v) (u a)) =
        mass π (fibre f w₀) * univ.sup' hA (fun a => E (condRow π f w₀) (u a)) := by
      rw [mass, sum_mul]
      apply sum_congr rfl
      intro v hv
      rw [hrow v hv]
    rw [e]
    exact mul_le_mul_of_nonneg_left
      (le_sup' (fun a => E (condRow π f w₀) (u a)) (mem_univ _)) hpos.le
  · have h0 : mass π (fibre f w₀) = 0 := le_antisymm (not_lt.1 hpos) (mass_nonneg hπ _)
    have hz : ∀ v ∈ fibre f w₀, π v = 0 := fun v hv => eq_zero_of_mass_eq_zero hπ h0 hv
    have l0 : ∑ v ∈ fibre f w₀, π v * u (act v) v = 0 :=
      sum_eq_zero (fun v hv => by rw [hz v hv, zero_mul])
    have r0 : ∑ v ∈ fibre f w₀,
        π v * univ.sup' hA (fun a => E ((refineFrame π hπ f).P v) (u a)) = 0 :=
      sum_eq_zero (fun v hv => by rw [hz v hv, zero_mul])
    rw [l0, r0]

/-- **The refinement's cellwise maximizer attains the bound**: a rule that is cell-constant and
maximizes `E_{π(·|f w)}(u a)` at every positive world has expected payoff exactly
`∑ w, π w · max_a E_{π(·|f w)}(u a)`. With `cellConstant_choice_le_refineFrame_value`: the
refinement's action weakly dominates every cell-constant rule, the twisted successor's included.
Source: [[selection]] R2.4 l. 55; corr-wf14-051
Kind: P
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w`, cell-constancy, cellwise maximality -/
theorem sum_maximizer_eq_refineFrame_value (hπ : ∀ w, 0 ≤ π w) (f : W → S) {A : Type}
    [Fintype A] (hA : (univ : Finset A).Nonempty) (u : A → W → ℝ) (act : W → A)
    (hact : ∀ v w, f v = f w → 0 < π v → 0 < π w → act v = act w)
    (hmax : ∀ w, 0 < π w → ∀ a,
      E ((refineFrame π hπ f).P w) (u a) ≤ E ((refineFrame π hπ f).P w) (u (act w))) :
    ∑ w, π w * u (act w) w =
      ∑ w, π w * univ.sup' hA (fun a => E ((refineFrame π hπ f).P w) (u a)) := by
  rw [sum_eq_sum_fibres f (fun w => π w * u (act w) w),
    sum_eq_sum_fibres f (fun w => π w * univ.sup' hA (fun a => E ((refineFrame π hπ f).P w) (u a)))]
  apply sum_congr rfl
  intro x hx
  obtain ⟨w₀, _, rfl⟩ := mem_image.1 hx
  change ∑ v ∈ fibre f w₀, _ = ∑ v ∈ fibre f w₀, _
  by_cases hpos : 0 < mass π (fibre f w₀)
  · obtain ⟨v₀, hv₀, hv₀pos⟩ := (mass_pos_iff hπ).1 hpos
    have hrow : ∀ v ∈ fibre f w₀, (refineFrame π hπ f).P v = condRow π f w₀ :=
      fun v hv => condRow_eq_of_mem hpos hv
    have hconst : ∀ v ∈ fibre f w₀, 0 < π v → act v = act v₀ := fun v hv hvpos =>
      hact v v₀ ((mem_fibre.1 hv).trans (mem_fibre.1 hv₀).symm) hvpos hv₀pos
    rw [sum_fibre_choice_eq hπ hpos u hconst]
    have e : ∑ v ∈ fibre f w₀, π v * univ.sup' hA (fun a => E ((refineFrame π hπ f).P v) (u a)) =
        mass π (fibre f w₀) * univ.sup' hA (fun a => E (condRow π f w₀) (u a)) := by
      rw [mass, sum_mul]
      apply sum_congr rfl
      intro v hv
      rw [hrow v hv]
    rw [e]
    congr 1
    apply le_antisymm
    · exact le_sup' (fun a => E (condRow π f w₀) (u a)) (mem_univ _)
    · rw [sup'_le_iff]
      intro a _
      have := hmax v₀ hv₀pos a
      rw [hrow v₀ hv₀] at this
      exact this
  · have h0 : mass π (fibre f w₀) = 0 := le_antisymm (not_lt.1 hpos) (mass_nonneg hπ _)
    have hz : ∀ v ∈ fibre f w₀, π v = 0 := fun v hv => eq_zero_of_mass_eq_zero hπ h0 hv
    have l0 : ∑ v ∈ fibre f w₀, π v * u (act v) v = 0 :=
      sum_eq_zero (fun v hv => by rw [hz v hv, zero_mul])
    have r0 : ∑ v ∈ fibre f w₀,
        π v * univ.sup' hA (fun a => E ((refineFrame π hπ f).P v) (u a)) = 0 :=
      sum_eq_zero (fun v hv => by rw [hz v hv, zero_mul])
    rw [l0, r0]

/-- **Any frame with rows constant on the `f`-cells is weakly dominated by the refinement**: a
successor `σ` whose rows are constant on the positive part of each cell, acting through any
tie-break `choose : (W → ℝ) → A` applied to its row, has expected world-indexed payoff at most
the refinement's.
Source: [[selection]] R2.4 l. 55; corr-wf14-051
Kind: C
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w`, rows constant on positive cells -/
theorem rowsConstant_choice_le_refineFrame_value (hπ : ∀ w, 0 ≤ π w) (f : W → S)
    {σ : Frame W} (hσ : ∀ v w, f v = f w → 0 < π v → 0 < π w → σ.P v = σ.P w) {A : Type}
    [Fintype A] (hA : (univ : Finset A).Nonempty) (u : A → W → ℝ) (choose : (W → ℝ) → A) :
    ∑ w, π w * u (choose (σ.P w)) w ≤
      ∑ w, π w * univ.sup' hA (fun a => E ((refineFrame π hπ f).P w) (u a)) :=
  cellConstant_choice_le_refineFrame_value hπ f hA u (fun w => choose (σ.P w))
    (fun v w h hv hw => by rw [hσ v w h hv hw])

/-- **The twisted successor is weakly dominated by the refinement** (corr-wf14-051): every
member of the twist family (rows `(1 − l) · π(·|f w) + l · π`, constant on positive cells),
under any tie-break, has expected world-indexed payoff at most the refinement's.
Source: [[selection]] R2.4 l. 55 ("the twisted successor is weakly dominated"); [[armstrong]]
I2.2 l. 95 (the twist), I6.2 l. 143; corr-wf14-051
Kind: C
Fidelity: exact (whole family, every tie-break; belief-indexed payoffs excluded)
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W`, `0 ≤ l ≤ 1` -/
theorem twist_choice_le_refineFrame_value (hπ : π ∈ stdSimplex ℝ W) (f : W → S) {l : ℝ}
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {A : Type} [Fintype A] (hA : (univ : Finset A).Nonempty)
    (u : A → W → ℝ) (choose : (W → ℝ) → A) :
    ∑ w, π w * u (choose ((twist π hπ f l hl0 hl1).P w)) w ≤
      ∑ w, π w * univ.sup' hA (fun a => E ((refineFrame π hπ.1 f).P w) (u a)) := by
  apply rowsConstant_choice_le_refineFrame_value hπ.1 f _ hA u choose
  intro v w hvw hv hw
  simp only [twist_P]
  have hpos : 0 < mass π (fibre f w) := mass_fibre_pos_of_pos hπ.1 hw
  rw [condRow_eq_of_mem hpos (mem_fibre.2 hvw)]

end

end Cleanroom.Corrigibility.CorrReflectFrames

import Cleanroom.Corrigibility.CorrLegitGeneral.Defs
import Cleanroom.Lit.LitDdbFacts.Reflection

/-!
# corr-legit-general — T2(a): Reflection conditional on legitimacy is unsatisfiable toward a
possibly-modest legitimate candidate

Abram's first minimal-viability criterion was the equality form, Reflection conditional on `L`
(`P_{t₁}(φ | P_{t₂}(φ) = c, L) = c`). Toward any expert that may be modest at a positive-mass
legitimate world — the programmers always are — it is unsatisfiable: this is DDB §1 l. 80
applied to the restricted deferrer (`not_reflects_of_modestAt`). The local form fails the same
way as soon as the modest candidate's self-cell is a partial answer to `Q` ("the modesty is
visible on `Q`"). The witnesses are fn 66's immodest frame, on which local Reflection still
fails while local Total Trust and local Value hold (`WitnessesFn66.lean`), and the
underconfident-but-informative expert (`WitnessesLeak.lean`).
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames
  Cleanroom.Lit.LitDdbFacts

noncomputable section

set_option linter.unusedSectionVars false

variable {W C : Type} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]

/-- **Reflection conditional on `L` is unsatisfiable toward a modest legitimate candidate**: if
some `w ∈ L` of positive `π`-mass has a modest expert state (`P_w(P = P_w) < 1`), the restricted
deferrer does not reflect the frame. (`0 < mass π L` is implied by `0 < π w`.)
Source: [[legitimacy]] R2.1 l. 56; [[ddb]] I5.2(d) l. 128; [[legitimacy-general-final]]
Statement 1 l. 43 ("satisfiable only if every positive-mass legitimate candidate is immodest")
Kind: C
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w`; `w ∈ L`, `0 < π w`, `F.ModestAt w` -/
theorem legitReflects_unsat {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W} {L : Finset W} {w : W}
    (hw : w ∈ L) (hπw : 0 < π w) (hmod : F.ModestAt w) : ¬ Reflects (restrict π L) F :=
  not_reflects_of_modestAt (restrict_nonneg hπ L) hmod (restrict_pos_of_mem hw hπw)

/-- Contrapositive form: Reflection conditional on `L` forces every positive-mass legitimate
candidate to be immodest.
Source: [[legitimacy-general-final]] Statement 1 l. 43
Kind: L
Fidelity: exact -/
theorem immodest_of_legitReflects {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W} {L : Finset W}
    (h : Reflects (restrict π L) F) {w : W} (hw : w ∈ L) (hπw : 0 < π w) :
    ¬ F.ModestAt w :=
  fun hmod => legitReflects_unsat hπ hw hπw hmod h

/-- **The local equality form fails toward a modest legitimate candidate whose modesty is
visible on `Q`**: if the self-cell `[P = P_w]` of a modest `w ∈ L` with `0 < π w` is a partial
answer to `Q` (`F.cell (F.P w) = answer Q T`), then `LegitReflectsWrt Q π F L` fails — the
clause at `ρ = P_w`, `T` reads `π_L(P = ρ) = π_L(P = ρ) · ρ(P = ρ)`, forcing `ρ(P = ρ) = 1`.
Source: [[legitimacy]] R2.1 l. 56 (local reading); [[Deference Done Better]] fn 62 l. 1231
Kind: C
Fidelity: exact (the visibility hypothesis is what makes the self-cell a partial answer)
Hyps: (a) `∀ w, 0 ≤ π w`; `w ∈ L`, `0 < π w`, `F.ModestAt w`, `F.cell (F.P w) = answer Q T` -/
theorem legitReflectsWrt_unsat_of_visible {Q : W → C} {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w)
    {F : Frame W} {L : Finset W} {w : W} (hw : w ∈ L) (hπw : 0 < π w) (hmod : F.ModestAt w)
    {T : Finset C} (hT : F.cell (F.P w) = answer Q T) : ¬ LegitReflectsWrt Q π F L := by
  intro h
  have hc : F.P w ∈ F.cands (restrict π L) := F.P_mem_cands (restrict_pos_of_mem hw hπw)
  have hcl := h _ hc T
  rw [← hT, inter_self] at hcl
  have hm : 0 < mass (restrict π L) (F.cell (F.P w)) :=
    mass_pos_of_mem (restrict_nonneg hπ L) (F.mem_cell_self w) (restrict_pos_of_mem hw hπw)
  have hx : F.selfMass (F.P w) = 1 := by
    have e : mass (restrict π L) (F.cell (F.P w)) * F.selfMass (F.P w) =
        mass (restrict π L) (F.cell (F.P w)) * 1 := by
      rw [mul_one]; exact hcl.symm
    exact mul_left_cancel₀ hm.ne' e
  unfold Frame.ModestAt at hmod
  linarith

/-- **Visibility up to null worlds** (audit r1 adversarial N10): the same conclusion when the
modest candidate's self-cell agrees with a partial answer `A = answer Q T` only up to null
worlds — `A` covers the cell up to `π_L`-null worlds (`π_L(cell ∩ A) = π_L(cell)`) and lies
inside it up to `P_w`-null worlds (`P_w(A) ≤ P_w(cell)`). The clause at `ρ = P_w`, `T` then
reads `π_L(cell) = π_L(cell) · P_w(A)`, forcing `P_w(A) = 1 ≤ P_w(cell) < 1`. Exact equality
`cell = A` is the special case (`legitReflectsWrt_unsat_of_visible`).
Source: [[legitimacy]] R2.1 l. 56 (local reading); [[Deference Done Better]] fn 62 l. 1231
Kind: C
Fidelity: stronger: visibility up to null worlds in place of exact equality — modestly so: `A`
may differ from the cell only by `π_L`-null worlds inside it and `P_w`-null worlds outside it (a
modest row has `P_w(cellᶜ) > 0`, so `A` absorbs no `P_w`-positive part of the complement; audit
r2 adversarial N7)
Hyps: (a) `∀ w, 0 ≤ π w`; `w ∈ L`, `0 < π w`, `F.ModestAt w`; the two mass conditions -/
theorem legitReflectsWrt_unsat_of_visible_ae {Q : W → C} {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w)
    {F : Frame W} {L : Finset W} {w : W} (hw : w ∈ L) (hπw : 0 < π w) (hmod : F.ModestAt w)
    {T : Finset C}
    (hT₁ : mass (restrict π L) (F.cell (F.P w) ∩ answer Q T) =
      mass (restrict π L) (F.cell (F.P w)))
    (hT₂ : mass (F.P w) (answer Q T) ≤ F.selfMass (F.P w)) : ¬ LegitReflectsWrt Q π F L := by
  intro h
  have hc : F.P w ∈ F.cands (restrict π L) := F.P_mem_cands (restrict_pos_of_mem hw hπw)
  have hcl := h _ hc T
  rw [hT₁] at hcl
  have hm : 0 < mass (restrict π L) (F.cell (F.P w)) :=
    mass_pos_of_mem (restrict_nonneg hπ L) (F.mem_cell_self w) (restrict_pos_of_mem hw hπw)
  have hA : mass (F.P w) (answer Q T) = 1 := by
    have e : mass (restrict π L) (F.cell (F.P w)) * mass (F.P w) (answer Q T) =
        mass (restrict π L) (F.cell (F.P w)) * 1 := by
      rw [mul_one]; exact hcl.symm
    exact mul_left_cancel₀ hm.ne' e
  unfold Frame.ModestAt at hmod
  linarith

/-- Local Reflection conditional on `L` with respect to the finest question is the global form.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem legitReflectsWrt_id_iff {π : W → ℝ} {F : Frame W} {L : Finset W} :
    LegitReflectsWrt (id : W → W) π F L ↔ Reflects (restrict π L) F := by
  unfold LegitReflectsWrt ReflectsWrt Reflects
  constructor
  · intro h ρ hρ w
    have := h ρ hρ {w}
    have ha : answer (id : W → W) {w} = {w} := by ext v; simp [answer]
    rw [ha] at this
    rw [mass_singleton] at this
    -- π_L(cell ∩ {w}) = π_L w · 𝟙_cell w
    have e : mass (restrict π L) (F.cell ρ ∩ {w}) = restrict π L w * ind (F.cell ρ) w := by
      unfold mass ind
      by_cases hw : w ∈ F.cell ρ
      · rw [inter_eq_right.2 (singleton_subset_iff.2 hw), sum_singleton, if_pos hw, mul_one]
      · rw [if_neg hw, mul_zero]
        apply sum_eq_zero
        intro v hv
        exfalso
        rw [mem_inter, mem_singleton] at hv
        exact hw (hv.2 ▸ hv.1)
    rw [e] at this
    exact this
  · intro h ρ hρ T
    -- partial answers are unions of singletons: sum the pointwise identity over `answer Q T`
    have e1 : mass (restrict π L) (F.cell ρ ∩ answer (id : W → W) T) =
        ∑ w ∈ answer (id : W → W) T, restrict π L w * ind (F.cell ρ) w := by
      unfold mass
      rw [inter_comm, ← sum_filter_add_sum_filter_not (answer (id : W → W) T) (· ∈ F.cell ρ)]
      rw [filter_mem_eq_inter]
      have h0 : ∑ w ∈ (answer (id : W → W) T).filter (fun w => w ∉ F.cell ρ),
          restrict π L w * ind (F.cell ρ) w = 0 := by
        apply sum_eq_zero
        intro w hw
        rw [mem_filter] at hw
        simp [ind, hw.2]
      rw [h0, add_zero]
      apply sum_congr rfl
      intro w hw
      rw [mem_inter] at hw
      simp [ind, hw.2]
    rw [e1]
    simp_rw [h ρ hρ]
    rw [← mul_sum]
    rfl

end

end Cleanroom.Corrigibility.CorrLegitGeneral

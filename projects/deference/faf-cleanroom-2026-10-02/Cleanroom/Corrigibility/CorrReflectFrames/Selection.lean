import Cleanroom.Corrigibility.CorrReflectFrames.Collapse

/-!
# corr-reflect-frames — T9(a): refinements are reflective; the selection theorem

Bayesian refinements `refineFrame π f` are reflective and immodest; a selection `s` among
refinements `f k` that **retains its grounds** (`RetainsGrounds f s`: `{s = k}` is
`f k`-measurable) is *itself* the refinement along `w ↦ (s w, f (s w) w)`, hence reflective
(value and function form), estimate-matching and totally trusted. R1.1's common-`G` hypothesis
implies retention (`retainsGrounds_of_refines`), so R1.1 is a corollary; the per-`k` form is the
common generalization that also covers adapted stopping (`Stopping.lean`), which R1.1's
hypothesis does not (findings).

Null-fibre convention: `condRow` is `δ_w` on a `π`-null fibre; candidates never sit on null
fibres (`mass_fibre_pos_of_pos`), so no headline touches the convention.
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W] {S T K : Type} [DecidableEq S] [DecidableEq T]
  {π : W → ℝ}

/-! ## Fibres and conditional rows -/

/-- Fibres are determined by the value of the partition map.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fibre_eq_of_eq {f : W → S} {v w : W} (h : f v = f w) : fibre f v = fibre f w := by
  ext u; simp [mem_fibre, h]

/-- The conditional row at `w` depends only on the fibre through `w`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condRow_congr_fibre {f : W → S} {g : W → T} {w : W} (h : fibre f w = fibre g w) :
    condRow π f w = condRow π g w := by
  unfold condRow; rw [h]

/-- A world of positive probability has a positive-mass fibre.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_fibre_pos_of_pos (hπ : ∀ w, 0 ≤ π w) {f : W → S} {w : W} (hw : 0 < π w) :
    0 < mass π (fibre f w) :=
  mass_pos_of_mem hπ (mem_fibre_self f w) hw

/-- The conditional row on a positive fibre, pointwise.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condRow_apply_of_pos {f : W → S} {w : W} (h : 0 < mass π (fibre f w)) (v : W) :
    condRow π f w v = ind (fibre f w) v * π v / mass π (fibre f w) := by
  rw [condRow_of_pos h]

/-- On a positive fibre the conditional row is constant along the fibre.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condRow_eq_of_mem {f : W → S} {w : W} (h : 0 < mass π (fibre f w)) {v : W}
    (hv : v ∈ fibre f w) : condRow π f v = condRow π f w := by
  have hfib : fibre f v = fibre f w := fibre_eq_of_eq (mem_fibre.1 hv)
  have hv' : 0 < mass π (fibre f v) := by rw [hfib]; exact h
  rw [condRow_of_pos hv', condRow_of_pos h, hfib]

/-- The row of a refinement frame.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem refineFrame_P (hπ : ∀ w, 0 ≤ π w) (f : W → S) (w : W) :
    (refineFrame π hπ f).P w = condRow π f w := rfl

/-- On a positive fibre, the cell of the conditional row is the fibre: a row on another fibre
(or a `δ` on a null one) vanishes at a positive point of this fibre where this row is positive.
Source: none: infrastructure (the "cells of the selected estimator partition `Ω`" step of R1.1)
Kind: L
Fidelity: n/a -/
theorem cell_condRow (hπ : ∀ w, 0 ≤ π w) {f : W → S} {w : W} (h : 0 < mass π (fibre f w)) :
    (refineFrame π hπ f).cell (condRow π f w) = fibre f w := by
  ext v
  rw [Frame.mem_cell, refineFrame_P]
  constructor
  · intro hv
    by_contra hnot
    obtain ⟨u, hu, hupos⟩ := (mass_pos_iff hπ).1 h
    have h1 : condRow π f w u = π u / mass π (fibre f w) := by
      rw [condRow_apply_of_pos h]; simp [ind, hu]
    have h2 : condRow π f v u = 0 := by
      by_cases hv' : 0 < mass π (fibre f v)
      · rw [condRow_apply_of_pos hv']
        have : u ∉ fibre f v := by
          rw [mem_fibre] at hu hnot ⊢
          intro e; exact hnot (e.symm.trans hu)
        simp [ind, this]
      · rw [condRow_of_not_pos hv']
        have : u ≠ v := by
          intro e; rw [e] at hu; exact hnot hu
        simp [this]
    rw [hv, h1] at h2
    have : 0 < π u / mass π (fibre f w) := div_pos hupos h
    linarith
  · intro hv; exact condRow_eq_of_mem h hv

/-! ## Refinements are reflective and immodest -/

/-- **Bayesian refinements are reflective**: for a candidate `ρ = π(· | f = f w₀)` the cell is the
fibre and `π w · 𝟙_fibre w = π(fibre) · ρ w` is the definition of the conditional row.
Source: [[armstrong]] Theorem A numerical T1 (Bayesian refinement: GR holds), [[selection]]
R1.1 ("itself a Bayesian refinement … satisfies general reflection")
Kind: P
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem refineFrame_reflects (hπ : ∀ w, 0 ≤ π w) (f : W → S) :
    Reflects π (refineFrame π hπ f) := by
  intro ρ hρ w
  obtain ⟨w₀, hw₀, rfl⟩ := Frame.mem_cands.1 hρ
  have hfib : 0 < mass π (fibre f w₀) := mass_fibre_pos_of_pos hπ hw₀
  rw [refineFrame_P, cell_condRow hπ hfib, condRow_apply_of_pos hfib]
  have hne := hfib.ne'
  field_simp
  try ring

/-- **Bayesian refinements are immodest** (every row, including the `δ_w` rows on null fibres):
a conditional row lives on its fibre, which is its cell.
Source: [[armstrong]] Theorem A numerical T1 (introspection holds for refinements);
mandate T9(a) `refineFrame_immodest`
Kind: P
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem refineFrame_immodest (hπ : ∀ w, 0 ≤ π w) (f : W → S) :
    (refineFrame π hπ f).Immodest := by
  intro w
  unfold Frame.selfMass
  by_cases h : 0 < mass π (fibre f w)
  · rw [refineFrame_P, cell_condRow hπ h]
    unfold mass
    have hrow : ∀ v ∈ fibre f w, condRow π f w v = π v * (mass π (fibre f w))⁻¹ := by
      intro v hv
      rw [condRow_apply_of_pos h]
      simp [ind, hv, div_eq_mul_inv]
    rw [sum_congr rfl hrow, ← sum_mul]
    exact mul_inv_cancel₀ h.ne'
  · apply le_antisymm (mass_le_one ((refineFrame π hπ f).P_mem w) _)
    calc (1 : ℝ) = (refineFrame π hπ f).P w w := by
          rw [refineFrame_P, condRow_of_not_pos h]; simp
      _ ≤ mass ((refineFrame π hπ f).P w) ((refineFrame π hπ f).cell ((refineFrame π hπ f).P w)) :=
          single_le_sum (fun v _ => (refineFrame π hπ f).P_nonneg w v)
            ((refineFrame π hπ f).mem_cell_self w)

/-- Refinements are introspective at candidates.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem refineFrame_candsIntrospective (hπ : ∀ w, 0 ≤ π w) (f : W → S) :
    CandsIntrospective π (refineFrame π hπ f) :=
  candsIntrospective_of_immodest (refineFrame_immodest hπ f) π

/-- Refinements are estimate-matching (Armstrong's SU for Bayesian refinements).
Source: [[armstrong]] Theorem A numerical T1
Kind: C
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem refineFrame_estimateMatching (hπ : ∀ w, 0 ≤ π w) (f : W → S) :
    EstimateMatching π (refineFrame π hπ f) :=
  estimateMatching_of_varReflects (varReflects_of_reflects hπ (refineFrame_reflects hπ f))

/-- Refinements are totally trusted.
Source: [[armstrong]] I6.2 (refinements are valued: Good), via T1
Kind: C
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem refineFrame_totalTrust (hπ : ∀ w, 0 ≤ π w) (f : W → S) :
    TotalTrust π (refineFrame π hπ f) :=
  totalTrust_of_varReflects hπ (varReflects_of_reflects hπ (refineFrame_reflects hπ f))

/-- Refinements satisfy value-form reflection.
Source: [[selection]] R1.1 ("in both value and function form")
Kind: C
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w` only -/
theorem refineFrame_valueReflects (hπ : ∀ w, 0 ≤ π w) (f : W → S) :
    ValueReflects π (refineFrame π hπ f) :=
  valueReflects_of_varReflects (varReflects_of_reflects hπ (refineFrame_reflects hπ f))

/-! ## The selection theorem -/

/-- Under retention of grounds, the fibre of the selected partition `w ↦ (s w, f (s w) w)`
through `w` is the fibre of the selected candidate's partition through `w`.
Source: [[selection]] R1.1 (the cells `{ℱ_k-cell of ω : s(ω) = k}` partition `Ω`)
Kind: L
Fidelity: n/a -/
theorem fibre_select_eq [DecidableEq K] {f : K → W → S} {s : W → K} (hret : RetainsGrounds f s)
    (w : W) : fibre (fun v => (s v, f (s v) v)) w = fibre (f (s w)) w := by
  ext v
  simp only [mem_fibre, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩; rw [h1] at h2; exact h2
  · intro h
    have h1 : s v = s w := hret (s w) w v rfl h.symm
    exact ⟨h1, by rw [h1]; exact h⟩

/-- **The selection theorem, per-`k` retention form.** A selection among Bayesian refinements
that retains its grounds is the Bayesian refinement along `w ↦ (s w, f (s w) w)`, as frames.
Source: [[selection]] R1.1 (strengthened form), [[armstrong]] A1 (proof: `{s = k}` is
`ℱ_k`-measurable), [[radical]] Sel.4
Kind: P
Scope: on positive fibres the frame equality is nearly *equivalent* to retention (a conditional
row determines its fibre), so the headline that carries R1.1's claim without being equivalent
to its hypothesis is `selectFrame_reflects` (audit r1, adversarial 6)
Fidelity: variant: per-`k` retention in place of R1.1's common coarser partition `G`
(`retainsGrounds_of_refines` recovers R1.1); frames compared as functions, null-fibre rows
included
Hyps: (a) `∀ w, 0 ≤ π w`; retention is the content hypothesis (without it the claim is false:
`Witnesses`, the forgetting rule) -/
theorem selectFrame_eq_refineFrame [DecidableEq K] (hπ : ∀ w, 0 ≤ π w) {f : K → W → S}
    {s : W → K} (hret : RetainsGrounds f s) :
    selectFrame π hπ f s = refineFrame π hπ (fun v => (s v, f (s v) v)) := by
  apply frame_ext
  intro w
  show condRow π (f (s w)) w = condRow π (fun v => (s v, f (s v) v)) w
  exact (condRow_congr_fibre (fibre_select_eq hret w)).symm

/-- **Selection preserves Reflection** (function form) under retention of grounds.
Source: [[selection]] R1.1; [[radical]] Sel.4 ("preserves it for an agent whose successor
conditions on the fact and grounds of its own selection")
Kind: C
Fidelity: exact (per-`k` retention)
Hyps: (a) `∀ w, 0 ≤ π w`; retention -/
theorem selectFrame_reflects [DecidableEq K] (hπ : ∀ w, 0 ≤ π w) {f : K → W → S} {s : W → K}
    (hret : RetainsGrounds f s) : Reflects π (selectFrame π hπ f s) := by
  rw [selectFrame_eq_refineFrame hπ hret]; exact refineFrame_reflects hπ _

/-- **Selection preserves value-form reflection** under retention of grounds.
Source: [[selection]] R1.1, R2.1 (`P(φ | P_{t₂}(φ) = c, {s = k}) = c`)
Kind: C
Fidelity: exact (per-`k` retention)
Hyps: (a) `∀ w, 0 ≤ π w`; retention -/
theorem selectFrame_valueReflects [DecidableEq K] (hπ : ∀ w, 0 ≤ π w) {f : K → W → S}
    {s : W → K} (hret : RetainsGrounds f s) : ValueReflects π (selectFrame π hπ f s) := by
  rw [selectFrame_eq_refineFrame hπ hret]; exact refineFrame_valueReflects hπ _

/-- **Selection preserves sequential unbiasedness** (estimate matching) under retention of
grounds — Armstrong's A1.
Source: [[armstrong]] A1 l. 262; [[selection]] R1.1
Kind: C
Fidelity: exact (per-`k` retention)
Hyps: (a) `∀ w, 0 ≤ π w`; retention -/
theorem selectFrame_estimateMatching [DecidableEq K] (hπ : ∀ w, 0 ≤ π w) {f : K → W → S}
    {s : W → K} (hret : RetainsGrounds f s) : EstimateMatching π (selectFrame π hπ f s) := by
  rw [selectFrame_eq_refineFrame hπ hret]; exact refineFrame_estimateMatching hπ _

/-- **Selection preserves Total Trust** under retention of grounds.
Source: [[selection]] R1.1; [[radical]] Sel.4
Kind: C
Fidelity: exact (per-`k` retention)
Hyps: (a) `∀ w, 0 ≤ π w`; retention -/
theorem selectFrame_totalTrust [DecidableEq K] (hπ : ∀ w, 0 ≤ π w) {f : K → W → S}
    {s : W → K} (hret : RetainsGrounds f s) : TotalTrust π (selectFrame π hπ f s) := by
  rw [selectFrame_eq_refineFrame hπ hret]; exact refineFrame_totalTrust hπ _

/-- **Selection preserves Value** under retention of grounds.
Source: [[selection]] R1.1 with DDB Theorem 2.2
Kind: C
Fidelity: exact (per-`k` retention)
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W`; retention -/
theorem selectFrame_value [DecidableEq K] (hπ : π ∈ stdSimplex ℝ W) {f : K → W → S}
    {s : W → K} (hret : RetainsGrounds f s) : Value π (selectFrame π hπ.1 f s) :=
  (value_iff_totalTrust hπ _).2 (selectFrame_totalTrust hπ.1 hret)

/-- **R1.1's hypothesis implies retention**: if a partition `G` is coarser than every candidate
partition `f k` and the rule `s` is `G`-measurable, then `{s = k}` is `f k`-measurable for
every `k`. So R1.1 is a corollary of the per-`k` theorem — and the per-`k` form is strictly more
general (adapted stopping has no common coarser `G`; findings, R1.3).
Source: [[selection]] R1.1 (hypothesis), R1.3 (the optional-stopping remark); [[armstrong]] A1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem retainsGrounds_of_refines {G : W → T} {f : K → W → S} {s : W → K}
    (hG : ∀ k, Blackwell.Refines (f k) G) (hs : Blackwell.Refines G s) : RetainsGrounds f s := by
  intro k w w' hw hf
  obtain ⟨h, hh⟩ := hs
  obtain ⟨hk, hhk⟩ := hG k
  have hGw : G w' = G w := by rw [hhk]; simp [Function.comp, hf]
  have : s w' = s w := by rw [hh]; simp [Function.comp, hGw]
  rw [this, hw]

end

end Cleanroom.Corrigibility.CorrReflectFrames

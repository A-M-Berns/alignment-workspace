import Cleanroom.Lit.LitDdbAccuracyMm.Basic

/-!
# Lemma 7.7: gsp + value-directed ⟹ monotone strictly proper (Target 4)

DDB's proof (due to Campbell-Moore) realised on worlds: for `e := E_ρ(X) ≤ s < t ≤ max X`, the
distribution `ρ⋆` moves all `ρ`-mass of `{X ≤ s}` onto one world `w_n` with `t ≤ X w_n`; the
segment from `ρ` to `ρ⋆` stays in DDB's order-cone `Q` and, by linearity, some point `ρ_λ` on it
has `E_{ρ_λ}(X) = s` exactly (`λ := (s − e)/(E_{ρ⋆}(X) − e)`; no IVT). Gsp at `ρ_λ` with the
estimate `t ≠ s` gives `E_{ρ_λ}(I_X(t) − I_X(s)) > 0`, and the sign pattern of
value-directedness gives `E_ρ(I_X(t) − I_X(s)) ≥ E_{ρ_λ}(…)`. Two traps of the printed proof are
avoided: the last sentence claims a *strict* `E_π(D) > E_ρ(D)`, false when `ρ = π` (the case
`s = e`, handled separately by gsp at `ρ` itself); and it writes `t < v_n` where the statement
allows `t = v_n` — the statement is what is proved.
-/

namespace Cleanroom.Lit.LitDdbAccuracyMm

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- DDB's `ρ⋆`, realised on worlds: zero on `{X ≤ s}`, `ρ` elsewhere, with the removed mass
`ρ(X ≤ s)` added at the world `wn`.
Source: [[Deference Done Better]] App. B Lemma 7.7 proof l. 664 (`ρ⋆` on the value set)
Kind: D
Fidelity: variant: `ρ⋆` is defined on worlds, not on the values of `X` (it induces DDB's) -/
def shiftUp (ρ X : W → ℝ) (s : ℝ) (wn : W) : W → ℝ :=
  fun w => (if X w ≤ s then 0 else ρ w) +
    (if w = wn then mass ρ (univ.filter (fun v => X v ≤ s)) else 0)

/-- `ρ⋆` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem shiftUp_mem_stdSimplex {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) (X : W → ℝ) (s : ℝ)
    (wn : W) : shiftUp ρ X s wn ∈ stdSimplex ℝ W := by
  have hM : 0 ≤ mass ρ (univ.filter (fun v => X v ≤ s)) := mass_nonneg hρ.1 _
  refine ⟨fun w => ?_, ?_⟩
  · unfold shiftUp
    apply add_nonneg
    · split_ifs
      · exact le_rfl
      · exact hρ.1 w
    · split_ifs
      · exact hM
      · exact le_rfl
  · unfold shiftUp
    rw [sum_add_distrib, sum_ite_eq' univ wn, if_pos (mem_univ _), sum_ite, sum_const_zero,
      zero_add, mass, add_comm, sum_filter_add_sum_filter_not, hρ.2]

/-- `s ≤ E_{ρ⋆}(X)` when `s ≤ X wn`: every world carrying `ρ⋆`-mass has `X ≥ s`.
Source: [[Deference Done Better]] App. B l. 666 ("`s < E_{ρ⋆}(X)`")
Kind: L
Fidelity: n/a -/
theorem le_E_shiftUp {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) (X : W → ℝ) {s : ℝ} {wn : W}
    (hwn : s ≤ X wn) : s ≤ E (shiftUp ρ X s wn) X := by
  have hmem := shiftUp_mem_stdSimplex hρ X s wn
  have h1 : ∀ w, shiftUp ρ X s wn w * s ≤ shiftUp ρ X s wn w * X w := by
    intro w
    by_cases hx : s ≤ X w
    · exact mul_le_mul_of_nonneg_left hx (hmem.1 w)
    · have hw : w ≠ wn := by
        rintro rfl; exact hx hwn
      have : shiftUp ρ X s wn w = 0 := by
        simp [shiftUp, hw, not_le.1 hx |>.le]
      rw [this]; simp
  have h2 : ∑ w, shiftUp ρ X s wn w * s ≤ ∑ w, shiftUp ρ X s wn w * X w :=
    sum_le_sum fun w _ => h1 w
  rw [← sum_mul, hmem.2, one_mul] at h2
  exact h2

/-! ## Value-directedness on the value range is a consequence of gsp (audit r1 repair) -/

/-- The two-point distribution `(1 − p)·δ_{w₀} + p·δ_w`.
Source: none: infrastructure (the mixtures of `IsGspOn.lt_of_lt_of_le`)
Kind: D
Fidelity: n/a -/
def twoPt (w₀ w : W) (p : ℝ) : W → ℝ :=
  fun v => (if v = w₀ then 1 - p else 0) + (if v = w then p else 0)

/-- `twoPt w₀ w p` is a distribution for `p ∈ [0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem twoPt_mem_stdSimplex (w₀ w : W) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    twoPt w₀ w p ∈ stdSimplex ℝ W := by
  refine ⟨fun v => ?_, ?_⟩
  · simp only [twoPt]
    apply add_nonneg <;> split_ifs <;> linarith
  · simp only [twoPt, sum_add_distrib, sum_ite_eq', mem_univ, if_true]
    ring

/-- `E_{twoPt}(X) = (1 − p) X w₀ + p X w`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_twoPt (w₀ w : W) (p : ℝ) (X : W → ℝ) :
    E (twoPt w₀ w p) X = (1 - p) * X w₀ + p * X w := by
  simp only [E, twoPt, add_mul, sum_add_distrib, ite_mul, zero_mul, sum_ite_eq', mem_univ,
    if_true]

/-- `E_{twoPt}(I_X(s)) = (1 − p) I s (X w₀) + p I s (X w)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem expInacc_twoPt (w₀ w : W) (p : ℝ) (X : W → ℝ) (I : Rule) (s : ℝ) :
    expInacc (twoPt w₀ w p) X I s = (1 - p) * I s (X w₀) + p * I s (X w) := by
  simp only [expInacc, twoPt, add_mul, sum_add_distrib, ite_mul, zero_mul, sum_ite_eq', mem_univ,
    if_true]

/-- **Clause 1 of value-directedness on the range, from gsp on the range.** For
`X w₀ ≤ e₁ < e₂ ≤ X w`, the two-point mixtures `ρ_p = (1 − p) δ_{w₀} + p δ_w` with means `e₁`
and `e₂` give two gsp instances — at `ρ_{e₂}` against the estimate `e₁`, at `ρ_{e₁}` against
`e₂` — whose combination `(1 − p₁)·[gsp at ρ_{e₂}] − (1 − p₂)·[gsp at ρ_{e₁}]` is
`(p₂ − p₁)·(I e₂ (X w) − I e₁ (X w)) < 0`.
Source: [[Deference Done Better]] App. B l. 650 (Campbell-Moore 2020, "every gsp
estimate-inaccuracy measure is value-directed"), proved here on the value range; audit r1
(fidelity) B1
Kind: P
Fidelity: exact on the value range
Hyps: (a) none beyond `IsGspOn` -/
theorem IsGspOn.lt_of_lt_of_le {X : W → ℝ} {I : Rule} (hg : IsGspOn X I) {w w₀ : W}
    {e₁ e₂ : ℝ} (hw₀ : X w₀ ≤ e₁) (h12 : e₁ < e₂) (h2 : e₂ ≤ X w) :
    I e₂ (X w) < I e₁ (X w) := by
  have hden : 0 < X w - X w₀ := by linarith
  have hne : X w - X w₀ ≠ 0 := hden.ne'
  set p₁ := (e₁ - X w₀) / (X w - X w₀) with hp₁
  set p₂ := (e₂ - X w₀) / (X w - X w₀) with hp₂
  have hp₁0 : 0 ≤ p₁ := div_nonneg (by linarith) hden.le
  have hp₂1 : p₂ ≤ 1 := by rw [hp₂, div_le_one hden]; linarith
  have hp₁₂ : p₁ < p₂ := by
    rw [hp₁, hp₂, ← sub_pos, div_sub_div_same]
    exact div_pos (by linarith) hden
  have hp₁1 : p₁ ≤ 1 := by linarith
  have hp₂0 : 0 ≤ p₂ := by linarith
  have hE₁ : E (twoPt w₀ w p₁) X = e₁ := by
    rw [E_twoPt, hp₁]; field_simp; ring
  have hE₂ : E (twoPt w₀ w p₂) X = e₂ := by
    rw [E_twoPt, hp₂]; field_simp; ring
  -- gsp at the mean-`e₂` mixture against the estimate `e₁`
  have g₂ := hg _ (twoPt_mem_stdSimplex w₀ w hp₂0 hp₂1) e₁ ⟨w₀, hw₀⟩ ⟨w, by linarith⟩
    (by rw [hE₂]; exact h12.ne)
  rw [hE₂, expInacc_twoPt, expInacc_twoPt] at g₂
  -- gsp at the mean-`e₁` mixture against the estimate `e₂`
  have g₁ := hg _ (twoPt_mem_stdSimplex w₀ w hp₁0 hp₁1) e₂ ⟨w₀, by linarith⟩ ⟨w, h2⟩
    (by rw [hE₁]; exact h12.ne')
  rw [hE₁, expInacc_twoPt, expInacc_twoPt] at g₁
  by_contra hB
  rw [not_lt] at hB
  have c₂ : (1 - p₁) * ((1 - p₂) * I e₂ (X w₀) + p₂ * I e₂ (X w) -
      ((1 - p₂) * I e₁ (X w₀) + p₂ * I e₁ (X w))) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) (by linarith)
  have c₁ : 0 ≤ (1 - p₂) * ((1 - p₁) * I e₂ (X w₀) + p₁ * I e₂ (X w) -
      ((1 - p₁) * I e₁ (X w₀) + p₁ * I e₁ (X w))) :=
    mul_nonneg (by linarith) (by linarith)
  have hkey : (1 - p₁) * ((1 - p₂) * I e₂ (X w₀) + p₂ * I e₂ (X w) -
      ((1 - p₂) * I e₁ (X w₀) + p₂ * I e₁ (X w))) -
      (1 - p₂) * ((1 - p₁) * I e₂ (X w₀) + p₁ * I e₂ (X w) -
      ((1 - p₁) * I e₁ (X w₀) + p₁ * I e₁ (X w))) =
      (p₂ - p₁) * (I e₂ (X w) - I e₁ (X w)) := by ring
  have hnn : 0 ≤ (p₂ - p₁) * (I e₂ (X w) - I e₁ (X w)) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

/-- **Every gsp rule is value-directed on the value range** — Campbell-Moore 2020 as cited at
DDB l. 650, proved here from `IsGspOn` alone (off the range the implication is false: audit r1
probes). Clause 2 is clause 1 for `(−X, I.neg)`.
Source: [[Deference Done Better]] App. B l. 650; Theorem 7.9 l. 766 (the domain); audit r1 B1
Kind: P
Fidelity: exact on the value range
Hyps: (a) none beyond `IsGspOn` -/
theorem IsGspOn.valueDirectedOn {X : W → ℝ} {I : Rule} (hg : IsGspOn X I) :
    ValueDirectedOn X I := by
  intro w e₁ e₂
  constructor
  · rintro ⟨w₀, hw₀⟩ h12 h2
    exact hg.lt_of_lt_of_le hw₀ h12 h2
  · rintro ⟨w₀, hw₀⟩ h2 h21
    have h := hg.neg.lt_of_lt_of_le (w := w) (w₀ := w₀) (e₁ := -e₁) (e₂ := -e₂)
      (by simp only [Pi.neg_apply]; linarith) (by linarith)
      (by simp only [Pi.neg_apply]; linarith)
    simpa [Rule.neg] using h

/-- Gsp (all real estimates) gives value-directedness on the value range.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsGsp.valueDirectedOn {X : W → ℝ} {I : Rule} (hg : IsGsp X I) : ValueDirectedOn X I :=
  hg.isGspOn.valueDirectedOn

/-! ## Lemma 7.7 -/

/-- **Lemma 7.7, upper clause.** For `I` gsp on the range and value-directed on the range
(the latter is derivable, `IsGspOn.valueDirectedOn`; kept as a hypothesis here so the argument is
DDB's), and any distribution `ρ` with `E_ρ(X) ≤ s < t ≤ max X`: `E_ρ(I_X(s)) < E_ρ(I_X(t))`.
Value-directedness is used at two estimates only, both in the range: `(s, t)` at a world with
`X w ≤ s` (clause 2, `t ≤ max X`) and at the receiving world `X wn ≥ t` (clause 1, `min X ≤ s`).
Source: [[Deference Done Better]] App. B Lemma 7.7 l. 658
Kind: P
Fidelity: exact (statement's `t ≤ v_n`, not the proof's `t < v_n`)
Hyps: (a) none beyond the class -/
theorem expInacc_lt_of_le_lt {X : W → ℝ} {I : Rule} (hg : IsGspOn X I)
    (hv : ValueDirectedOn X I) {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) {s t : ℝ} (hst : s < t)
    (hes : E ρ X ≤ s) (hrange : ∃ w, t ≤ X w) : expInacc ρ X I s < expInacc ρ X I t := by
  obtain ⟨wn, hwn⟩ := hrange
  have hlo : ∃ w, X w ≤ t := by
    obtain ⟨w, hw⟩ := exists_le_E hρ X
    exact ⟨w, by linarith⟩
  have hhi : ∃ w, t ≤ X w := ⟨wn, hwn⟩
  rcases hes.lt_or_eq with hlt | heq
  · -- the case `e < s`: move along the segment from `ρ` to `ρ⋆`
    have hlos : ∃ w, X w ≤ s := by
      obtain ⟨w, hw⟩ := exists_le_E hρ X
      exact ⟨w, by linarith⟩
    set e := E ρ X with he
    set ρs := shiftUp ρ X s wn with hρs
    have hρs_mem := shiftUp_mem_stdSimplex hρ X s wn
    have hEs : s ≤ E ρs X := le_E_shiftUp hρ X (by linarith)
    have hden : 0 < E ρs X - e := by linarith
    set lam := (s - e) / (E ρs X - e) with hlam
    have hlam0 : 0 ≤ lam := div_nonneg (by linarith) hden.le
    have hlam1 : lam ≤ 1 := by rw [hlam, div_le_one hden]; linarith
    set ρl : W → ℝ := (1 - lam) • ρ + lam • ρs with hρl
    have hρl_mem : ρl ∈ stdSimplex ℝ W :=
      (convex_stdSimplex ℝ W) hρ hρs_mem (by linarith) hlam0 (by ring)
    have hEl : E ρl X = s := by
      rw [hρl, E_add_left, E_smul_left, E_smul_left, hlam]
      field_simp
      ring
    have hgsp := hg ρl hρl_mem t hlo hhi (by rw [hEl]; exact hst.ne')
    rw [hEl] at hgsp
    have key : expInacc ρl X I t - expInacc ρl X I s ≤
        expInacc ρ X I t - expInacc ρ X I s := by
      simp only [expInacc, ← sum_sub_distrib, ← mul_sub]
      apply sum_le_sum
      intro w _
      have hρlw : ρl w = (1 - lam) * ρ w + lam * ρs w := by
        simp [hρl]
      by_cases hxs : X w ≤ s
      · -- `X w ≤ s`: `ρ⋆ w = 0`, and `I s (X w) < I t (X w)`
        have hw : w ≠ wn := by rintro rfl; linarith
        have hρsw : ρs w = 0 := by simp [hρs, shiftUp, hxs, hw]
        have hD : 0 < I t (X w) - I s (X w) := by
          have := (hv w t s).2 hhi hxs hst
          linarith
        rw [hρlw, hρsw]
        apply mul_le_mul_of_nonneg_right _ hD.le
        nlinarith [hρ.1 w]
      · by_cases hw : w = wn
        · -- the receiving world: `ρ⋆ wn = ρ wn + M ≥ ρ wn`, and `I t (X wn) < I s (X wn)`
          subst hw
          have hM : 0 ≤ mass ρ (univ.filter (fun v => X v ≤ s)) := mass_nonneg hρ.1 _
          have hρsw : ρs w = ρ w + mass ρ (univ.filter (fun v => X v ≤ s)) := by
            simp [hρs, shiftUp, hxs]
          have hD : I t (X w) - I s (X w) ≤ 0 := by
            have := (hv w s t).1 hlos hst hwn
            linarith
          rw [hρlw, hρsw]
          apply mul_le_mul_of_nonpos_right _ hD
          nlinarith
        · -- untouched worlds
          have hρsw : ρs w = ρ w := by simp [hρs, shiftUp, hxs, hw]
          rw [hρlw, hρsw]
          apply le_of_eq
          ring
    linarith
  · -- the case `e = s`: gsp at `ρ` itself with the estimate `t ≠ e`
    have := hg ρ hρ t hlo hhi (by rw [heq]; exact hst.ne')
    rw [heq] at this
    exact this

/-- **Lemma 7.7.** Every rule gsp on the value range is monotone strictly proper. DDB's
statement ("Let `I_X` be a gsp … monotone strictly proper") takes value-directedness from
Campbell-Moore 2020; here it is `IsGspOn.valueDirectedOn`, so the only hypothesis is gsp on the
range. The lower clause is the upper clause for `(−X, I.neg)`.
Source: [[Deference Done Better]] App. B Lemma 7.7 l. 658; items 076, 2-013
Kind: P
Fidelity: stronger: gsp on the value range only (DDB: gsp, with value-directedness by citation)
Hyps: (a) none -/
theorem monotoneStrictlyProper_of_isGspOn {X : W → ℝ} {I : Rule} (hg : IsGspOn X I) :
    MonotoneStrictlyProper X I := by
  intro ρ hρ s t hst
  constructor
  · intro hes hr
    exact expInacc_lt_of_le_lt hg hg.valueDirectedOn hρ hst hes hr
  · intro hte ⟨w, hw⟩
    have h := expInacc_lt_of_le_lt hg.neg hg.neg.valueDirectedOn hρ (s := -t) (t := -s)
      (by linarith) (by rw [E_neg_right]; linarith) ⟨w, by simp only [Pi.neg_apply]; linarith⟩
    rw [expInacc_neg, expInacc_neg, neg_neg, neg_neg] at h
    exact h

/-- **Lemma 7.7 for gsp rules** (fn 47's class, all real estimates).
Source: [[Deference Done Better]] App. B Lemma 7.7 l. 658
Kind: P
Fidelity: exact (DDB's class; value-directedness derived, not cited)
Hyps: (a) none -/
theorem monotoneStrictlyProper_of_isGsp {X : W → ℝ} {I : Rule} (hg : IsGsp X I) :
    MonotoneStrictlyProper X I :=
  monotoneStrictlyProper_of_isGspOn hg.isGspOn

end

end Cleanroom.Lit.LitDdbAccuracyMm

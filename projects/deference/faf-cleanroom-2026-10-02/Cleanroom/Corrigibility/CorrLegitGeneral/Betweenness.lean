import Cleanroom.Corrigibility.CorrLegitGeneral.TwoCell
import Cleanroom.Lit.LitDdbFacts.Examples

/-!
# corr-legit-general — T4(c): affine betweenness on the P2 frame is the settled two-cell case

approval-final P2′ (l. 93) proves local Value on its P2 example from "betweenness"
`p̂₂ ≤ p_{H₂} ≤ p_P ≤ p_{H₁} ≤ p̂₁` by an envelope argument and leaves open whether betweenness is
also necessary (O1 l. 197: "the failure boundary (overseer credence outside `[p_P, p̂_s]`)").
Here the example is built as a frame on four worlds `(x, s)` — `0 = (x=1, s=1)`, `1 = (x=0, s=1)`,
`2 = (x=1, s=2)`, `3 = (x=0, s=2)` — with the overseer's row at a signal-`s` world the credence
`p_{H_s}` in `x = 1` spread over that signal's two worlds, and the deferrer the joint law
`π(s = 1) = σ`, `π(x = 1 | s) = p̂_s`. The `x`-question `{x = 1} = {0, 2}` is two-cell, so T4(b)
applies: local Total Trust is the pair of Simple-Trust cuts, and because the two rows are
determined by their `P(x = 1)` the two-cell Value theorem applies too. For two signals with
`p_{H₂} < p_{H₁}` the four cuts at the attained thresholds are exactly the four betweenness
inequalities — **betweenness is necessary and sufficient**, for local Total Trust and for local
Value alike (`p2_totalTrustWrt_iff`, `p2_valuesWrt_iff`), on the whole parametric family off its
diagonal. The standing `p_{H₂} < p_{H₁}` is load-bearing: on the diagonal `h₁ = h₂ = p_P` local
Total Trust holds while local Value fails by the tie mechanism of `tie4`
(`BetweennessDiagonal.lean`, `p2_diagonal_breaks`; audit r2 adversarial N2). The source's
numbers (`p2_instance`) and its "overconfident overseer" failure (`p2_overconfident`) are
instances. This answers P2′/O1's necessity question for two signals and shows corr-wf14-2-047
is an instance of the two-cell case rather than progress on fn 65 (findings F4, Known issues 3).
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Lit.LitDdbAccuracyMm
  Cleanroom.Lit.LitDdbFacts.Examples

noncomputable section

set_option linter.unusedSectionVars false

/-! ## The parametric P2 frame -/

/-- The `x`-question's true cell `{x = 1} = {0, 2}` on the worlds `(x, s)`.
Source: [[approval-final]] P2 l. 91 ("Domain `𝒟` = functions of `x`")
Kind: D
Fidelity: exact -/
abbrev xq : Finset (Fin 4) := {0, 2}

/-- The two-signal overseer frame: at the signal-1 worlds `0, 1` the row is `(h₁, 1 − h₁, 0, 0)`
(credence `h₁ = p_{H₁}` in `x = 1`, knowing `s = 1`); at the signal-2 worlds `2, 3` it is
`(0, 0, h₂, 1 − h₂)`.
Source: [[approval-final]] P2 l. 91 ("Overseer credences given its signal: `p_{H₁}`, `p_{H₂}`")
Kind: D
Fidelity: exact (the overseer's credence about `x` given its signal, as a row on `(x, s)`) -/
def p2Frame (h₁ h₂ : ℝ) (hh₁ : 0 ≤ h₁ ∧ h₁ ≤ 1) (hh₂ : 0 ≤ h₂ ∧ h₂ ≤ 1) : Frame (Fin 4) :=
  mk4 ![h₁, 1 - h₁, 0, 0] ![h₁, 1 - h₁, 0, 0] ![0, 0, h₂, 1 - h₂] ![0, 0, h₂, 1 - h₂]
    (simplex4 _ _ _ _ hh₁.1 (by linarith [hh₁.2]) le_rfl le_rfl (by ring))
    (simplex4 _ _ _ _ hh₁.1 (by linarith [hh₁.2]) le_rfl le_rfl (by ring))
    (simplex4 _ _ _ _ le_rfl le_rfl hh₂.1 (by linarith [hh₂.2]) (by ring))
    (simplex4 _ _ _ _ le_rfl le_rfl hh₂.1 (by linarith [hh₂.2]) (by ring))

/-- The joint deferrer on `(x, s)`: `π(s = 1) = σ`, `π(x = 1 | s = 1) = q₁ = p̂₁`,
`π(x = 1 | s = 2) = q₂ = p̂₂`, i.e. `(σ q₁, σ (1 − q₁), (1 − σ) q₂, (1 − σ)(1 − q₂))`.
Source: [[approval-final]] P2 l. 91 (`P(1,1) = 0.45`, `P(0,1) = 0.05`, `P(1,2) = 0.10`,
`P(0,2) = 0.40`)
Kind: D
Fidelity: exact -/
def p2Def (σ q₁ q₂ : ℝ) : Fin 4 → ℝ :=
  ![σ * q₁, σ * (1 - q₁), (1 - σ) * q₂, (1 - σ) * (1 - q₂)]

/-- The deferrer's prior in `x = 1`: `p_P = σ q₁ + (1 − σ) q₂`.
Source: [[approval-final]] P2 l. 91 (`p_P := P(x = 1) = 0.55`)
Kind: D
Fidelity: exact -/
def p2Prior (σ q₁ q₂ : ℝ) : ℝ := σ * q₁ + (1 - σ) * q₂

/-- **Betweenness** for two signals with `p_{H₂} < p_{H₁}`: `p̂₂ ≤ p_{H₂} ≤ p_P ≤ p_{H₁} ≤ p̂₁`.
Source: [[approval-final]] P2′ l. 93 ("Betweenness: `p_P ≤ p_{H₁} ≤ p̂₁` and `p̂₂ ≤ p_{H₂} ≤ p_P`")
Kind: D
Fidelity: exact -/
def Betweenness (σ q₁ q₂ h₁ h₂ : ℝ) : Prop :=
  q₂ ≤ h₂ ∧ h₂ ≤ p2Prior σ q₁ q₂ ∧ p2Prior σ q₁ q₂ ≤ h₁ ∧ h₁ ≤ q₁

/-- The rows of the P2 frame, by signal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem p2Frame_P (h₁ h₂ : ℝ) (hh₁ : 0 ≤ h₁ ∧ h₁ ≤ 1) (hh₂ : 0 ≤ h₂ ∧ h₂ ≤ 1) (w : Fin 4) :
    (p2Frame h₁ h₂ hh₁ hh₂).P w =
      if w.val < 2 then ![h₁, 1 - h₁, 0, 0] else ![0, 0, h₂, 1 - h₂] := by
  fin_cases w <;> rfl

/-- The rows' credences in `x = 1`: `h₁` at the signal-1 worlds, `h₂` at the signal-2 worlds.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem p2Frame_mass_xq (h₁ h₂ : ℝ) (hh₁ : 0 ≤ h₁ ∧ h₁ ≤ 1) (hh₂ : 0 ≤ h₂ ∧ h₂ ≤ 1) (w : Fin 4) :
    mass ((p2Frame h₁ h₂ hh₁ hh₂).P w) xq = if w.val < 2 then h₁ else h₂ := by
  rw [p2Frame_P]
  split_ifs <;> simp +decide [mass_eq_sum_ite, Fin.sum_univ_four, xq, vec4_two, vec4_three]

/-- The deferrer is nonnegative for `0 ≤ σ ≤ 1`, `0 ≤ q₁, q₂ ≤ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem p2Def_nonneg {σ q₁ q₂ : ℝ} (hσ : 0 ≤ σ ∧ σ ≤ 1) (hq₁ : 0 ≤ q₁ ∧ q₁ ≤ 1)
    (hq₂ : 0 ≤ q₂ ∧ q₂ ≤ 1) : ∀ w, 0 ≤ p2Def σ q₁ q₂ w := by
  intro w
  have h1 : 0 ≤ σ * q₁ := mul_nonneg hσ.1 hq₁.1
  have h2 : 0 ≤ σ * (1 - q₁) := mul_nonneg hσ.1 (by linarith [hq₁.2])
  have h3 : 0 ≤ (1 - σ) * q₂ := mul_nonneg (by linarith [hσ.2]) hq₂.1
  have h4 : 0 ≤ (1 - σ) * (1 - q₂) := mul_nonneg (by linarith [hσ.2]) (by linarith [hq₂.2])
  fin_cases w <;> simp [p2Def, vec4_two, vec4_three] <;> first | assumption | nlinarith [h1, h2, h3, h4]

/-- The deferrer is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem p2Def_mem {σ q₁ q₂ : ℝ} (hσ : 0 ≤ σ ∧ σ ≤ 1) (hq₁ : 0 ≤ q₁ ∧ q₁ ≤ 1)
    (hq₂ : 0 ≤ q₂ ∧ q₂ ≤ 1) : p2Def σ q₁ q₂ ∈ stdSimplex ℝ (Fin 4) :=
  simplex4 _ _ _ _ (mul_nonneg hσ.1 hq₁.1) (mul_nonneg hσ.1 (by linarith [hq₁.2]))
    (mul_nonneg (by linarith [hσ.2]) hq₂.1) (mul_nonneg (by linarith [hσ.2]) (by linarith [hq₂.2]))
    (by ring)

/-- Rows are determined by `P(x = 1)` when `h₂ ≠ h₁`: the two-cell Value theorem's `hdet`.
Source: none: infrastructure (the hypothesis of `valuesWrt_questionOf_of_simpleTrustOn`)
Kind: L
Fidelity: n/a -/
theorem p2Frame_hdet {σ q₁ q₂ h₁ h₂ : ℝ} (hh₁ : 0 ≤ h₁ ∧ h₁ ≤ 1) (hh₂ : 0 ≤ h₂ ∧ h₂ ≤ 1)
    (hne : h₂ ≠ h₁) : ∀ w v, 0 < p2Def σ q₁ q₂ w → 0 < p2Def σ q₁ q₂ v →
      mass ((p2Frame h₁ h₂ hh₁ hh₂).P w) xq = mass ((p2Frame h₁ h₂ hh₁ hh₂).P v) xq →
      (p2Frame h₁ h₂ hh₁ hh₂).P w = (p2Frame h₁ h₂ hh₁ hh₂).P v := by
  intro w v _ _ h
  rw [p2Frame_mass_xq, p2Frame_mass_xq] at h
  rw [p2Frame_P, p2Frame_P]
  split_ifs at h ⊢ <;> first | rfl | exact absurd h hne.symm | exact absurd h hne

/-! ## Betweenness is necessary and sufficient -/

/-- **Local Total Trust on the P2 family is betweenness**: for `0 < σ < 1`, credences in
`[0, 1]` and `p_{H₂} < p_{H₁}`, the deferrer totally trusts the overseer with respect to the
`x`-question iff `p̂₂ ≤ p_{H₂} ≤ p_P ≤ p_{H₁} ≤ p̂₁`. By T4(b) local Total Trust is the pair of
Simple-Trust cuts at every `t`; on this frame `[P(x=1) ≥ t]` is everything for `t ≤ p_{H₂}` (cut:
`t ≤ p_P`), the signal-1 worlds for `p_{H₂} < t ≤ p_{H₁}` (cut: `t ≤ p̂₁`) and empty above, and
dually for the below cut — so the four cuts at the attained thresholds `p_{H₁}, p_{H₂}` are the
four inequalities, and they imply all the others. Necessity is the new half (approval-final O1
asked for it); sufficiency is P2′'s envelope argument specialised.
Source: [[approval-final]] P2′ l. 93, O1 l. 197; corr-wf14-2-047; mandate T4(c)
Kind: C (T4(b)'s `totalTrustWrt_questionOf_iff` plus case analysis at the two attained thresholds; re-kinded from P, audit r2 fidelity N2)
Fidelity: exact (the two-signal family; the source's example is `p2_instance`)
Hyps: (a) `0 < σ < 1`, `q₁ q₂ h₁ h₂ ∈ [0, 1]`, `h₂ < h₁` (two distinct attained thresholds) -/
theorem p2_totalTrustWrt_iff {σ q₁ q₂ h₁ h₂ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    (hq₁ : 0 ≤ q₁ ∧ q₁ ≤ 1) (hq₂ : 0 ≤ q₂ ∧ q₂ ≤ 1) (hh₁ : 0 ≤ h₁ ∧ h₁ ≤ 1)
    (hh₂ : 0 ≤ h₂ ∧ h₂ ≤ 1) (hlt : h₂ < h₁) :
    TotalTrustWrt (questionOf xq) (p2Def σ q₁ q₂) (p2Frame h₁ h₂ hh₁ hh₂) ↔
      Betweenness σ q₁ q₂ h₁ h₂ := by
  have hπ := p2Def_nonneg ⟨hσ.le, hσ1.le⟩ hq₁ hq₂
  rw [totalTrustWrt_questionOf_iff hπ]
  have m0 := p2Frame_mass_xq h₁ h₂ hh₁ hh₂ 0
  have m1 := p2Frame_mass_xq h₁ h₂ hh₁ hh₂ 1
  have m2 := p2Frame_mass_xq h₁ h₂ hh₁ hh₂ 2
  have m3 := p2Frame_mass_xq h₁ h₂ hh₁ hh₂ 3
  simp only [show ((0 : Fin 4)).val < 2 from by decide, show ((1 : Fin 4)).val < 2 from by decide,
    show ¬ ((2 : Fin 4)).val < 2 from by decide, show ¬ ((3 : Fin 4)).val < 2 from by decide,
    if_true, if_false] at m0 m1 m2 m3
  have hle : h₂ ≤ h₁ := hlt.le
  have hnle : ¬ h₁ ≤ h₂ := not_le.2 hlt
  have h1σ : 0 < 1 - σ := by linarith
  constructor
  · rintro ⟨hA, hB⟩
    have a2 := hA h₂
    have a1 := hA h₁
    have b1 := hB h₁
    have b2 := hB h₂
    rw [mass_probEvent_eq, mass_inter_probEvent_eq] at a1 a2
    rw [mass_probEventLE_eq, mass_inter_probEventLE_eq] at b1 b2
    simp only [Fin.sum_univ_four, m0, m1, m2, m3] at a1 a2 b1 b2
    simp +decide [p2Def, xq, vec4_two, vec4_three, hle, hnle] at a1 a2 b1 b2
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : (1 - σ) * q₂ ≤ (1 - σ) * h₂ := by linarith
      exact le_of_mul_le_mul_left this h1σ
    · unfold p2Prior; linarith
    · unfold p2Prior; linarith
    · have : σ * h₁ ≤ σ * q₁ := by linarith
      exact le_of_mul_le_mul_left this hσ
  · rintro ⟨hb1, hb2, hb3, hb4⟩
    unfold p2Prior at hb2 hb3
    constructor
    · intro t
      rw [mass_probEvent_eq, mass_inter_probEvent_eq]
      simp only [Fin.sum_univ_four, m0, m1, m2, m3]
      simp +decide [p2Def, xq, vec4_two, vec4_three]
      split_ifs <;>
        first
          | linarith
          | nlinarith [mul_nonneg hσ.le (sub_nonneg.2 (le_trans ‹t ≤ h₁› hb4))]
    · intro t
      rw [mass_probEventLE_eq, mass_inter_probEventLE_eq]
      simp only [Fin.sum_univ_four, m0, m1, m2, m3]
      simp +decide [p2Def, xq, vec4_two, vec4_three]
      split_ifs <;>
        first
          | linarith
          | nlinarith [mul_nonneg h1σ.le (sub_nonneg.2 (le_trans hb1 ‹h₂ ≤ t›))]

/-- **Local Value on the P2 family is betweenness** too: the rows are determined by `P(x = 1)`
(`p2Frame_hdet`), so the two-cell theorem makes local Value and local Total Trust coincide on
this family, and the previous theorem reads them both as betweenness. Hence P2′'s sufficiency
argument has a converse: an overseer credence outside `[p_P, p̂_s]` on either signal breaks
local Value (O1's "failure boundary") — the source's "and such an overseer also violates Total
Trust" is the same fact, not an extra one.
Source: [[approval-final]] P2′ l. 93, S2 l. 53, O1 l. 197; corr-wf14-2-047
Kind: C
Fidelity: exact (two-signal family)
Hyps: (a) as `p2_totalTrustWrt_iff` -/
theorem p2_valuesWrt_iff {σ q₁ q₂ h₁ h₂ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    (hq₁ : 0 ≤ q₁ ∧ q₁ ≤ 1) (hq₂ : 0 ≤ q₂ ∧ q₂ ≤ 1) (hh₁ : 0 ≤ h₁ ∧ h₁ ≤ 1)
    (hh₂ : 0 ≤ h₂ ∧ h₂ ≤ 1) (hlt : h₂ < h₁) :
    ValuesWrt (questionOf xq) (p2Def σ q₁ q₂) (p2Frame h₁ h₂ hh₁ hh₂) ↔
      Betweenness σ q₁ q₂ h₁ h₂ :=
  (localTotalTrust_iff_localValue_two_cell (p2Def_mem ⟨hσ.le, hσ1.le⟩ hq₁ hq₂)
    (p2Frame_hdet hh₁ hh₂ hlt.ne)).symm.trans
    (p2_totalTrustWrt_iff hσ hσ1 hq₁ hq₂ hh₁ hh₂ hlt)

/-! ## The source's instances -/

/-- **The P2 example** (`p̂ = (9/10, 1/5)`, `p_H = (3/5, 2/5)`, `σ = 1/2`, so `p_P = 11/20`):
betweenness `1/5 ≤ 2/5 ≤ 11/20 ≤ 3/5 ≤ 9/10` holds, hence local Total Trust and local Value with
respect to the `x`-question. Both `x`-cells have positive mass (`11/20`, `9/20`) and the rows
differ across the signals, so the local predicates are not vacuous.
Source: [[approval-final]] P2 l. 91, P2′ l. 93; mandate T4(c)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem p2_instance :
    p2Prior (1 / 2) (9 / 10) (1 / 5) = 11 / 20 ∧
    TotalTrustWrt (questionOf xq) (p2Def (1 / 2) (9 / 10) (1 / 5))
      (p2Frame (3 / 5) (2 / 5) (by norm_num) (by norm_num)) ∧
    ValuesWrt (questionOf xq) (p2Def (1 / 2) (9 / 10) (1 / 5))
      (p2Frame (3 / 5) (2 / 5) (by norm_num) (by norm_num)) ∧
    mass (p2Def (1 / 2) (9 / 10) (1 / 5)) xq = 11 / 20 ∧
    mass (p2Def (1 / 2) (9 / 10) (1 / 5)) xqᶜ = 9 / 20 := by
  refine ⟨by norm_num [p2Prior], ?_, ?_, ?_, ?_⟩
  · exact (p2_totalTrustWrt_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num [Betweenness, p2Prior])
  · exact (p2_valuesWrt_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num [Betweenness, p2Prior])
  · simp +decide [mass_eq_sum_ite, Fin.sum_univ_four, xq, p2Def, vec4_two, vec4_three] <;> norm_num
  · simp +decide [mass_eq_sum_ite, Fin.sum_univ_four, xq, p2Def, vec4_two, vec4_three] <;> norm_num

/-- **The overconfident overseer** (`p_H = (19/20, 1/10)` at the same `p̂`): betweenness fails
(`19/20 > 9/10`), so both local Total Trust and local Value fail — the source's failure boundary
reached from the necessity half.
Source: [[approval-final]] P2′ l. 93 ("overconfident overseer `(0.95, 0.1)`: worst slack
`−0.278`"), O1 l. 197
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem p2_overconfident :
    ¬ TotalTrustWrt (questionOf xq) (p2Def (1 / 2) (9 / 10) (1 / 5))
      (p2Frame (19 / 20) (1 / 10) (by norm_num) (by norm_num)) ∧
    ¬ ValuesWrt (questionOf xq) (p2Def (1 / 2) (9 / 10) (1 / 5))
      (p2Frame (19 / 20) (1 / 10) (by norm_num) (by norm_num)) := by
  constructor
  · intro h
    have := (p2_totalTrustWrt_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)).1 h
    norm_num [Betweenness, p2Prior] at this
  · intro h
    have := (p2_valuesWrt_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)).1 h
    norm_num [Betweenness, p2Prior] at this

end

end Cleanroom.Corrigibility.CorrLegitGeneral

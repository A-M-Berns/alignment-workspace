import Cleanroom.Decision.DpTwoLesions.InteriorReal

/-!
# T20 (extension) — `δ*` bracketed exactly

At the doc's parameters the discriminant of the quadratic of record is
`−(160δ³ − 4404δ² + 1020δ − 25)/25` (`docP_discrim_eq`, a polynomial identity in `δ`), so the
three-fixed-point regime's discriminant condition is `cubic(δ) < 0`. The cubic changes sign
between `0.02785` and `0.02786` (`deltaStar_bracket`), and the regime switches there: at
`δ = 2785/100000` there are exactly three fixed points, at `δ = 2786/100000` the unique fixed
point is `0` (`regime_switches_at_deltaStar`). The doc's "`δ* ≈ 0.028`" is this root; uniqueness
of the root in `(0, 1/5)` (the cubic is increasing on `(0, 0.1166)` and positive after) is
stated in the report, not formalized.
Serves [[dp-two-lesions-mandate]] T20.
-/

namespace Cleanroom.Decision.DpTwoLesions

open Set

namespace DlParams

/-- The cubic `160δ³ − 4404δ² + 1020δ − 25` whose root in `(0, 1/5)` is `δ*`.
Source: mandate §3.6 ("`δ*` is the root of `160δ³ − 4404δ² + 1020δ − 25` in `(0, 1/5)`")
Kind: D -/
def deltaStarCubic (δ : ℝ) : ℝ := 160 * δ ^ 3 - 4404 * δ ^ 2 + 1020 * δ - 25

/-- **The discriminant at the doc's parameters is `−cubic(δ)/25`** for every grip.
Source: mandate §3.6 ("`discrim = −(160δ³ − 4404δ² + 1020δ − 25)/25`"), re-derived
Kind: P
Fidelity: exact
Hyps: none -/
theorem docP_discrim_eq (δ : ℝ) (h0 : 0 < δ) (h1 : δ ≤ 1) :
    discrim (docP δ h0 h1).qA (docP δ h0 h1).qB (docP δ h0 h1).qE = -(deltaStarCubic δ) / 25 := by
  simp only [discrim, qA, qB, qE, kappa, kcC, docP, deltaStarCubic]
  ring

/-- The cubic changes sign between `0.02785` and `0.02786`.
Source: mandate §3.6 ("`≈ 0.027857`")
Kind: N+ -/
theorem deltaStar_bracket :
    deltaStarCubic (2785/100000) < 0 ∧ 0 < deltaStarCubic (2786/100000) := by
  unfold deltaStarCubic; norm_num

/-- **The regime switches at `δ*`**: at `δ = 2785/100000` the fixed points are exactly three
(`0 < p̌ < p̂ < 1`), at `δ = 2786/100000` the unique fixed point is `0` — the limit-of-fixed-points
corollary made quantitative.
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 3(iii) ("the three-fixed-point regime
obtains for `δ` below `δ*`"), "`δ* ≈ 0.028`"; mandate T20
Kind: N+
Fidelity: exact (a bracket, rule 4; uniqueness of the switch not formalized) -/
theorem regime_switches_at_deltaStar :
    (∃ p₁ p₂ : ℝ, 0 < p₁ ∧ p₁ < p₂ ∧ p₂ < 1 ∧
      (docP (2785/100000 : ℝ) (by norm_num) (by norm_num)).fixedPts = {0, p₁, p₂}) ∧
    (docP (2786/100000 : ℝ) (by norm_num) (by norm_num)).fixedPts = {0} := by
  constructor
  · apply (DlParams.prop3_three_iff _ (docP_hypH _ _ _)).mpr
    refine ⟨?_, ?_, ?_⟩
    · rw [docP_discrim_eq]; have := deltaStar_bracket.1; linarith
    · simp only [qA, qB, kappa, kcC, docP]; norm_num
    · simp only [qA, qB, kappa, kcC, docP]; norm_num
  · apply DlParams.fixedPts_eq_singleton_of_Q_pos _ (docP_hypH _ _ _)
    intro p _ _
    apply DlParams.Q_pos_of_discrim_neg
    rw [docP_discrim_eq]; have := deltaStar_bracket.2; linarith

/-! ## Uniqueness of `δ*` in `(0, 1/5)` (repair round 1, audit r1 N9) -/

/-- The cubic is strictly increasing on `(0, 23/200]`: `cubic(b) − cubic(a) =
(b − a)(160(a² + ab + b²) − 4404(a + b) + 1020)` and `4404(a + b) ≤ 1012.92 < 1020` there.
Source: none: infrastructure (the monotonicity behind the uniqueness of `δ*`)
Kind: L -/
theorem deltaStarCubic_strictMonoOn : StrictMonoOn deltaStarCubic (Set.Ioc 0 (23/200)) := by
  intro a ha b hb hab
  simp only [deltaStarCubic]
  have h1 : a + b ≤ 23/100 := by linarith [ha.2, hb.2]
  have hab' : 0 < b - a := sub_pos.mpr hab
  have key : 160 * b ^ 3 - 4404 * b ^ 2 + 1020 * b - 25 -
      (160 * a ^ 3 - 4404 * a ^ 2 + 1020 * a - 25) =
      (b - a) * (160 * (a ^ 2 + a * b + b ^ 2) - 4404 * (a + b) + 1020) := by ring
  have hpos : 0 < 160 * (a ^ 2 + a * b + b ^ 2) - 4404 * (a + b) + 1020 := by
    nlinarith [sq_nonneg a, sq_nonneg b, mul_pos ha.1 hb.1, h1]
  nlinarith [key, mul_pos hab' hpos]

/-- The cubic is positive on `[23/200, 1/5]`: `cubic(δ) = cubic(1/5) + (δ − 1/5)·g(δ)` with
`cubic(1/5) = 103/25` and `g(δ) = 160δ² − 4372δ + 728/5 < 0` there.
Source: none: infrastructure
Kind: L -/
theorem deltaStarCubic_pos_of_ge {δ : ℝ} (h1 : 23/200 ≤ δ) (h2 : δ ≤ 1/5) :
    0 < deltaStarCubic δ := by
  unfold deltaStarCubic
  have hδ0 : 0 ≤ δ := by linarith
  have hsq : δ ^ 2 ≤ δ / 5 := by nlinarith [mul_nonneg (sub_nonneg.mpr h2) hδ0]
  have hg : 160 * δ ^ 2 - 4372 * δ + 728/5 < 0 := by nlinarith
  have key : 160 * δ ^ 3 - 4404 * δ ^ 2 + 1020 * δ - 25 =
      103/25 + (δ - 1/5) * (160 * δ ^ 2 - 4372 * δ + 728/5) := by ring
  have := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h2) hg.le
  linarith [key, this]

/-- Two roots of the cubic in `(0, 1/5)` coincide (both lie in `(0, 23/200]`, where the cubic
is strictly increasing).
Source: none: infrastructure
Kind: L -/
theorem deltaStarCubic_root_unique {a b : ℝ} (ha : 0 < a ∧ a < 1/5) (hb : 0 < b ∧ b < 1/5)
    (hfa : deltaStarCubic a = 0) (hfb : deltaStarCubic b = 0) : a = b := by
  have ha' : a ≤ 23/200 := by
    by_contra h; push_neg at h
    exact absurd hfa (deltaStarCubic_pos_of_ge h.le ha.2.le).ne'
  have hb' : b ≤ 23/200 := by
    by_contra h; push_neg at h
    exact absurd hfb (deltaStarCubic_pos_of_ge h.le hb.2.le).ne'
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := deltaStarCubic_strictMonoOn ⟨ha.1, ha'⟩ ⟨hb.1, hb'⟩ h
    rw [hfa, hfb] at this; exact lt_irrefl _ this
  · have := deltaStarCubic_strictMonoOn ⟨hb.1, hb'⟩ ⟨ha.1, ha'⟩ h
    rw [hfa, hfb] at this; exact lt_irrefl _ this

/-- **`δ*` is the unique root of the cubic in `(0, 1/5)`, it lies in `(0.02785, 0.02786)`, and
the cubic is negative exactly below it**: for every grip `δ ∈ (0, 1/5)`, `cubic(δ) < 0 ↔ δ < δ*`.
With `docP_discrim_eq`, the discriminant condition of the three-fixed-point regime at the doc's
parameters holds exactly for `δ < δ*` (the vertex condition `0 < −qB/(2qA) < 1` is checked at
the instance grips, not here).
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 3(iii) ("the three-fixed-point regime
obtains for `δ` below `δ*`"), "`δ* ≈ 0.028`"; mandate T20
Kind: P
Fidelity: exact (existence by the intermediate value theorem on the bracket, uniqueness by
monotonicity)
Hyps: none -/
theorem deltaStar_threshold :
    ∃ δs : ℝ, 0 < δs ∧ δs < 1/5 ∧ deltaStarCubic δs = 0 ∧
      2785/100000 < δs ∧ δs < 2786/100000 ∧
      (∀ δ', 0 < δ' → δ' < 1/5 → deltaStarCubic δ' = 0 → δ' = δs) ∧
      (∀ δ, 0 < δ → δ < 1/5 → (deltaStarCubic δ < 0 ↔ δ < δs)) := by
  have hcont : Continuous deltaStarCubic := by unfold deltaStarCubic; fun_prop
  obtain ⟨hlo, hhi⟩ := deltaStar_bracket
  have hmem : (0 : ℝ) ∈ Set.Icc (deltaStarCubic (2785/100000)) (deltaStarCubic (2786/100000)) :=
    ⟨hlo.le, hhi.le⟩
  obtain ⟨δs, hδs, hfδs⟩ :=
    intermediate_value_Icc (by norm_num) hcont.continuousOn hmem
  have h0 : 0 < δs := by linarith [hδs.1]
  have h15 : δs < 1/5 := by linarith [hδs.2]
  have hlo' : 2785/100000 < δs := by
    rcases hδs.1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hfδs; linarith
  have hhi' : δs < 2786/100000 := by
    rcases hδs.2.lt_or_eq with h | h
    · exact h
    · rw [h] at hfδs; linarith
  have hδs' : δs ≤ 23/200 := by linarith
  refine ⟨δs, h0, h15, hfδs, hlo', hhi', fun δ' h0' h1' hf' =>
    deltaStarCubic_root_unique ⟨h0', h1'⟩ ⟨h0, h15⟩ hf' hfδs, fun δ hδ0 hδ1 => ?_⟩
  constructor
  · intro hneg
    by_contra hge
    push_neg at hge
    have hδ' : δ ≤ 23/200 := by
      by_contra h; push_neg at h
      exact absurd hneg (not_lt.mpr (deltaStarCubic_pos_of_ge h.le hδ1.le).le)
    rcases hge.lt_or_eq with h | h
    · have := deltaStarCubic_strictMonoOn ⟨h0, hδs'⟩ ⟨hδ0, hδ'⟩ h
      rw [hfδs] at this; linarith
    · rw [← h, hfδs] at hneg; exact lt_irrefl _ hneg
  · intro hlt
    have := deltaStarCubic_strictMonoOn ⟨hδ0, by linarith⟩ ⟨h0, hδs'⟩ hlt
    rw [hfδs] at this; exact this

/-- **The discriminant at the doc's parameters is positive exactly below `δ*`**, for every grip
in `(0, 1/5)`.
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 3(iii); mandate T20
Kind: C
Fidelity: exact
Hyps: none -/
theorem docP_discrim_pos_iff :
    ∃ δs : ℝ, 2785/100000 < δs ∧ δs < 2786/100000 ∧
      ∀ δ (h0 : 0 < δ) (h1 : δ ≤ 1), δ < 1/5 →
        (0 < discrim (docP δ h0 h1).qA (docP δ h0 h1).qB (docP δ h0 h1).qE ↔ δ < δs) := by
  obtain ⟨δs, -, -, -, hlo, hhi, -, hiff⟩ := deltaStar_threshold
  refine ⟨δs, hlo, hhi, fun δ h0 h1 h15 => ?_⟩
  rw [docP_discrim_eq, ← hiff δ h0 h15]
  constructor
  · intro h; linarith
  · intro h; linarith

end DlParams

end Cleanroom.Decision.DpTwoLesions

import Cleanroom.Decision.DpTwoLesions.Interior
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Convex.Function

/-!
# T4 — Proposition 3(i) and (iii) over `ℝ`

The three-fixed-point characterisation as an iff (`prop3_three_iff`: square roots exist in
`ℝ`), the unique-fixed-point characterisation (`prop3_unique_iff`: by the intermediate value
theorem), convexity of `Δ` on `[0, 1]` (Proposition 3(i), by the doc's own decomposition into a
convex and a minus-concave Möbius piece), and the doc's three instances: `δ = 1/10` (no
interior fixed point), `δ = 1/100` (the two surds `23167/41334 ∓ 25√105835/20667`), and
`δ = 1/1000` (the roots bracketed by sign changes, rule 4: no decimals in statements).
Serves [[dp-two-lesions-mandate]] T4 (dp-core-075).
-/

namespace Cleanroom.Decision.DpTwoLesions

open Finset Set

namespace DlParams

variable (P : DlParams ℝ)

/-! ## The regime criterion as an iff -/

/-- **Proposition 3(iii), the regime criterion**: under (H), the fixed points are exactly
`{0, p̌, p̂}` with `0 < p̌ < p̂ < 1` **iff** `discrim qA qB qE > 0` and the vertex `−qB/(2qA)`
lies in `(0, 1)` — the doc's `m(δ) < π`, made a condition on the explicit quadratic.
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 3(iii) ("if `m(δ) < π`, there are exactly
three fixed points, `0 < p̌(δ) < p̂(δ) < 1`, the latter two being the solutions of `Δ(p) = π`");
mandate §3.6 ("the three-fixed-point regime is `discrim A B E > 0 ∧ 0 < −B/(2A) < 1`")
Kind: P
Fidelity: exact ("exactly three" as a set equality; the regime as the discriminant condition,
which is the doc's `m(δ) < π` since `m(δ) < π ↔ Q < 0 somewhere ↔` these)
Hyps: (a) (H) -/
theorem prop3_three_iff (hH : P.HypH) :
    (∃ p₁ p₂ : ℝ, 0 < p₁ ∧ p₁ < p₂ ∧ p₂ < 1 ∧ P.fixedPts = {0, p₁, p₂}) ↔
    (0 < discrim P.qA P.qB P.qE ∧ 0 < -P.qB / (2 * P.qA) ∧ -P.qB / (2 * P.qA) < 1) := by
  constructor
  · rintro ⟨p₁, p₂, h0, h12, h1, hset⟩
    exact P.prop3_three_imp hH h0 h12 h1 hset
  · rintro ⟨hd, hv0, hv1⟩
    have hs0 : 0 < Real.sqrt (discrim P.qA P.qB P.qE) := Real.sqrt_pos.mpr hd
    have hs : discrim P.qA P.qB P.qE =
        Real.sqrt (discrim P.qA P.qB P.qE) * Real.sqrt (discrim P.qA P.qB P.qE) :=
      (Real.mul_self_sqrt hd.le).symm
    obtain ⟨hr0, hr12, hr1, hset⟩ := P.fixedPts_eq_of_sqrt hH hs0 hs hv0 hv1
    exact ⟨_, _, hr0, hr12, hr1, hset⟩

/-- `Q` is continuous. Source: none: infrastructure. Kind: L -/
theorem continuous_Q : Continuous P.Q := by
  unfold Q; fun_prop

/-- **Proposition 3(iii), the unique-fixed-point regime**: under (H), `0` is the unique fixed
point **iff** `Q > 0` on `[0, 1]` (the doc's `m(δ) > π`). The `⇒` half needs the intermediate
value theorem: a non-positive value of `Q` in `(0, 1)` produces a root there.
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 3(iii) ("if `m(δ) > π`, the unique fixed
point is `0`")
Kind: P
Fidelity: exact (the boundary `m(δ) = π`, a double root and exactly two fixed points, is
neither regime — the doc is silent on it)
Hyps: (a) (H) -/
theorem prop3_unique_iff (hH : P.HypH) :
    P.fixedPts = {0} ↔ ∀ p ∈ Icc (0 : ℝ) 1, 0 < P.Q p := by
  constructor
  · intro hset p hp
    by_contra hle
    push_neg at hle
    have hQ0 := P.Q_zero_pos hH
    have hp0 : 0 < p := by
      rcases hp.1.lt_or_eq with h | h
      · exact h
      · rw [← h] at hle; linarith
    have hp1 : p < 1 := by
      rcases hp.2.lt_or_eq with h | h
      · exact h
      · rw [h] at hle; linarith [P.Q_one_pos hH]
    have hmem : (0 : ℝ) ∈ Icc (P.Q p) (P.Q 0) := ⟨hle, hQ0.le⟩
    obtain ⟨r, hr, hQr⟩ := intermediate_value_Icc' hp0.le P.continuous_Q.continuousOn hmem
    have hr0 : 0 < r := by
      rcases hr.1.lt_or_eq with h | h
      · exact h
      · rw [← h] at hQr; linarith
    have hr1 : r < 1 := lt_of_le_of_lt hr.2 hp1
    have hmem' : r ∈ P.fixedPts := by
      rw [P.prop3_fixedPoints_eq hH]; right; exact ⟨hr0, hr1, hQr⟩
    rw [hset, mem_singleton_iff] at hmem'
    linarith
  · intro hQ
    exact P.fixedPts_eq_singleton_of_Q_pos hH (fun p h0 h1 => hQ p ⟨h0, h1⟩)

/-! ## Proposition 3(i): convexity -/

/-- `p ↦ 1/(u + v·p)` is convex on `[0, 1]` when positive there (`u > 0`, `u + v > 0`): the
convexity of `1/x` composed with an affine map, proved from the definition.
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 3(i) proof ("a positive constant times a
convex function of `p`")
Kind: L -/
theorem convexOn_one_div_affine (u v : ℝ) (hu : 0 < u) (huv : 0 < u + v) :
    ConvexOn ℝ (Icc 0 1) (fun p : ℝ => 1 / (u + v * p)) := by
  have hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < u + v * x := by
    intro x hx
    have : u + v * x = u * (1 - x) + (u + v) * x := by ring
    rw [this]
    rcases hx.1.lt_or_eq with h | h
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hu.le (by linarith [hx.2])) (mul_pos huv h)
    · rw [← h]; simpa using hu
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hX := hpos x hx
  have hY := hpos y hy
  have hZ : u + v * (a * x + b * y) = a * (u + v * x) + b * (u + v * y) := by
    linear_combination (-u) * hab
  rw [hZ]
  have hXY : 0 < a * (u + v * x) + b * (u + v * y) := by
    rcases ha.lt_or_eq with ha' | ha'
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hX) (mul_nonneg hb hY.le)
    · rw [← ha'] at hab ⊢
      have hb1 : b = 1 := by linarith
      rw [hb1]; simpa using hY
  rw [mul_one_div, mul_one_div, div_add_div _ _ hX.ne' hY.ne',
    div_le_div_iff₀ hXY (mul_pos hX hY)]
  have key : (a * (u + v * y) + b * (u + v * x)) * (a * (u + v * x) + b * (u + v * y)) -
      (u + v * x) * (u + v * y) = a * b * ((u + v * x) - (u + v * y)) ^ 2 := by
    linear_combination ((u + v * x) * (u + v * y) * (a + b + 1)) * hab
  nlinarith [key, mul_nonneg (mul_nonneg ha hb) (sq_nonneg ((u + v * x) - (u + v * y)))]

/-- **Proposition 3(i): `Δ` is convex on `[0, 1]`.** The doc's proof: the smoke conditional is
`c_C + ρδL(γ₁ − c_C)/(ρδL + κp)`, a non-negative multiple of a convex function plus a
constant; the abstain conditional is `c_C + ρAδA(γ₀ − c_C)/(ρAδA + κ(1−p))`, concave; a convex
function less a concave one is convex.
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 3(i) ("`Δ` is convex on `[0, 1]`")
Kind: P
Fidelity: exact (general `γ`, two grips)
Hyps: none -/
theorem prop3_convex : ConvexOn ℝ (Icc 0 1) P.Delta := by
  have hk := P.kappa_pos
  have ha : 0 < P.ρ * P.δL := mul_pos P.ρ_pos P.δL_pos
  have hb : 0 < P.ρA * P.δA := mul_pos P.ρA_pos P.δA_pos
  have hc₁ : 0 ≤ P.β * (P.ρ * P.δL) * (P.kappa * P.γ₁ - P.kcC) / P.kappa :=
    div_nonneg (mul_nonneg (mul_nonneg P.β_pos.le ha.le) (sub_nonneg.mpr P.kcC_le_kappa_mul))
      hk.le
  have hc₂ : 0 ≤ P.β * (P.ρA * P.δA) * (P.kcC - P.kappa * P.γ₀) / P.kappa :=
    div_nonneg (mul_nonneg (mul_nonneg P.β_pos.le hb.le) (sub_nonneg.mpr P.kappa_mul_le_kcC))
      hk.le
  have h1 := (convexOn_one_div_affine (P.ρ * P.δL) P.kappa ha (by linarith)).smul hc₁
  have h2 := (convexOn_one_div_affine (P.ρA * P.δA + P.kappa) (-P.kappa) (by linarith)
    (by linarith)).smul hc₂
  refine (h1.add h2).congr ?_
  intro p hp
  simp only [Pi.add_apply, smul_eq_mul]
  rw [Delta_eq P p hp.1 hp.2]
  unfold condSmoke condAbstain
  have hd1 : P.ρ * P.δL + P.kappa * p ≠ 0 := (P.denomSmoke_pos p hp.1 hp.2).ne'
  have hd2 : P.ρA * P.δA + P.kappa * (1 - p) ≠ 0 := (P.denomAbstain_pos p hp.1 hp.2).ne'
  have hd2' : P.ρA * P.δA + P.kappa + -P.kappa * p ≠ 0 := by
    convert hd2 using 1; ring
  have hk' : P.kappa ≠ 0 := hk.ne'
  rw [mul_one_div, mul_one_div, div_add_div _ _ hd1 hd2', div_sub_div _ _ hd1 hd2, mul_div_assoc' P.β,
    div_eq_div_iff (mul_ne_zero hd1 hd2') (mul_ne_zero hd1 hd2)]
  field_simp
  ring

/-! ## The doc's instances -/

/-- The doc's parameters at `δ = 1/10`, over `ℝ`. Source: doc §4 numerics. Kind: D -/
noncomputable def docDeci : DlParams ℝ := docP (1/10) (by norm_num) (by norm_num)

/-- The doc's parameters at `δ = 1/100`, over `ℝ`. Source: doc §5 numerics. Kind: D -/
noncomputable def docCenti : DlParams ℝ := docP (1/100) (by norm_num) (by norm_num)

/-- The doc's parameters at `δ = 1/1000`, over `ℝ`. Source: doc §4 numerics. Kind: D -/
noncomputable def docMilli : DlParams ℝ := docP (1/1000) (by norm_num) (by norm_num)

/-- **At `δ = 1/10` the discriminant is negative**: no interior fixed point.
Source: [[two-lesions-doc-2026-09-18]] §4 ("at `δ = 0.1` the unique fixed point is `0`")
Kind: N+ -/
theorem docDeci_discrim_neg : discrim docDeci.qA docDeci.qB docDeci.qE < 0 := by
  simp only [discrim, qA, qB, qE, kappa, kcC, docDeci, docP]
  norm_num

/-- **At `δ = 1/10` the unique fixed point is `0`** (the doc's `δ = 0.1` instance, exactly).
Source: [[two-lesions-doc-2026-09-18]] §4 ("at `δ = 0.1` the unique fixed point is `0`")
Kind: N+
Fidelity: exact -/
theorem prop3_unique_at_doc_deci : docDeci.fixedPts = {0} :=
  docDeci.fixedPts_eq_singleton_of_Q_pos (docP_hypH _ _ _)
    (fun p _ _ => docDeci.Q_pos_of_discrim_neg docDeci_discrim_neg p)

/-- The quadratic's coefficients at `δ = 1/100`: `qA = 62001/62500`, `qB = −69501/62500`,
`qE = 39501/250000`.
Source: mandate §3.6, recomputed
Kind: N+ -/
theorem docCenti_coeffs :
    docCenti.qA = 62001/62500 ∧ docCenti.qB = -69501/62500 ∧ docCenti.qE = 39501/250000 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [qA, qB, qE, kappa, kcC, docCenti, docP]
    norm_num

/-- At `δ = 1/100`, `discrim = (150√105835/62500)²`.
Source: mandate §3.6 ("`23167/41334 ∓ 25√105835/20667`")
Kind: N+ -/
theorem docCenti_discrim :
    discrim docCenti.qA docCenti.qB docCenti.qE =
      (150 * Real.sqrt 105835 / 62500) * (150 * Real.sqrt 105835 / 62500) := by
  obtain ⟨hA, hB, hE⟩ := docCenti_coeffs
  rw [discrim, hA, hB, hE]
  have hs : Real.sqrt 105835 * Real.sqrt 105835 = 105835 := Real.mul_self_sqrt (by norm_num)
  have : 150 * Real.sqrt 105835 / 62500 * (150 * Real.sqrt 105835 / 62500) =
      150 * 150 / (62500 * 62500) * (Real.sqrt 105835 * Real.sqrt 105835) := by ring
  rw [this, hs]
  norm_num

/-- `325 < √105835 < 326`. Source: none: infrastructure. Kind: L -/
theorem sqrt_105835_bounds : 325 < Real.sqrt 105835 ∧ Real.sqrt 105835 < 326 :=
  ⟨(Real.lt_sqrt (by norm_num)).mpr (by norm_num), (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)⟩

/-- **Proposition 3 at the doc's `δ = 1/100`, exactly**: the fixed points are
`{0, 23167/41334 − 25√105835/20667, 23167/41334 + 25√105835/20667}` (`≈ 0, 0.16695, 0.95401`;
the note's `0.1670`, `0.9540`), with `0 < p̌ < p̂ < 1`.
Source: [[iv-design-draw-as-instrument]] §5 ("crosses zero at `p̌ = 0.1670` and `p̂ = 0.9540`");
[[two-lesions-doc-2026-09-18]] §5 ("reaches `0.954 = p̂`"); mandate §3.6
Kind: N+
Fidelity: exact (surds, rule 4) -/
theorem prop3_three_at_doc_centi :
    0 < 23167/41334 - 25 * Real.sqrt 105835 / 20667 ∧
    23167/41334 - 25 * Real.sqrt 105835 / 20667 < 23167/41334 + 25 * Real.sqrt 105835 / 20667 ∧
    23167/41334 + 25 * Real.sqrt 105835 / 20667 < 1 ∧
    docCenti.fixedPts = {0, 23167/41334 - 25 * Real.sqrt 105835 / 20667,
      23167/41334 + 25 * Real.sqrt 105835 / 20667} := by
  obtain ⟨hA, hB, hE⟩ := docCenti_coeffs
  have hs0 : 0 < 150 * Real.sqrt 105835 / 62500 := by
    have := sqrt_105835_bounds.1; positivity
  have hv0 : 0 < -docCenti.qB / (2 * docCenti.qA) := by rw [hA, hB]; norm_num
  have hv1 : -docCenti.qB / (2 * docCenti.qA) < 1 := by rw [hA, hB]; norm_num
  obtain ⟨hr0, hr12, hr1, hset⟩ :=
    docCenti.fixedPts_eq_of_sqrt (docP_hypH _ _ _) hs0 docCenti_discrim hv0 hv1
  have e1 : (-docCenti.qB - 150 * Real.sqrt 105835 / 62500) / (2 * docCenti.qA) =
      23167/41334 - 25 * Real.sqrt 105835 / 20667 := by rw [hA, hB]; ring
  have e2 : (-docCenti.qB + 150 * Real.sqrt 105835 / 62500) / (2 * docCenti.qA) =
      23167/41334 + 25 * Real.sqrt 105835 / 20667 := by rw [hA, hB]; ring
  rw [e1] at hr0 hr12 hset
  rw [e2] at hr12 hr1 hset
  exact ⟨hr0, hr12, hr1, hset⟩

/-- **Proposition 3 at the doc's `δ = 1/1000`, bracketed**: the fixed points are
`{0, p̌, p̂}` with `p̌ ∈ (0.0158, 0.0159)` and `p̂ ∈ (0.9961, 0.9962)`, by sign changes of `Q`
(the doc: "`0, 0.0159, and 0.9961`").
Source: [[two-lesions-doc-2026-09-18]] §4 ("at `δ = 0.001` the fixed points are `0`, `0.0159`,
and `0.9961`")
Kind: N+
Fidelity: exact (bracketing intervals, rule 4; the doc's `0.0159` is the rounding of a root in
`(0.0158, 0.0159)`) -/
theorem prop3_three_at_doc_milli :
    ∃ p₁ p₂ : ℝ, 0 < p₁ ∧ p₁ < p₂ ∧ p₂ < 1 ∧ docMilli.fixedPts = {0, p₁, p₂} ∧
      158/10000 < p₁ ∧ p₁ < 159/10000 ∧ 9961/10000 < p₂ ∧ p₂ < 9962/10000 := by
  have hH := docP_hypH (1/1000 : ℝ) (by norm_num) (by norm_num)
  have hreg : 0 < discrim docMilli.qA docMilli.qB docMilli.qE ∧
      0 < -docMilli.qB / (2 * docMilli.qA) ∧ -docMilli.qB / (2 * docMilli.qA) < 1 := by
    refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [discrim, qA, qB, qE, kappa, kcC, docMilli, docP]
      norm_num
  obtain ⟨p₁, p₂, h0, h12, h1, hset⟩ := (docMilli.prop3_three_iff hH).mpr hreg
  have hmem : ∀ p ∈ docMilli.fixedPts, p = 0 ∨ (0 < p ∧ p < 1 ∧ docMilli.Q p = 0) := by
    intro p hp
    rw [docMilli.prop3_fixedPoints_eq hH] at hp
    simpa using hp
  have hq1 : docMilli.Q p₁ = 0 := by
    rcases hmem p₁ (by rw [hset]; simp) with h | h
    · exact absurd h h0.ne'
    · exact h.2.2
  have hq2 : docMilli.Q p₂ = 0 := by
    rcases hmem p₂ (by rw [hset]; simp) with h | h
    · exact absurd h (by linarith)
    · exact h.2.2
  have hsign := docMilli.Q_sign_pattern h12 hq1 hq2
  have e1 : 0 < docMilli.Q (158/10000) := by
    simp only [Q, qA, qB, qE, kappa, kcC, docMilli, docP]; norm_num
  have e2 : docMilli.Q (159/10000) < 0 := by
    simp only [Q, qA, qB, qE, kappa, kcC, docMilli, docP]; norm_num
  have e3 : docMilli.Q (9961/10000) < 0 := by
    simp only [Q, qA, qB, qE, kappa, kcC, docMilli, docP]; norm_num
  have e4 : 0 < docMilli.Q (9962/10000) := by
    simp only [Q, qA, qB, qE, kappa, kcC, docMilli, docP]; norm_num
  refine ⟨p₁, p₂, h0, h12, h1, hset, ?_, ?_, ?_, ?_⟩
  · rcases (hsign _).2.mp e1 with h | h
    · exact h
    · linarith [((hsign _).1.mp e2).2]
  · exact ((hsign _).1.mp e2).1
  · exact ((hsign _).1.mp e3).2
  · rcases (hsign _).2.mp e4 with h | h
    · linarith [((hsign _).1.mp e3).1]
    · exact h

end DlParams

end Cleanroom.Decision.DpTwoLesions

import Cleanroom.Decision.DpTwoLesions.InteriorReal

/-!
# T6 — Proposition 4, fixed grip: the recency learner abstains

The recency learner's trajectory `p_{t+1} = (1 − η_{t+1}) b_t + η_{t+1}/2`, `b_t ∈ β(p_t)`, with
`η_t → 0` at fixed grip, converges to `0` under (H) — the proof of record replaces the doc's
"`≫`" case analysis: after step `0` every `p_{t+1}` is `η_{t+1}/2` or `1 − η_{t+1}/2`; `Δ`
exceeds `α` on a neighbourhood of each endpoint (`Q` is continuous with `Q(0), Q(1) > 0`), so
for `t` large `b_t = 0` and `p_{t+1} = η_{t+1}/2 → 0`. Rest points at fixed `η`
(`prop4_restPoint_iff`): `1 − η/2` rests iff `Δ(1 − η/2) ≤ α`, `η/2` iff `α ≤ Δ(η/2)`; at the
doc's `δ = 1/100`: `η = 1/5` rests at `9/10`, `η = 1/20` collapses to `1/40`, and the switch
is `η† = 2(1 − p̂) ∈ (0.0919, 0.0920)` exactly (the note's "`≈ 0.095`"), with the rest-point
status of `1 − η/2` monotone in `η`.
Serves [[dp-two-lesions-mandate]] T6 (dp-core-077, 2-009(b)).
-/

namespace Cleanroom.Decision.DpTwoLesions

open Set Filter Topology

namespace DlParams

variable (P : DlParams ℝ)

/-- **The recency learner's trajectory** (doc §5): `p_{t+1} = (1 − η_{t+1}) b_t + η_{t+1}/2` with
`b_t ∈ β(p_t)`.
Source: [[two-lesions-doc-2026-09-18]] §5 ("The recency learner … Its update is …")
Kind: D
Fidelity: exact -/
def IsRecencyTraj (η p : ℕ → ℝ) : Prop :=
  ∀ t, ∃ b ∈ P.bestResp (p t), p (t + 1) = (1 - η (t + 1)) * b + η (t + 1) / 2

/-- **No ties along a trajectory**: `Δ(p_t) ≠ α` for every `t` (the mandate's §3.8 scope; at a
tie `β = [0, 1]` and the dynamics are selection-dependent).
Source: mandate §3.8
Kind: D -/
def NoTie (p : ℕ → ℝ) : Prop := ∀ t, P.Delta (p t) ≠ P.α

/-- At a non-tie the best response is `{0}` or `{1}`. Source: doc §3. Kind: L -/
theorem bestResp_of_ne {p : ℝ} (hne : P.Delta p ≠ P.α) :
    (P.α < P.Delta p ∧ P.bestResp p = {0}) ∨ (P.Delta p < P.α ∧ P.bestResp p = {1}) := by
  rcases lt_or_gt_of_ne hne with h | h
  · right
    refine ⟨h, ?_⟩
    ext b
    unfold bestResp
    simp only [mem_setOf_eq, mem_singleton_iff]
    constructor
    · rintro ⟨hb, -, -, -⟩; exact hb h
    · rintro rfl; exact ⟨fun _ => rfl, fun h' => absurd h' (not_lt.mpr h.le), zero_le_one, le_rfl⟩
  · left
    refine ⟨h, ?_⟩
    ext b
    unfold bestResp
    simp only [mem_setOf_eq, mem_singleton_iff]
    constructor
    · rintro ⟨-, hb, -, -⟩; exact hb h
    · rintro rfl; exact ⟨fun h' => absurd h' (not_lt.mpr h.le), fun _ => rfl, le_rfl, zero_le_one⟩

/-- Members of a best response lie in `[0, 1]`. Source: doc §3. Kind: L -/
theorem bestResp_mem_Icc {p b : ℝ} (hb : b ∈ P.bestResp p) : 0 ≤ b ∧ b ≤ 1 := ⟨hb.2.2.1, hb.2.2.2⟩

/-- **The margin at the endpoints**: under (H) there is `ε₀ > 0` with `α < Δ(p)` for every
`p ∈ [0, 1]` within `ε₀` of `0` or of `1` (continuity of `Q` with `Q(0), Q(1) > 0`).
Source: [[two-lesions-doc-2026-09-18]] §5 Proposition 4 proof ("the penalty is close to
`Cε_L > π`" / "close to `C(1 − ε_L) > π`"), made exact
Kind: L -/
theorem exists_margin (hH : P.HypH) :
    ∃ ε₀ > 0, ∀ p ∈ Icc (0 : ℝ) 1, (p < ε₀ ∨ 1 - ε₀ < p) → P.α < P.Delta p := by
  have h0 : ∀ᶠ p in 𝓝 (0 : ℝ), 0 < P.Q p :=
    P.continuous_Q.continuousAt.eventually (lt_mem_nhds (P.Q_zero_pos hH))
  have h1 : ∀ᶠ p in 𝓝 (1 : ℝ), 0 < P.Q p :=
    P.continuous_Q.continuousAt.eventually (lt_mem_nhds (P.Q_one_pos hH))
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.eventually_nhds_iff.mp h0
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.eventually_nhds_iff.mp h1
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun p hp hcase => ?_⟩
  rw [P.alpha_lt_Delta_iff p hp.1 hp.2]
  rcases hcase with hc | hc
  · apply hb₁
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hp.1]
    exact lt_of_lt_of_le hc (min_le_left _ _)
  · apply hb₂
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hp.2])]
    linarith [min_le_right ε₁ ε₂]

/-- A recency trajectory stays in `[0, 1]` (given `η ∈ [0, 1]` and `p₀ ∈ [0, 1]`).
Source: none: infrastructure
Kind: L -/
theorem recency_mem_Icc {η p : ℕ → ℝ} (hη0 : ∀ t, 0 ≤ η t) (hη1 : ∀ t, η t ≤ 1)
    (htraj : P.IsRecencyTraj η p) (hp0 : 0 ≤ p 0 ∧ p 0 ≤ 1) (t : ℕ) : 0 ≤ p t ∧ p t ≤ 1 := by
  induction t with
  | zero => exact hp0
  | succ t _ =>
    obtain ⟨b, hb, hstep⟩ := htraj t
    obtain ⟨hb0, hb1⟩ := P.bestResp_mem_Icc hb
    rw [hstep]
    constructor
    · nlinarith [hη0 (t + 1), hη1 (t + 1)]
    · nlinarith [hη0 (t + 1), hη1 (t + 1)]

/-- **Proposition 4, fixed grip**: under (H), for a non-tying recency trajectory with `η_t → 0`
(and `η_t ∈ [0, 1]`, `p₀ ∈ [0, 1]`), `p_t → 0`.
Source: [[two-lesions-doc-2026-09-18]] §5 Proposition 4 ("Let `δ` be fixed and `η_t → 0`. Under
(H), `p_t → 0`")
Kind: P
Fidelity: exact for non-tying trajectories (the mandate's scope; the doc's `β` is set-valued
and its sketch ignores ties); the doc's "`≫`" case analysis replaced by the endpoint margin
Hyps: (a) (H); non-tying; `η ∈ [0, 1]` (implicit in "explores with probability `η`") -/
theorem prop4_fixedGrip (hH : P.HypH) {η p : ℕ → ℝ} (hη0 : ∀ t, 0 ≤ η t) (hη1 : ∀ t, η t ≤ 1)
    (hη : Tendsto η atTop (𝓝 0)) (htraj : P.IsRecencyTraj η p) (hp0 : 0 ≤ p 0 ∧ p 0 ≤ 1)
    (hnt : P.NoTie p) : Tendsto p atTop (𝓝 0) := by
  obtain ⟨ε₀, hε₀, hmargin⟩ := P.exists_margin hH
  -- eventually `η t < 2ε₀`
  have hev : ∀ᶠ t in atTop, η t < 2 * ε₀ := hη.eventually (gt_mem_nhds (by linarith))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨T, hT⟩ := hev
  -- for `t ≥ T`, `p (t+1) ∈ {η/2, 1 − η/2}` lies in the margin, so `b_{t+1} = 0`
  have hstep : ∀ t, T ≤ t → p (t + 2) = η (t + 2) / 2 := by
    intro t ht
    obtain ⟨b, hb, hstep⟩ := htraj t
    obtain ⟨b', hb', hstep'⟩ := htraj (t + 1)
    have hmem := P.recency_mem_Icc hη0 hη1 htraj hp0 (t + 1)
    -- `p (t+1)` is in the margin
    have hin : p (t + 1) < ε₀ ∨ 1 - ε₀ < p (t + 1) := by
      rcases P.bestResp_of_ne (hnt t) with ⟨-, h0⟩ | ⟨-, h1⟩
      · rw [h0, mem_singleton_iff] at hb; subst hb
        left; rw [hstep]; linarith [hT (t + 1) (by omega), hη0 (t + 1)]
      · rw [h1, mem_singleton_iff] at hb; subst hb
        right; rw [hstep]; linarith [hT (t + 1) (by omega), hη1 (t + 1)]
    have hgt := hmargin _ hmem hin
    -- so `b' = 0`
    rcases P.bestResp_of_ne (hnt (t + 1)) with ⟨-, h0⟩ | ⟨hlt, -⟩
    · rw [h0, mem_singleton_iff] at hb'; subst hb'
      rw [hstep']; ring
    · exact absurd hgt (not_lt.mpr hlt.le)
  -- conclude: `p =ᶠ η/2`
  have hlim : Tendsto (fun t => η t / 2) atTop (𝓝 0) := by
    have := hη.div_const 2; simpa using this
  refine hlim.congr' ?_
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  refine ⟨T + 2, fun t ht => ?_⟩
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
  exact (hstep s (by omega)).symm

/-! ## Rest points at fixed `η` -/

/-- A rest point of the fixed-`η` recency map: `p = (1 − η) b + η/2` for some `b ∈ β(p)`.
Source: [[two-lesions-doc-2026-09-18]] §5 (the recursion at fixed `η`); dp-core-2-009
Kind: D -/
def IsRecencyRest (η p : ℝ) : Prop := ∃ b ∈ P.bestResp p, p = (1 - η) * b + η / 2

/-- **The rest points of the fixed-`η` recency map**: `1 − η/2` rests iff `Δ(1 − η/2) ≤ α`,
and `η/2` rests iff `α ≤ Δ(η/2)` (for `0 < η < 1`; the ties included, where `β = [0, 1]`).
Source: mandate T6 (`prop4_restPoint_iff`); dp-core-2-009 ("the constants `1 − η/2`, `η/2` are
the doc's own recursion's rest points")
Kind: P
Fidelity: exact (the mandate's strict `<` is `≤` at the tie: a tie is a rest point too)
Hyps: none -/
theorem prop4_restPoint_iff {η : ℝ} (_hη : 0 < η) (hη1 : η < 1) :
    (P.IsRecencyRest η (1 - η / 2) ↔ P.Delta (1 - η / 2) ≤ P.α) ∧
    (P.IsRecencyRest η (η / 2) ↔ P.α ≤ P.Delta (η / 2)) := by
  constructor
  · constructor
    · rintro ⟨b, hb, heq⟩
      have hb1 : b = 1 := by
        have : (1 - η) * b = 1 - η := by linarith
        exact mul_left_cancel₀ (sub_pos.mpr hη1).ne' (by linarith)
      subst hb1
      by_contra hlt
      exact one_ne_zero (hb.2.1 (not_le.mp hlt))
    · intro h
      refine ⟨1, ⟨fun _ => rfl, fun hlt => absurd hlt (not_lt.mpr h), zero_le_one, le_rfl⟩, by ring⟩
  · constructor
    · rintro ⟨b, hb, heq⟩
      have hb0 : b = 0 := by
        have : (1 - η) * b = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left (sub_pos.mpr hη1).ne'
      subst hb0
      by_contra hlt
      exact zero_ne_one (hb.1 (not_le.mp hlt))
    · intro h
      refine ⟨0, ⟨fun hgt => absurd hgt (not_lt.mpr h), fun _ => rfl, le_rfl, zero_le_one⟩, by ring⟩

/-- **At the doc's `δ = 1/100`: `η = 1/5` rests at `9/10`; `η = 1/20` does not rest at `39/40`
and rests at `1/40`** ("collapses to `1/40`") — by the sign of `Q` at those points.
Source: [[iv-design-draw-as-instrument]] §5 ("The recency learner with fixed `η = 0.2` stays at
`1 − η/2 = 0.9`, with `η ≤ 0.05` collapses to `η/2`")
Kind: N+ -/
theorem prop4_rest_at_doc :
    docCenti.IsRecencyRest (1/5) (9/10) ∧ ¬ docCenti.IsRecencyRest (1/20) (39/40) ∧
    docCenti.IsRecencyRest (1/20) (1/40) := by
  have e1 : (9/10 : ℝ) = 1 - (1/5) / 2 := by norm_num
  have e2 : (39/40 : ℝ) = 1 - (1/20) / 2 := by norm_num
  have e3 : (1/40 : ℝ) = (1/20) / 2 := by norm_num
  obtain ⟨hA, hB, hE⟩ := docCenti_coeffs
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, (docCenti.prop4_restPoint_iff (by norm_num) (by norm_num)).1]
    apply le_of_lt
    rw [docCenti.Delta_lt_alpha_iff _ (by norm_num) (by norm_num), Q, hA, hB, hE]
    norm_num
  · rw [e2, (docCenti.prop4_restPoint_iff (by norm_num) (by norm_num)).1, not_le,
      docCenti.alpha_lt_Delta_iff _ (by norm_num) (by norm_num), Q, hA, hB, hE]
    norm_num
  · rw [e3, (docCenti.prop4_restPoint_iff (by norm_num) (by norm_num)).2]
    apply le_of_lt
    rw [docCenti.alpha_lt_Delta_iff _ (by norm_num) (by norm_num), Q, hA, hB, hE]
    norm_num

/-- **The switch `η†` at the doc's `δ = 1/100`, exactly**: for `η ∈ (0, 1)`, `1 − η/2` is a
rest point iff `η ≥ 2(1 − p̂)` where `p̂ = 23167/41334 + 25√105835/20667` — so the status is
monotone in `η` and switches once, at `η† = 2(1 − p̂) ∈ (0.0919, 0.0920)` (the note's first-order
"`≈ 0.095`" is off by `3·10⁻³`).
Source: [[iv-design-draw-as-instrument]] §5 ("the doc's own first-order formula puts the switch
at `η ≈ 0.095`"); mandate §3.6 ("`η† ∈ (0.0919, 0.0920)`")
Kind: P
Fidelity: exact (surds and a bracketing interval, rule 4)
Hyps: none -/
theorem prop4_threshold_at_doc :
    (∀ η : ℝ, 0 < η → η < 1 →
      (docCenti.IsRecencyRest η (1 - η / 2) ↔
        2 * (1 - (23167/41334 + 25 * Real.sqrt 105835 / 20667)) ≤ η)) ∧
    919/10000 < 2 * (1 - (23167/41334 + 25 * Real.sqrt 105835 / 20667)) ∧
    2 * (1 - (23167/41334 + 25 * Real.sqrt 105835 / 20667)) < 920/10000 := by
  obtain ⟨hr0, hr12, hr1, hset⟩ := prop3_three_at_doc_centi
  have hH := docP_hypH (1/100 : ℝ) (by norm_num) (by norm_num)
  have hmem : ∀ p ∈ docCenti.fixedPts, p = 0 ∨ (0 < p ∧ p < 1 ∧ docCenti.Q p = 0) := by
    intro p hp
    rw [docCenti.prop3_fixedPoints_eq hH] at hp
    simpa using hp
  have hq1 : docCenti.Q (23167/41334 - 25 * Real.sqrt 105835 / 20667) = 0 := by
    rcases hmem (23167/41334 - 25 * Real.sqrt 105835 / 20667) (by rw [hset]; simp) with h | h
    · exact absurd h hr0.ne'
    · exact h.2.2
  have hq2 : docCenti.Q (23167/41334 + 25 * Real.sqrt 105835 / 20667) = 0 := by
    rcases hmem (23167/41334 + 25 * Real.sqrt 105835 / 20667) (by rw [hset]; simp) with h | h
    · exact absurd h (by linarith)
    · exact h.2.2
  have hsign := docCenti.Q_sign_pattern hr12 hq1 hq2
  refine ⟨fun η hη hη1 => ?_, ?_, ?_⟩
  · rw [(docCenti.prop4_restPoint_iff hη hη1).1]
    have hmemI : 0 ≤ 1 - η / 2 ∧ 1 - η / 2 ≤ 1 := ⟨by linarith, by linarith⟩
    constructor
    · intro h
      rcases h.lt_or_eq with h | h
      · rw [docCenti.Delta_lt_alpha_iff _ hmemI.1 hmemI.2] at h
        have := ((hsign _).1.mp h).2
        linarith
      · rw [docCenti.Delta_eq_alpha_iff _ hmemI.1 hmemI.2] at h
        -- a root: `1 − η/2 = p̌` or `p̂`; both give `η ≥ 2(1 − p̂)`
        rw [docCenti.Q_factor hr12.ne hq1 hq2] at h
        rcases mul_eq_zero.mp h with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact absurd h'' docCenti.qA_pos.ne'
          · linarith
        · linarith
    · intro h
      rcases h.lt_or_eq with h | h
      · apply le_of_lt
        rw [docCenti.Delta_lt_alpha_iff _ hmemI.1 hmemI.2, (hsign _).1]
        constructor
        · -- `p̌ < 1 − η/2` since `η < 1` and `p̌ < 1/2`
          have : 23167/41334 - 25 * Real.sqrt 105835 / 20667 < 1/2 := by
            have := sqrt_105835_bounds.1; norm_num; nlinarith
          linarith
        · linarith
      · apply le_of_eq
        rw [docCenti.Delta_eq_alpha_iff _ hmemI.1 hmemI.2]
        have : 1 - η / 2 = 23167/41334 + 25 * Real.sqrt 105835 / 20667 := by linarith
        rw [this]; exact hq2
  · have : Real.sqrt 105835 < 32535/100 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
    linarith
  · have : 32532/100 < Real.sqrt 105835 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
    linarith

end DlParams

end Cleanroom.Decision.DpTwoLesions

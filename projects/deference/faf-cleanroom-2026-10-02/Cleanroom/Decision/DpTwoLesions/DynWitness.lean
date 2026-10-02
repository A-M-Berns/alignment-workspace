import Cleanroom.Decision.DpTwoLesions.Cumulative
import Cleanroom.Decision.DpTwoLesions.Recency

/-!
# Trajectory witnesses for the dynamics headlines (repair round 1)

Audit r1 (fidelity N6, adversarial N5) asked for Lean-instantiated trajectories inhabiting the
full hypothesis packages of the dynamics theorems, in place of the parameter instances named
in the ledger. Each witness is an explicit non-constant trajectory on a doc instance, with the
headline applied to it:

* `prop5_strong_at_doc_deci` — at `δ = 1/10` (unique fixed point `0`), the cumulative trajectory
  `x_t = 1/(t+1)` from `x₀ = 1` (`b ≡ 0`), converging to `0` by `prop5_strong`.
* `prop5_weak_below_at_doc` — at `δ = 1/100`, the trajectory `x_t = (1/10)/(t+1)` from
  `x₀ = 1/10 < p̌` (`b ≡ 0`), converging to `0` by `prop5_weak_below`.
* `prop4_fixedGrip_at_doc` — at `δ = 1/100`, the recency trajectory with `η_t = 1/(t+20)` from
  `p₀ = ½ ∈ (p̌, p̂)`: it first climbs to `p₁ = 1 − η₁/2 = 41/42 > p̂`, then collapses to
  `p₂ = η₂/2 = 1/44 < p̌` and follows `p_t = η_t/2 → 0` (`prop4_fixedGrip`); non-tying
  throughout (`Q ≠ 0` at every visited point).

(`prop5_weak_between`'s witness is `prop5_weak_between_at_doc` in `Cumulative.lean`.)
Serves [[dp-two-lesions-mandate]] T6, T8 (witnesses).
-/

namespace Cleanroom.Decision.DpTwoLesions

open Set Filter Topology

namespace DlParams

/-- The two interior fixed points at `δ = 1/100` are zeros of `Q`. Source: none: infrastructure.
Kind: L -/
theorem docCenti_Q_roots :
    docCenti.Q (23167/41334 - 25 * Real.sqrt 105835 / 20667) = 0 ∧
    docCenti.Q (23167/41334 + 25 * Real.sqrt 105835 / 20667) = 0 := by
  obtain ⟨hr0, hr12, hr1, hset⟩ := prop3_three_at_doc_centi
  have hH := docP_hypH (1/100 : ℝ) (by norm_num) (by norm_num)
  have hmem : ∀ p ∈ docCenti.fixedPts, p = 0 ∨ (0 < p ∧ p < 1 ∧ docCenti.Q p = 0) := by
    intro p hp
    rw [docCenti.prop3_fixedPoints_eq hH] at hp
    simpa using hp
  constructor
  · rcases hmem (23167/41334 - 25 * Real.sqrt 105835 / 20667) (by rw [hset]; simp) with h | h
    · exact absurd h hr0.ne'
    · exact h.2.2
  · rcases hmem (23167/41334 + 25 * Real.sqrt 105835 / 20667) (by rw [hset]; simp) with h | h
    · exact absurd h (by linarith)
    · exact h.2.2

/-- **`prop5_strong`'s witness** at the doc's `δ = 1/10`: the cumulative trajectory
`x_t = 1/(t+1)` from `x₀ = 1` takes `b ≡ 0` (`Q > 0` everywhere) and converges to `0`.
Source: [[two-lesions-doc-2026-09-18]] §5 Proposition 5 ("if `δ > δ*`, then `p̄_t → 0` from every
initial policy"), at `δ = 1/10`
Kind: N+ (a non-constant trajectory from the smoke label)
Fidelity: exact -/
theorem prop5_strong_at_doc_deci :
    ∃ x : ℕ → ℝ, docDeci.IsCumulTraj x ∧ x 0 = 1 ∧ (∀ t, x t = 1 / ((t : ℝ) + 1)) ∧
      Tendsto x atTop (𝓝 0) := by
  have hQ : ∀ p ∈ Icc (0 : ℝ) 1, 0 < docDeci.Q p :=
    fun p _ => docDeci.Q_pos_of_discrim_neg docDeci_discrim_neg p
  let x : ℕ → ℝ := fun t => 1 / ((t : ℝ) + 1)
  have hx : ∀ t, x t = 1 / ((t : ℝ) + 1) := fun t => rfl
  have hmem : ∀ t, 0 ≤ x t ∧ x t ≤ 1 := by
    intro t; rw [hx]
    have : (1 : ℝ) ≤ t + 1 := by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
    exact ⟨by positivity, by rw [div_le_one (by positivity)]; exact this⟩
  have htraj : docDeci.IsCumulTraj x := by
    intro t
    refine ⟨0, ?_, ?_⟩
    · have hgt : docDeci.α < docDeci.Delta (x t) :=
        (docDeci.alpha_lt_Delta_iff _ (hmem t).1 (hmem t).2).mpr (hQ _ (hmem t))
      exact ⟨fun h => absurd h (not_lt.mpr hgt.le), fun _ => rfl, le_rfl, zero_le_one⟩
    · rw [hx, hx, cumulStep]
      push_cast
      have h1 : ((t : ℝ) + 1) ≠ 0 := by positivity
      have h2 : ((t : ℝ) + 2) ≠ 0 := by positivity
      have h3 : ((t : ℝ) + 1 + 1) ≠ 0 := by positivity
      field_simp
      ring
  exact ⟨x, htraj, by rw [hx]; norm_num, hx, docDeci.prop5_strong hQ htraj (hmem 0)⟩

/-- **`prop5_weak_below`'s witness** at the doc's `δ = 1/100`: the cumulative trajectory
`x_t = (1/10)/(t+1)` from `x₀ = 1/10 < p̌` takes `b ≡ 0` and converges to `0`.
Source: [[two-lesions-doc-2026-09-18]] §5 Proposition 5 ("`p̄_t → 0` when `p̄₀ < p̌`"), at
`δ = 1/100`
Kind: N+ (a non-constant trajectory in the basin of `0`)
Fidelity: exact -/
theorem prop5_weak_below_at_doc :
    ∃ x : ℕ → ℝ, docCenti.IsCumulTraj x ∧ x 0 = 1/10 ∧
      1/10 < 23167/41334 - 25 * Real.sqrt 105835 / 20667 ∧ Tendsto x atTop (𝓝 0) := by
  obtain ⟨hr0, hr12, hr1, hset⟩ := prop3_three_at_doc_centi
  obtain ⟨hq1, hq2⟩ := docCenti_Q_roots
  have hsign := docCenti.Q_sign_pattern hr12 hq1 hq2
  have hs := sqrt_105835_bounds
  have hlt : (1/10 : ℝ) < 23167/41334 - 25 * Real.sqrt 105835 / 20667 := by linarith [hs.2]
  let x : ℕ → ℝ := fun t => (1/10) / ((t : ℝ) + 1)
  have hx : ∀ t, x t = (1/10) / ((t : ℝ) + 1) := fun t => rfl
  have hmem : ∀ t, 0 < x t ∧ x t ≤ 1/10 := by
    intro t; rw [hx]
    have : (1 : ℝ) ≤ t + 1 := by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
    constructor
    · positivity
    · rw [div_le_iff₀ (by positivity)]; nlinarith
  have htraj : docCenti.IsCumulTraj x := by
    intro t
    refine ⟨0, ?_, ?_⟩
    · have hQ : 0 < docCenti.Q (x t) := (hsign _).2.mpr (Or.inl (by linarith [(hmem t).2]))
      have hgt : docCenti.α < docCenti.Delta (x t) :=
        (docCenti.alpha_lt_Delta_iff _ (hmem t).1.le (by linarith [(hmem t).2])).mpr hQ
      exact ⟨fun h => absurd h (not_lt.mpr hgt.le), fun _ => rfl, le_rfl, zero_le_one⟩
    · rw [hx, hx, cumulStep]
      push_cast
      have h1 : ((t : ℝ) + 1) ≠ 0 := by positivity
      have h2 : ((t : ℝ) + 2) ≠ 0 := by positivity
      have h3 : ((t : ℝ) + 1 + 1) ≠ 0 := by positivity
      field_simp
      ring
  have hx0 : x 0 = 1/10 := by rw [hx]; norm_num
  refine ⟨x, htraj, hx0, hlt, ?_⟩
  exact docCenti.prop5_weak_below hr0 hr12 hr1 hq1 hq2 htraj (by rw [hx0]; norm_num)
    (by rw [hx0]; exact hlt)

/-- **`prop4_fixedGrip`'s witness** at the doc's `δ = 1/100`: with `η_t = 1/(t+20)` the recency
trajectory from `p₀ = ½ ∈ (p̌, p̂)` climbs to `p₁ = 1 − η₁/2 = 41/42 > p̂` (best response `1`),
collapses to `p₂ = η₂/2 = 1/44 < p̌` (best response `0`) and follows `p_t = η_t/2 → 0`; it
never ties.
Source: [[two-lesions-doc-2026-09-18]] §5 Proposition 4 ("Let `δ` be fixed and `η_t → 0`. Under
(H), `p_t → 0`"), at `δ = 1/100`
Kind: N+ (a trajectory that visits both best responses before collapsing)
Fidelity: exact -/
theorem prop4_fixedGrip_at_doc :
    ∃ η p : ℕ → ℝ, (∀ t, η t = 1 / ((t : ℝ) + 20)) ∧ p 0 = 1/2 ∧ p 1 = 41/42 ∧ p 2 = 1/44 ∧
      docCenti.IsRecencyTraj η p ∧ docCenti.NoTie p ∧
      Tendsto η atTop (𝓝 0) ∧ Tendsto p atTop (𝓝 0) := by
  obtain ⟨hr0, hr12, hr1, hset⟩ := prop3_three_at_doc_centi
  obtain ⟨hq1, hq2⟩ := docCenti_Q_roots
  have hsign := docCenti.Q_sign_pattern hr12 hq1 hq2
  have hs := sqrt_105835_bounds
  let η : ℕ → ℝ := fun t => 1 / ((t : ℝ) + 20)
  let p : ℕ → ℝ := fun t => match t with
    | 0 => 1/2
    | 1 => 41/42
    | t + 2 => 1 / (2 * ((t : ℝ) + 22))
  have hη : ∀ t, η t = 1 / ((t : ℝ) + 20) := fun t => rfl
  have hp0 : p 0 = 1/2 := rfl
  have hp1 : p 1 = 41/42 := rfl
  have hp2 : ∀ t, p (t + 2) = 1 / (2 * ((t : ℝ) + 22)) := fun t => rfl
  -- the signs of `Q` at the visited points
  have e0 : docCenti.Q (1/2) < 0 := by
    simp only [Q, qA, qB, qE, kappa, kcC, docCenti, docP]; norm_num
  have e1 : 0 < docCenti.Q (41/42) := (hsign _).2.mpr (Or.inr (by linarith [hs.2]))
  have hp2mem : ∀ t, 0 < p (t + 2) ∧ p (t + 2) ≤ 1/44 := by
    intro t
    rw [hp2]
    have : (22 : ℝ) ≤ t + 22 := by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
    constructor
    · positivity
    · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have e2 : ∀ t, 0 < docCenti.Q (p (t + 2)) := fun t =>
    (hsign _).2.mpr (Or.inl (by have := (hp2mem t).2; linarith [hs.2]))
  have hη0 : ∀ t, 0 ≤ η t := fun t => by rw [hη]; positivity
  have hη1 : ∀ t, η t ≤ 1 := fun t => by
    rw [hη, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
  have htraj : docCenti.IsRecencyTraj η p := by
    intro t
    match t with
    | 0 =>
      refine ⟨1, ?_, ?_⟩
      · have hlt : docCenti.Delta (p 0) < docCenti.α := by
          rw [hp0, docCenti.Delta_lt_alpha_iff _ (by norm_num) (by norm_num)]; exact e0
        exact ⟨fun _ => rfl, fun h => absurd h (not_lt.mpr hlt.le), zero_le_one, le_rfl⟩
      · rw [hp1, hη]; push_cast; norm_num
    | 1 =>
      refine ⟨0, ?_, ?_⟩
      · have hgt : docCenti.α < docCenti.Delta (p 1) := by
          rw [hp1, docCenti.alpha_lt_Delta_iff _ (by norm_num) (by norm_num)]; exact e1
        exact ⟨fun h => absurd h (not_lt.mpr hgt.le), fun _ => rfl, le_rfl, zero_le_one⟩
      · rw [hp2 0, hη]; push_cast; norm_num
    | t + 2 =>
      refine ⟨0, ?_, ?_⟩
      · have hmem := hp2mem t
        have hgt : docCenti.α < docCenti.Delta (p (t + 2)) :=
          (docCenti.alpha_lt_Delta_iff _ hmem.1.le (by linarith [hmem.2])).mpr (e2 t)
        exact ⟨fun h => absurd h (not_lt.mpr hgt.le), fun _ => rfl, le_rfl, zero_le_one⟩
      · show p ((t + 1) + 2) = (1 - η ((t + 1) + 2)) * 0 + η ((t + 1) + 2) / 2
        rw [hp2 (t + 1), hη]
        push_cast
        have h1 : ((t : ℝ) + 1 + 22) ≠ 0 := by positivity
        have h2 : ((t : ℝ) + 1 + 2 + 20) ≠ 0 := by positivity
        field_simp
        ring
  have hnt : docCenti.NoTie p := by
    intro t
    match t with
    | 0 => rw [hp0, Ne, docCenti.Delta_eq_alpha_iff _ (by norm_num) (by norm_num)]; exact e0.ne
    | 1 => rw [hp1, Ne, docCenti.Delta_eq_alpha_iff _ (by norm_num) (by norm_num)]; exact e1.ne'
    | t + 2 =>
      have hmem := hp2mem t
      rw [Ne, docCenti.Delta_eq_alpha_iff _ hmem.1.le (by linarith [hmem.2])]
      exact (e2 t).ne'
  have hηlim : Tendsto η atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h := h0.comp (tendsto_add_atTop_nat 19)
    refine h.congr fun t => ?_
    simp only [Function.comp, hη]
    push_cast
    ring
  refine ⟨η, p, hη, hp0, hp1, by rw [hp2 0]; norm_num, htraj, hnt, hηlim, ?_⟩
  exact docCenti.prop4_fixedGrip (docP_hypH _ _ _) hη0 hη1 hηlim htraj
    ⟨by rw [hp0]; norm_num, by rw [hp0]; norm_num⟩ hnt

end DlParams

end Cleanroom.Decision.DpTwoLesions

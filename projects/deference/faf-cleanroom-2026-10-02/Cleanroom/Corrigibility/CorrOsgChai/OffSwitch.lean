import Cleanroom.Found.CorrThreeStep.OffSwitch
import Cleanroom.Found.CorrThreeStep.Identities
import Cleanroom.Corrigibility.CorrOsgChai.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# The off-switch game over `corr-three-step`'s `osgDelta`: HM 2017 Theorem 1, Corollary 1,
the chance node, and Wängberg's Proposition 4 (T1–T4)

Package `corr-osg-chai`. Nothing here redefines the game: the incentive is `corr-three-step`'s
`osgDelta μ U πH = E_μ[πH · U] − max(E_μ[U], 0)` on FAF's `Distr`, with `πH : Ω → ℝ` a function
of the world (the paper's `π^H(U_a)` is the special case `πH ω = g (U ω)`).

* **T1** `osgDelta_eq_min`: Eq. 1's two forms agree for every `μ, U, πH` — no `[0,1]` bound on
  `πH` is needed (it is linearity plus `max`).
* **T2** `osgDelta_rational_eq`, `osgDelta_rational_nonneg`, `osgDelta_rational_pos_iff`:
  Hadfield-Menell Theorem 1 with the rational human `rationalAllow U = 𝟙[U ≥ 0]` (Eq. 2, the
  convention `π^H(0) = 1`), *derived* from Wängberg's Theorem 9 (`expect_allow_eq_stats`) at
  `p_r⁺ = p_r⁻ = 1` through the identity `rationalAllow U = OSG.allowProb U 1 1`. Strictness
  needs strictly positive mass on `{U > 0}` and on `{U < 0}` (the paper's `Pr(U_a ≤ 0)` in
  Eq. 3 is harmless: mass at `U = 0` contributes to neither term; finding F-1).
* **T3** Corollary 1 on a Dirac belief `Distr.delta u₀`: the closed form (`osgDelta_delta`) —
  **with the branches the other way round from the printed Eq. 4** (finding F-2: at `U < 0`
  the Dirac incentive is `U · π`, at `U ≥ 0` it is `−U (1 − π)`; the printed association gives
  `Δ = −U > 0` at `U < 0, π = 0`, where `w(a)` and `s` both pay `0`); the per-point iff
  (`osgDelta_delta_nonneg_iff`, no `[0,1]` bound needed); the function-level "iff H is
  rational" (`forall_osgDelta_delta_nonneg_iff`), which is what Corollary 1 states and whose
  proof gives only the per-point form (finding F-3). The chance node (`osgDelta_const_le`,
  `osgDelta_const_eq_zero_iff`): a fixed press probability never helps (`Δ ≤ 0`), and `Δ = 0`
  iff (`E[U] > 0 → p = 1`) and (`E[U] < 0 → p = 0`). The paper (l. 76) states the necessary
  condition — `Δ = 0` only when `p ∈ {0, 1}` or `E[U] = 0` — which is the `→` half; the
  mandate's iff "`p ∈ {0, 1} ∨ E[U] = 0`" is false (finding F-15; audit r1 N3).
* **T4** Wängberg's Proposition 4 in this carrier is the equation `pRationalAllow U p =
  OSG.allowProb U p p` (kind T); the new statement is `osgDelta_allowProb_nonneg_iff`: the
  two-type human's `Δ ≥ 0` in the five statistics — Corollary 10's `(4) ≤ 0` *and* the
  `s`-comparison `0 ≤ E[U | w(a)]` that Corollary 10 omits.

Sources: `04-chai/hadfield-menell-2017-the-off-switch-game.md` l. 84–102 (Eq. 1, chance node,
Theorem 1), l. 96 (Eq. 2), l. 166–168 (Corollary 1, Eq. 4);
`04-chai/wangberg-2017-…md` l. 110–120 (Defs 2–3, Prop. 4).
-/

namespace Cleanroom.Corrigibility.CorrOsgChai

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
  Cleanroom.Found.CorrThreeStep.OSG
open Finset hiding expect

set_option linter.unusedSectionVars false

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## D1: the rational human, the `p`-rational human, Dirac beliefs -/

/-- **The rational human** (Hadfield-Menell et al. 2017 Eq. 2): allows `a` iff `U_a ≥ 0`, with the
paper's convention `π^H(0) = 1`. Ties at `U = 0` allowed.
Source: Hadfield-Menell et al. 2017 Eq. 2 (l. 96)
Kind: D
Fidelity: exact -/
noncomputable def rationalAllow (U : Ω → ℝ) : Ω → ℝ := fun ω => if 0 ≤ U ω then 1 else 0

/-- **The `p`-rational human** (Wängberg et al. 2017 Def. 3): picks the optimum with probability
`p`, so allows `a` with probability `p` when `U ≥ 0` and `1 − p` when `U < 0`.
Source: Wängberg et al. 2017 Def. 3 (l. 112)
Kind: D
Fidelity: exact (two-action menu) -/
noncomputable def pRationalAllow (U : Ω → ℝ) (p : ℝ) : Ω → ℝ :=
  fun ω => if 0 ≤ U ω then p else 1 - p

/-- The rational human is Wängberg's two-type human at `p_r⁺ = p_r⁻ = 1`. This is the identity
that makes Theorem 1 a corollary of Wängberg's Theorem 9.
Source: Hadfield-Menell et al. 2017 Eq. 2; Wängberg et al. 2017 §3.3
Kind: L
Fidelity: exact -/
lemma rationalAllow_eq_allowProb (U : Ω → ℝ) : rationalAllow U = allowProb U 1 1 := by
  funext ω; simp [rationalAllow, allowProb]

/-- **Wängberg Proposition 4 in this carrier** (T4): the `p`-rational human *is* the two-type
human with `p_r⁺ = p_r⁻ = p`. On a two-action menu the Harsanyi representation of a stochastic
decision as a random rational type is exhausted by this equation.
Source: Wängberg et al. 2017 Prop. 4 (l. 116–120)
Kind: T
Fidelity: exact (two-action menu; the proposition's content on that menu is this equation) -/
lemma pRationalAllow_eq_allowProb (U : Ω → ℝ) (p : ℝ) : pRationalAllow U p = allowProb U p p := rfl

/-! ## T1: Eq. 1's two forms -/

/-- **Eq. 1, the two forms agree** for every prior, every `U` and every `πH : Ω → ℝ` — no `[0,1]`
bound on `πH` is needed, it is linearity of `expect` plus a case split on the sign of `E[U]`.
Source: Hadfield-Menell et al. 2017 Eq. 1 (l. 88, "a little manipulation shows")
Kind: L
Fidelity: exact (stronger: no bound on `πH`)
Hyps: (a) none -/
theorem osgDelta_eq_min (μ : Distr Ω) (U πH : Ω → ℝ) :
    osgDelta μ U πH =
      min (expect μ (fun ω => -U ω * (1 - πH ω))) (expect μ (fun ω => U ω * πH ω)) := by
  have h1 : expect μ (fun ω => -U ω * (1 - πH ω)) =
      expect μ (fun ω => πH ω * U ω) - expect μ U := by
    rw [← expect_sub]; congr 1; funext ω; ring
  have h2 : expect μ (fun ω => U ω * πH ω) = expect μ (fun ω => πH ω * U ω) := by
    congr 1; funext ω; ring
  rw [osgDelta, h1, h2]
  rcases le_total (expect μ U) 0 with hE | hE
  · rw [max_eq_right hE, min_eq_right (by linarith), sub_zero]
  · rw [max_eq_left hE, min_eq_left (by linarith)]

/-- Eq. 1 in the paper's shape `π^H(U_a)`: the special case `πH ω = g (U ω)`.
Source: Hadfield-Menell et al. 2017 Eq. 1
Kind: L
Fidelity: exact -/
theorem osgDelta_comp_eq_min (μ : Distr Ω) (U : Ω → ℝ) (g : ℝ → ℝ) :
    osgDelta μ U (fun ω => g (U ω)) =
      min (expect μ (fun ω => -U ω * (1 - g (U ω)))) (expect μ (fun ω => U ω * g (U ω))) :=
  osgDelta_eq_min μ U _

/-! ## T2: Hadfield-Menell Theorem 1, derived from Wängberg's Theorem 9 -/

/-- `E[U 1_{U ≥ 0}] ≥ 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma posSum_nonneg (μ : Distr Ω) (U : Ω → ℝ) : 0 ≤ posSum μ U :=
  sum_nonneg fun ω hω => mul_nonneg (μ.nonneg ω) (mem_filter.mp hω).2

/-- `E[U 1_{U < 0}] ≤ 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma negSum_nonpos (μ : Distr Ω) (U : Ω → ℝ) : negSum μ U ≤ 0 :=
  sum_nonpos fun ω hω => mul_nonpos_of_nonneg_of_nonpos (μ.nonneg ω) (mem_filter.mp hω).2.le

/-- `E[U] = E[U 1_{U ≥ 0}] + E[U 1_{U < 0}]` (Theorem 9's first form, denominator-free).
Source: Wängberg et al. 2017 Theorem 9 (via `expect_eq_stats`). Kind: L. Fidelity: n/a -/
lemma expect_eq_posSum_add_negSum (μ : Distr Ω) (U : Ω → ℝ) :
    expect μ U = posSum μ U + negSum μ U := by
  rw [expect_eq_stats, posMass_mul_ePlus, negMass_mul_eMinus]

/-- Under the rational human, `E[π^H U] = E[U 1_{U ≥ 0}]`: Theorem 9's second form at
`p_r⁺ = p_r⁻ = 1`.
Source: Wängberg et al. 2017 Theorem 9 at `p_r = 1` (the extension corr-refs-031 flags)
Kind: L
Fidelity: exact -/
lemma expect_rationalAllow_mul (μ : Distr Ω) (U : Ω → ℝ) :
    expect μ (fun ω => rationalAllow U ω * U ω) = posSum μ U := by
  rw [rationalAllow_eq_allowProb, expect_allow_eq_stats, sub_self, mul_zero, zero_mul, add_zero,
    mul_one, posMass_mul_ePlus]

/-- **Theorem 1, the closed form.** With the rational human, Eq. 1's incentive is
`min(E[U 1_{U ≥ 0}], −E[U 1_{U < 0}]) = min(E[U_a | U_a > 0] Pr(U_a > 0), E[−U_a | U_a < 0] Pr(U_a < 0))`
(the paper's Eq. 3, denominator-free; mass at `U = 0` contributes to neither term).
Source: Hadfield-Menell et al. 2017 Theorem 1 Eq. 3 (l. 88)
Kind: C (Wängberg Theorem 9 at `p_r = 1` chained with the `min` form of Eq. 1)
Fidelity: exact
Hyps: (a) none -/
theorem osgDelta_rational_eq (μ : Distr Ω) (U : Ω → ℝ) :
    osgDelta μ U (rationalAllow U) = min (posSum μ U) (-negSum μ U) := by
  rw [osgDelta, expect_rationalAllow_mul, expect_eq_posSum_add_negSum]
  have hp := posSum_nonneg μ U
  have hn := negSum_nonpos μ U
  rcases le_total 0 (posSum μ U + negSum μ U) with hE | hE
  · rw [max_eq_left hE, min_eq_right (by linarith)]; ring
  · rw [max_eq_right hE, min_eq_left (by linarith), sub_zero]

/-- **Theorem 1, clause 1.** With the rational human, `Δ ≥ 0`: `w(a)` is never suboptimal.
Regime-free: no sign assumption on `E[U]`.
Source: Hadfield-Menell et al. 2017 Theorem 1 clause 1 (l. 88)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem osgDelta_rational_nonneg (μ : Distr Ω) (U : Ω → ℝ) :
    0 ≤ osgDelta μ U (rationalAllow U) := by
  rw [osgDelta_rational_eq]
  exact le_min (posSum_nonneg μ U) (by linarith [negSum_nonpos μ U])

/-- `E[U 1_{U ≥ 0}] > 0` iff some world of positive mass has `U > 0`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma posSum_pos_iff (μ : Distr Ω) (U : Ω → ℝ) :
    0 < posSum μ U ↔ ∃ ω, 0 < μ.mass ω ∧ 0 < U ω := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    refine absurd h (not_lt.mpr (sum_nonpos fun ω hω => ?_))
    rcases (μ.nonneg ω).lt_or_eq with hμ | hμ
    · have := hne ω hμ; nlinarith
    · rw [← hμ, zero_mul]
  · rintro ⟨ω, hμ, hU⟩
    refine lt_of_lt_of_le (mul_pos hμ hU) (single_le_sum (fun ω' hω' =>
      mul_nonneg (μ.nonneg ω') (mem_filter.mp hω').2) (mem_filter.mpr ⟨mem_univ ω, hU.le⟩))

/-- `E[U 1_{U < 0}] < 0` iff some world of positive mass has `U < 0`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma negSum_neg_iff (μ : Distr Ω) (U : Ω → ℝ) :
    negSum μ U < 0 ↔ ∃ ω, 0 < μ.mass ω ∧ U ω < 0 := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    refine absurd h (not_lt.mpr (sum_nonneg fun ω hω => ?_))
    rcases (μ.nonneg ω).lt_or_eq with hμ | hμ
    · have := hne ω hμ; nlinarith
    · rw [← hμ, zero_mul]
  · rintro ⟨ω, hμ, hU⟩
    have h1 : -(μ.mass ω * U ω) ≤ ∑ ω' ∈ univ.filter (fun ω => U ω < 0), -(μ.mass ω' * U ω') :=
      single_le_sum (f := fun ω' => -(μ.mass ω' * U ω')) (fun ω' hω' =>
        neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (μ.nonneg ω') (mem_filter.mp hω').2.le))
        (mem_filter.mpr ⟨mem_univ ω, hU⟩)
    rw [sum_neg_distrib] at h1
    unfold negSum
    nlinarith [mul_neg_of_pos_of_neg hμ hU]

/-- **Theorem 1, clause 2, as an iff.** With the rational human, `Δ > 0` iff the belief puts
positive mass on `{U > 0}` *and* on `{U < 0}` — strictly on both sides (the paper's clause 2
writes `U_a > 0` and `U_a < 0`, its Eq. 3 writes `Pr(U_a ≤ 0)`; with `π^H(0) = 1` the mass at
`0` contributes nothing, so strict mass on each side is the exact condition: finding F-1).
Source: Hadfield-Menell et al. 2017 Theorem 1 clause 2 (l. 100)
Kind: C
Fidelity: stronger: the paper states `⇐`; this is `↔`
Hyps: (a) none -/
theorem osgDelta_rational_pos_iff (μ : Distr Ω) (U : Ω → ℝ) :
    0 < osgDelta μ U (rationalAllow U) ↔
      (∃ ω, 0 < μ.mass ω ∧ 0 < U ω) ∧ (∃ ω, 0 < μ.mass ω ∧ U ω < 0) := by
  rw [osgDelta_rational_eq, lt_min_iff, posSum_pos_iff, neg_pos, negSum_neg_iff]

/-! ## T3: Corollary 1 on a Dirac belief, and the chance node -/

/-- **Corollary 1's closed form (Eq. 4, corrected).** On the Dirac belief at `u₀`,
`Δ = U(u₀) π^H(u₀)` when `U(u₀) < 0` and `Δ = −U(u₀) (1 − π^H(u₀))` when `U(u₀) ≥ 0`. The
printed Eq. 4 (l. 166 of the extraction) associates the branches the other way; that
association gives `Δ = −U(u₀) > 0` at `U(u₀) < 0, π^H = 0`, where `w(a)` and `s` both pay `0`
(finding F-2).
Source: Hadfield-Menell et al. 2017 Corollary 1, Eq. 4 (l. 166), corrected
Kind: L
Fidelity: variant: branches swapped relative to the printed Eq. 4 (the printed form is false)
Hyps: (a) none -/
theorem osgDelta_delta (u₀ : Ω) (U πH : Ω → ℝ) :
    osgDelta (Distr.delta u₀) U πH =
      if U u₀ < 0 then U u₀ * πH u₀ else -U u₀ * (1 - πH u₀) := by
  rw [osgDelta, expect_delta, expect_delta]
  split_ifs with h
  · rw [max_eq_right h.le]; ring
  · rw [max_eq_left (not_lt.mp h)]; ring

/-- **Corollary 1, per point.** On the Dirac belief at `u₀`, `Δ ≥ 0` iff (`U(u₀) < 0` forces
`π^H(u₀) ≤ 0`) and (`U(u₀) > 0` forces `π^H(u₀) ≥ 1`); at `U(u₀) = 0` anything goes. No
`[0,1]` bound on `π^H` is needed for this form.
Source: Hadfield-Menell et al. 2017 Corollary 1 (l. 166–168; the proof sketch's content)
Kind: L
Fidelity: exact (this is what the proof establishes; see `forall_osgDelta_delta_nonneg_iff`)
Hyps: (a) none -/
theorem osgDelta_delta_nonneg_iff (u₀ : Ω) (U πH : Ω → ℝ) :
    0 ≤ osgDelta (Distr.delta u₀) U πH ↔
      (U u₀ < 0 → πH u₀ ≤ 0) ∧ (0 < U u₀ → 1 ≤ πH u₀) := by
  rw [osgDelta_delta]
  split_ifs with h
  · constructor
    · intro hΔ
      refine ⟨fun _ => ?_, fun h' => absurd h' (not_lt.mpr h.le)⟩
      by_contra hπ; push Not at hπ
      nlinarith [mul_neg_of_neg_of_pos h hπ]
    · rintro ⟨h1, -⟩
      exact mul_nonneg_of_nonpos_of_nonpos h.le (h1 h)
  · push Not at h
    rcases h.lt_or_eq with h | h
    · constructor
      · intro hΔ
        refine ⟨fun h' => absurd h' (not_lt.mpr h.le), fun _ => ?_⟩
        by_contra hπ; push Not at hπ
        nlinarith [mul_pos h (sub_pos.mpr hπ)]
      · rintro ⟨-, h2⟩
        have := h2 h
        nlinarith
    · rw [← h]; simp

/-- **Corollary 1, function level ("`w(a)` is optimal iff H is rational").** The paper's
statement quantifies over the human's policy as a function while the belief fixes one `u₀`; the
only reading under which "iff H is rational" is a statement about `π^H` as a function is: `Δ ≥ 0`
under *every* Dirac belief iff `π^H` agrees with the rational policy wherever `U ≠ 0`. This is
that statement; it needs `π^H ∈ [0,1]`, and the paper's proof sketch gives only the per-point
form (`osgDelta_delta_nonneg_iff`; finding F-3). At `U = 0` the policy is unconstrained
(`rationalAllow` says `1` there by convention).
Source: Hadfield-Menell et al. 2017 Corollary 1 (l. 166)
Kind: L
Fidelity: variant: function-level reading of the "iff"; `U ≠ 0` clause made explicit
Hyps: (a) `hπ : πH ∈ [0,1]` pointwise (the paper's type of `π^H`) -/
theorem forall_osgDelta_delta_nonneg_iff (U πH : Ω → ℝ) (hπ : ∀ ω, πH ω ∈ Set.Icc (0 : ℝ) 1) :
    (∀ u₀, 0 ≤ osgDelta (Distr.delta u₀) U πH) ↔
      ∀ ω, U ω ≠ 0 → πH ω = rationalAllow U ω := by
  simp only [osgDelta_delta_nonneg_iff]
  constructor
  · intro h ω hU
    rcases lt_or_gt_of_ne hU with hU | hU
    · simp only [rationalAllow, if_neg (not_le.mpr hU)]
      exact le_antisymm ((h ω).1 hU) (hπ ω).1
    · simp only [rationalAllow, if_pos hU.le]
      exact le_antisymm (hπ ω).2 ((h ω).2 hU)
  · intro h ω
    refine ⟨fun hU => ?_, fun hU => ?_⟩
    · rw [h ω hU.ne, rationalAllow, if_neg (not_le.mpr hU)]
    · rw [h ω hU.ne', rationalAllow, if_pos hU.le]

/-- **The chance node (l. 84): a constant press probability never helps.** If the human is a
coin, `π^H ≡ p ∈ [0,1]`, then `Δ = p E[U] − max(E[U], 0) ≤ 0`: `w(a)` is weakly dominated by
the better of `a` and `s`.
Source: Hadfield-Menell et al. 2017 §3 (l. 84–86, "if H is a chance node …")
Kind: L
Fidelity: exact
Hyps: (a) `hp : p ∈ [0,1]` -/
theorem osgDelta_const_le (μ : Distr Ω) (U : Ω → ℝ) {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    osgDelta μ U (fun _ => p) ≤ 0 := by
  rw [osgDelta, expect_const_mul]
  rcases le_total 0 (expect μ U) with hE | hE
  · rw [max_eq_left hE]; nlinarith [hp.2]
  · rw [max_eq_right hE]; nlinarith [hp.1]

/-- **The chance node, the equality case.** With `π^H ≡ p`, `Δ = 0` iff (`E[U] > 0` forces
`p = 1`) and (`E[U] < 0` forces `p = 0`); at `E[U] = 0` every `p` gives `Δ = 0`. The paper
(l. 76) states the necessary condition — `max{Ua, 0}` is preferred "except in the case where
`p = 1` or `p = 0`, or when `Ua = 0`" — which is the `→` half of this iff; the exact
characterisation is proved here. The mandate's shape "`= 0 ↔ p = 0 ∨ p = 1 ∨ E[U] = 0`" is
false at `p = 1, E[U] < 0` (there `Δ = E[U] < 0`: always allowing a bad action is worse than
`s`), report deviation 1; the paper does not assert it (audit r1 N3). No `[0,1]` bound on `p`
is needed for the equality case.
Source: Hadfield-Menell et al. 2017 §3 (l. 76, 84–86); the paper states the `→` half
Kind: L
Fidelity: stronger: the paper asserts the boundary cases; this is the characterisation
Hyps: (a) none -/
theorem osgDelta_const_eq_zero_iff (μ : Distr Ω) (U : Ω → ℝ) (p : ℝ) :
    osgDelta μ U (fun _ => p) = 0 ↔ (0 < expect μ U → p = 1) ∧ (expect μ U < 0 → p = 0) := by
  rw [osgDelta, expect_const_mul]
  rcases lt_trichotomy (expect μ U) 0 with hE | hE | hE
  · rw [max_eq_right hE.le, sub_zero]
    constructor
    · intro h
      refine ⟨fun h' => absurd h' (not_lt.mpr hE.le), fun _ => ?_⟩
      rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h hE.ne
    · rintro ⟨-, h2⟩
      rw [h2 hE, zero_mul]
  · simp [hE]
  · rw [max_eq_left hE.le]
    constructor
    · intro h
      refine ⟨fun _ => ?_, fun h' => absurd h' (not_lt.mpr hE.le)⟩
      have : (p - 1) * expect μ U = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hE.ne'
    · rintro ⟨h1, -⟩
      rw [h1 hE, one_mul, sub_self]

/-! ## T4: Wängberg's `Δ ≥ 0` in the five statistics -/

/-- **`Δ ≥ 0` for the two-type human in the five statistics.** `osgDelta μ U (allowProb U p⁺ p⁻) ≥ 0`
iff Corollary 10's expression `(4) ≤ 0` (so `w(a)` is at least as good as `a`) *and*
`0 ≤ E[U | w(a)] = p⁺ p_r⁺ e⁺ + p⁻ (1 − p_r⁻) e⁻` (so `w(a)` is at least as good as `s`). Corollary 10
only compares `a` with `w(a)`; the paper's "R will take `s` if `E[U_a] ≤ 0`" is the other half.
Source: Wängberg et al. 2017 Theorem 9 / Corollary 10 (l. 266–282) and the `s` remark (l. 100)
Kind: L (over `expr4_eq` and `expect_allow_eq_stats`)
Fidelity: exact
Hyps: (a) none -/
theorem osgDelta_allowProb_nonneg_iff (μ : Distr Ω) (U : Ω → ℝ) (prPlus prMinus : ℝ) :
    0 ≤ osgDelta μ U (allowProb U prPlus prMinus) ↔
      expr4 μ U prPlus prMinus ≤ 0 ∧
        0 ≤ posMass μ U * prPlus * ePlus μ U + negMass μ U * (1 - prMinus) * eMinus μ U := by
  rw [osgDelta, sub_nonneg, max_le_iff, expr4_eq, sub_nonpos, expect_allow_eq_stats]

/-! ## Witnesses -/

/-- **T2's witness (N+)**: the uniform belief on `Fin 2` with `U = ![1, −1]` and the rational human
gives `Δ = 1/2` — both signs carry mass, so the incentive is strictly positive.
Source: Hadfield-Menell et al. 2017 Theorem 1 (N+ instance)
Kind: N+
Fidelity: exact -/
theorem w_theorem1 :
    osgDelta (Distr.uniform : Distr (Fin 2)) ![1, -1] (rationalAllow ![1, -1]) = 1 / 2 := by
  simp [osgDelta, expect, rationalAllow, Distr.uniform, Fin.sum_univ_two]

/-- **T2's degenerate side (N−)**: with `U ≥ 0` everywhere (`U = ![1, 2]`) the rational human
always allows and `Δ = 0` — Theorem 1's clause 1 holds with equality; disclosed as the
degenerate case, not the content.
Source: Hadfield-Menell et al. 2017 Theorem 1 (the boundary case)
Kind: N−
Fidelity: exact -/
theorem w_theorem1_degenerate :
    osgDelta (Distr.uniform : Distr (Fin 2)) ![1, 2] (rationalAllow ![1, 2]) = 0 := by
  simp [osgDelta, expect, rationalAllow, Distr.uniform, Fin.sum_univ_two]
  norm_num [max_def]

/-- **T3's witness (N+)**: the Dirac belief at a world with `U = 1` and a coin-flip human
(`π^H ≡ 1/2`) gives `Δ = −1/2` — a chance-node human costs the agent.
Source: Hadfield-Menell et al. 2017 §3 (the chance node), Corollary 1
Kind: N+
Fidelity: exact -/
theorem w_chance_node :
    osgDelta (Distr.delta (0 : Fin 2)) ![1, -1] (fun _ => (1 / 2 : ℝ)) = -(1 / 2) := by
  rw [osgDelta_delta]
  norm_num

end Cleanroom.Corrigibility.CorrOsgChai

import Cleanroom.Decision.DpTwoLesions.FixedPoints
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# T4 — Proposition 3(iii), the algebra: the quadratic of record

Clearing denominators, `Δ(p) − α` has the sign of an explicit quadratic
`Q(p) = qA p² + qB p + qE` with `qA = ακ²` (general `γ`, two grips; the mandate's §3.6 at the
doc's parameters). This file holds the quadratic, `signDelta`, the sign iffs, the fixed-point
set equality under (H) (`prop3_fixedPoints_eq`), Vieta's relations for two roots, the
factorisation and the sign-pattern lemmas, and the generic half of the three-fixed-point
characterisation (two roots in `(0, 1)` force `discrim > 0` and a vertex in `(0, 1)`). The
`ℝ`-half (square roots, IVT, convexity, the instances) is `InteriorReal.lean`.
Serves [[dp-two-lesions-mandate]] T4 (dp-core-075).
-/

namespace Cleanroom.Decision.DpTwoLesions

open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

namespace DlParams

variable (P : DlParams K)

/-! ## The quadratic -/

/-- `qA := ακ²`, the leading coefficient of `Q`.
Source: mandate §3.6 ("`A = π κ²`"), general `γ`
Kind: D -/
def qA : K := P.α * P.kappa ^ 2

/-- `qB`, the linear coefficient of `Q` (general `γ`; the mandate's `B` at `γ = (1, 0)`).
Source: mandate §3.6; derived by the formalizer by clearing denominators in `Delta_eq`
Kind: D -/
def qB : K :=
  P.β * (-(P.ρ * P.δL) * P.γ₁ * P.kappa + P.kcC * (P.ρA * P.δA) - (P.ρA * P.δA) * P.γ₀ * P.kappa +
    P.kcC * (P.ρ * P.δL)) +
  P.α * P.kappa * (P.ρ * P.δL - P.ρA * P.δA - P.kappa)

/-- `qE`, the constant coefficient of `Q` (general `γ`; the mandate's `E` at `γ = (1, 0)`).
Source: mandate §3.6; derived by the formalizer
Kind: D -/
def qE : K :=
  P.β * (P.ρ * P.δL) * (P.γ₁ * (P.ρA * P.δA + P.kappa) - P.ρA * P.δA * P.γ₀ - P.kcC) -
  P.α * (P.ρ * P.δL) * (P.ρA * P.δA + P.kappa)

/-- **The quadratic of record** `Q(p) := qA p² + qB p + qE`.
Source: mandate §3.6 ("`Q_δ(p) := A p² + B p + E`")
Kind: D -/
def Q (p : K) : K := P.qA * p ^ 2 + P.qB * p + P.qE

/-- The product of the two conditioning masses, `(ρδL + κp)(ρAδA + κ(1 − p))`.
Source: mandate T4 ("the positive denominator product `D`")
Kind: D -/
def denom (p : K) : K := (P.ρ * P.δL + P.kappa * p) * (P.ρA * P.δA + P.kappa * (1 - p))

/-- `0 < qA`. Source: none: infrastructure. Kind: L -/
theorem qA_pos : 0 < P.qA := mul_pos P.α_pos (pow_pos P.kappa_pos 2)

/-- `0 < denom p` on `[0, 1]`. Source: none: infrastructure. Kind: L -/
theorem denom_pos (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 < P.denom p :=
  mul_pos (P.denomSmoke_pos p h0 h1) (P.denomAbstain_pos p h0 h1)

/-- `Q` in the `a·x·x + b·x + c` shape of Mathlib's quadratic lemmas.
Source: none: infrastructure
Kind: L -/
theorem Q_eq_mul_self (p : K) : P.Q p = P.qA * (p * p) + P.qB * p + P.qE := by
  unfold Q; ring

/-- **`signDelta`: `(Δ(p) − α)·D(p) = Q(p)` on `[0, 1]`.** The sign of the evidential margin is
the sign of the quadratic.
Source: mandate T4 (`signDelta`); [[two-lesions-doc-2026-09-18]] §4 Proposition 3(iii) ("the
solutions of `Δ(p) = π`")
Kind: P
Fidelity: exact
Hyps: none -/
theorem signDelta (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    (P.Delta p - P.α) * P.denom p = P.Q p := by
  rw [Delta_eq P p h0 h1]
  unfold condSmoke condAbstain denom Q qA qB qE
  have hd1 : P.ρ * P.δL + P.kappa * p ≠ 0 := (P.denomSmoke_pos p h0 h1).ne'
  have hd2 : P.ρA * P.δA + P.kappa * (1 - p) ≠ 0 := (P.denomAbstain_pos p h0 h1).ne'
  rw [div_sub_div _ _ hd1 hd2, mul_div_assoc', sub_mul, div_mul_cancel₀ _ (mul_ne_zero hd1 hd2)]
  ring

/-- `Δ(p) < α ↔ Q(p) < 0` on `[0, 1]`. Source: mandate T4. Kind: P. Fidelity: exact.
Hyps: none -/
theorem Delta_lt_alpha_iff (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) : P.Delta p < P.α ↔ P.Q p < 0 := by
  have hs := P.signDelta p h0 h1
  have hd := P.denom_pos p h0 h1
  rw [← hs]
  constructor
  · intro h; exact mul_neg_of_neg_of_pos (sub_neg.mpr h) hd
  · intro h; by_contra hge
    exact absurd h (not_lt.mpr (mul_nonneg (sub_nonneg.mpr (not_lt.mp hge)) hd.le))

/-- `α < Δ(p) ↔ 0 < Q(p)` on `[0, 1]`. Source: mandate T4. Kind: P. Fidelity: exact.
Hyps: none -/
theorem alpha_lt_Delta_iff (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) : P.α < P.Delta p ↔ 0 < P.Q p := by
  have hs := P.signDelta p h0 h1
  have hd := P.denom_pos p h0 h1
  rw [← hs]
  constructor
  · intro h; exact mul_pos (sub_pos.mpr h) hd
  · intro h; by_contra hge
    exact absurd h (not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (not_lt.mp hge))
      hd.le))

/-- `Δ(p) = α ↔ Q(p) = 0` on `[0, 1]`. Source: mandate T4. Kind: P. Fidelity: exact.
Hyps: none -/
theorem Delta_eq_alpha_iff (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) : P.Delta p = P.α ↔ P.Q p = 0 := by
  have hs := P.signDelta p h0 h1
  have hd := P.denom_pos p h0 h1
  rw [← hs, mul_eq_zero, sub_eq_zero]
  exact ⟨fun h => Or.inl h, fun h => h.resolve_right hd.ne'⟩

/-- Under (H), `Q(0) > 0`. Source: doc Proposition 1. Kind: L -/
theorem Q_zero_pos (hH : P.HypH) : 0 < P.Q 0 :=
  (P.alpha_lt_Delta_iff 0 le_rfl zero_le_one).mp (P.alpha_lt_Delta_zero hH)

/-- Under (H), `Q(1) > 0`. Source: doc Proposition 2. Kind: L -/
theorem Q_one_pos (hH : P.HypH) : 0 < P.Q 1 :=
  (P.alpha_lt_Delta_iff 1 zero_le_one le_rfl).mp (P.alpha_lt_Delta_one hH)

/-! ## The fixed-point set -/

/-- **Proposition 3(iii), the set equality**: under (H) the fixed points in `[0, 1]` are `0`
together with the roots of `Q` in `(0, 1)`.
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 3(iii) ("the fixed points are `0`
together with the crossings"); mandate T4 (`prop3_fixedPoints_eq`)
Kind: P
Fidelity: exact (the crossings are the roots of the explicit quadratic; no convexity used)
Hyps: (a) (H) -/
theorem prop3_fixedPoints_eq (hH : P.HypH) :
    P.fixedPts = {0} ∪ {p | 0 < p ∧ p < 1 ∧ P.Q p = 0} := by
  ext p
  simp only [fixedPts, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, Set.mem_Icc]
  constructor
  · rintro ⟨⟨h0, h1⟩, hfp⟩
    rcases h0.lt_or_eq with h0 | h0
    · rcases h1.lt_or_eq with h1 | h1
      · right
        exact ⟨h0, h1, (P.Delta_eq_alpha_iff p h0.le h1.le).mp
          ((P.isFixedPt_interior_iff h0 h1).mp hfp)⟩
      · subst h1; exact absurd hfp (P.prop2 hH)
    · left; exact h0.symm
  · rintro (rfl | ⟨h0, h1, hq⟩)
    · exact ⟨⟨le_rfl, zero_le_one⟩, P.prop1 hH⟩
    · exact ⟨⟨h0.le, h1.le⟩, (P.isFixedPt_interior_iff h0 h1).mpr
        ((P.Delta_eq_alpha_iff p h0.le h1.le).mpr hq)⟩

/-! ## Two roots: Vieta, the factorisation, the sign pattern -/

/-- **Vieta** for two distinct roots of `Q`: `qB = −qA(r₁ + r₂)` and `qE = qA r₁ r₂`.
Source: none: infrastructure
Kind: L -/
theorem vieta {r₁ r₂ : K} (hne : r₁ ≠ r₂) (h₁ : P.Q r₁ = 0) (h₂ : P.Q r₂ = 0) :
    P.qB = -P.qA * (r₁ + r₂) ∧ P.qE = P.qA * r₁ * r₂ := by
  unfold Q at h₁ h₂
  have hprod : (r₁ - r₂) * (P.qA * (r₁ + r₂) + P.qB) = 0 := by linear_combination h₁ - h₂
  have hB : P.qA * (r₁ + r₂) + P.qB = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)
  refine ⟨by linear_combination hB, ?_⟩
  linear_combination h₁ - r₁ * hB

/-- **The factorisation** `Q(p) = qA (p − r₁)(p − r₂)` for two distinct roots.
Source: none: infrastructure
Kind: L -/
theorem Q_factor {r₁ r₂ : K} (hne : r₁ ≠ r₂) (h₁ : P.Q r₁ = 0) (h₂ : P.Q r₂ = 0) (p : K) :
    P.Q p = P.qA * (p - r₁) * (p - r₂) := by
  obtain ⟨hB, hE⟩ := P.vieta hne h₁ h₂
  unfold Q; rw [hB, hE]; ring

/-- Between two roots `r₁ < r₂`, `Q < 0`; outside, `Q > 0`.
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 3(iii) proof ("falls below `π` on a
single open interval bounded by exactly two crossings")
Kind: P
Fidelity: exact
Hyps: none -/
theorem Q_sign_pattern {r₁ r₂ : K} (hlt : r₁ < r₂) (h₁ : P.Q r₁ = 0) (h₂ : P.Q r₂ = 0) (p : K) :
    (P.Q p < 0 ↔ r₁ < p ∧ p < r₂) ∧ (0 < P.Q p ↔ p < r₁ ∨ r₂ < p) := by
  rw [P.Q_factor hlt.ne h₁ h₂ p]
  have hA := P.qA_pos
  constructor
  · constructor
    · intro h
      by_contra hc
      rw [not_and_or, not_lt, not_lt] at hc
      rcases hc with hc | hc
      · have : 0 ≤ P.qA * (p - r₁) * (p - r₂) :=
          mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hA.le (by linarith))
            (by linarith)
        linarith
      · have : 0 ≤ P.qA * (p - r₁) * (p - r₂) :=
          mul_nonneg (mul_nonneg hA.le (by linarith)) (by linarith)
        linarith
    · rintro ⟨ha, hb⟩
      exact mul_neg_of_pos_of_neg (mul_pos hA (by linarith)) (by linarith)
  · constructor
    · intro h
      by_contra hc
      rw [not_or, not_lt, not_lt] at hc
      have : P.qA * (p - r₁) * (p - r₂) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hA.le (by linarith [hc.1])) (by linarith [hc.2])
      linarith
    · rintro (ha | ha)
      · exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hA (by linarith)) (by linarith)
      · exact mul_pos (mul_pos hA (by linarith)) (by linarith)

/-- **The three-fixed-point regime forces `discrim > 0` and a vertex in `(0, 1)`** (the
`⇒` half of Proposition 3(iii)'s regime criterion, over any ordered field): if the fixed points
are exactly `{0, p̌, p̂}` with `0 < p̌ < p̂ < 1`, then `discrim qA qB qE = qA²(p̂ − p̌)² > 0` and
`−qB/(2qA) = (p̌ + p̂)/2 ∈ (0, 1)`.
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 3(iii) ("if `m(δ) < π`, there are exactly
three fixed points"), the regime read as the discriminant condition (mandate §3.6)
Kind: P
Fidelity: exact
Hyps: (a) (H) -/
theorem prop3_three_imp (hH : P.HypH) {p₁ p₂ : K} (h0 : 0 < p₁) (h12 : p₁ < p₂) (h1 : p₂ < 1)
    (hset : P.fixedPts = {0, p₁, p₂}) :
    0 < discrim P.qA P.qB P.qE ∧ 0 < -P.qB / (2 * P.qA) ∧ -P.qB / (2 * P.qA) < 1 := by
  have hmem : ∀ p ∈ P.fixedPts, p = 0 ∨ (0 < p ∧ p < 1 ∧ P.Q p = 0) := by
    intro p hp
    rw [P.prop3_fixedPoints_eq hH] at hp
    simpa using hp
  have hq1 : P.Q p₁ = 0 := by
    have := hmem p₁ (by rw [hset]; simp)
    rcases this with h | h
    · exact absurd h h0.ne'
    · exact h.2.2
  have hq2 : P.Q p₂ = 0 := by
    have := hmem p₂ (by rw [hset]; simp)
    rcases this with h | h
    · exact absurd h (by linarith)
    · exact h.2.2
  obtain ⟨hB, hE⟩ := P.vieta h12.ne hq1 hq2
  have hA := P.qA_pos
  refine ⟨?_, ?_, ?_⟩
  · unfold discrim
    rw [hB, hE]
    have : (-P.qA * (p₁ + p₂)) ^ 2 - 4 * P.qA * (P.qA * p₁ * p₂) = P.qA ^ 2 * (p₂ - p₁) ^ 2 := by
      ring
    rw [this]
    exact mul_pos (pow_pos hA 2) (pow_pos (sub_pos.mpr h12) 2)
  · rw [hB]
    have : -(-P.qA * (p₁ + p₂)) / (2 * P.qA) = (p₁ + p₂) / 2 := by
      field_simp
    rw [this]
    linarith
  · rw [hB]
    have : -(-P.qA * (p₁ + p₂)) / (2 * P.qA) = (p₁ + p₂) / 2 := by
      field_simp
    rw [this]
    linarith

/-- **The regime given a square root of the discriminant** (the `⇐` half's engine, over any
ordered field that supplies `s` with `s² = discrim`): if `0 < s`, `s² = discrim`, and the vertex
`−qB/(2qA) ∈ (0, 1)`, then under (H) the fixed points are exactly
`{0, (−qB − s)/(2qA), (−qB + s)/(2qA)}` with `0 < (−qB − s)/(2qA) < (−qB + s)/(2qA) < 1`.
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 3(iii); mandate T4 ("the quadratic's roots
must be shown to lie in `(0, 1)` from `Q(0), Q(1) > 0` and the vertex")
Kind: P
Fidelity: exact
Hyps: (a) (H); the square root is supplied (`ℝ` supplies it in `InteriorReal.lean`) -/
theorem fixedPts_eq_of_sqrt (hH : P.HypH) {s : K} (hs0 : 0 < s)
    (hs : discrim P.qA P.qB P.qE = s * s) (hv0 : 0 < -P.qB / (2 * P.qA))
    (hv1 : -P.qB / (2 * P.qA) < 1) :
    0 < (-P.qB - s) / (2 * P.qA) ∧ (-P.qB - s) / (2 * P.qA) < (-P.qB + s) / (2 * P.qA) ∧
    (-P.qB + s) / (2 * P.qA) < 1 ∧
    P.fixedPts = {0, (-P.qB - s) / (2 * P.qA), (-P.qB + s) / (2 * P.qA)} := by
  have hA := P.qA_pos
  have h2A : 0 < 2 * P.qA := by linarith
  have hQ0 := P.Q_zero_pos hH
  have hQ1 := P.Q_one_pos hH
  have hE : P.qE = P.Q 0 := by unfold Q; ring
  have hQ1' : P.Q 1 = P.qA + P.qB + P.qE := by unfold Q; ring
  -- `−qB > 0` and `2qA + qB > 0` from the vertex
  have hB : 0 < -P.qB := by
    have := (div_pos_iff_of_pos_right h2A).mp hv0; linarith
  have hB' : 0 < 2 * P.qA + P.qB := by
    have := (div_lt_one h2A).mp hv1; linarith
  -- `s < −qB` and `s < 2qA + qB` by comparing squares
  have hs1 : s < -P.qB := by
    have hsq : s * s < (-P.qB) * (-P.qB) := by
      rw [← hs]; unfold discrim; rw [hE]; nlinarith
    nlinarith
  have hs2 : s < 2 * P.qA + P.qB := by
    have hsq : s * s < (2 * P.qA + P.qB) * (2 * P.qA + P.qB) := by
      rw [← hs]; unfold discrim; rw [hE]; nlinarith
    nlinarith
  have hr0 : 0 < (-P.qB - s) / (2 * P.qA) := div_pos (by linarith) h2A
  have hr12 : (-P.qB - s) / (2 * P.qA) < (-P.qB + s) / (2 * P.qA) :=
    div_lt_div_of_pos_right (by linarith) h2A
  have hr1 : (-P.qB + s) / (2 * P.qA) < 1 := (div_lt_one h2A).mpr (by linarith)
  refine ⟨hr0, hr12, hr1, ?_⟩
  rw [P.prop3_fixedPoints_eq hH]
  have hroot : ∀ p, P.Q p = 0 ↔ p = (-P.qB + s) / (2 * P.qA) ∨ p = (-P.qB - s) / (2 * P.qA) := by
    intro p
    rw [Q_eq_mul_self]
    exact quadratic_eq_zero_iff hA.ne' hs p
  ext p
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, Set.mem_insert_iff]
  constructor
  · rintro (rfl | ⟨-, -, hq⟩)
    · left; rfl
    · rcases (hroot p).mp hq with h | h
      · right; right; exact h
      · right; left; exact h
  · rintro (rfl | rfl | rfl)
    · left; rfl
    · right; exact ⟨hr0, by linarith, (hroot _).mpr (Or.inr rfl)⟩
    · right; exact ⟨by linarith, hr1, (hroot _).mpr (Or.inl rfl)⟩

/-- **`discrim < 0` forces `Q > 0` everywhere** (the unique-fixed-point regime, over any ordered
field): `4qA·Q(p) = (2qA p + qB)² − discrim`.
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 3(iii) ("if `m(δ) > π`, the unique fixed
point is `0`"), the regime read as the discriminant condition
Kind: P
Fidelity: exact
Hyps: none -/
theorem Q_pos_of_discrim_neg (hd : discrim P.qA P.qB P.qE < 0) (p : K) : 0 < P.Q p := by
  have hA := P.qA_pos
  have h : 4 * P.qA * P.Q p = (2 * P.qA * p + P.qB) ^ 2 - discrim P.qA P.qB P.qE := by
    unfold Q discrim; ring
  have : 0 < 4 * P.qA * P.Q p := by rw [h]; nlinarith [sq_nonneg (2 * P.qA * p + P.qB)]
  exact pos_of_mul_pos_right this (by linarith)

/-- Under (H), if `Q > 0` on `[0, 1]` the unique fixed point is `0`.
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 3(iii) ("the unique fixed point is `0`")
Kind: P
Fidelity: exact
Hyps: (a) (H) -/
theorem fixedPts_eq_singleton_of_Q_pos (hH : P.HypH) (hQ : ∀ p, 0 ≤ p → p ≤ 1 → 0 < P.Q p) :
    P.fixedPts = {0} := by
  rw [P.prop3_fixedPoints_eq hH]
  ext p
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro (h | ⟨h0, h1, hq⟩)
    · exact h
    · exact absurd hq (hQ p h0.le h1.le).ne'
  · intro h; left; exact h

end DlParams

end Cleanroom.Decision.DpTwoLesions

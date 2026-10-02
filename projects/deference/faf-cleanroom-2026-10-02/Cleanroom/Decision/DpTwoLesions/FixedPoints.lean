import Cleanroom.Decision.DpTwoLesions.Laws

/-!
# T3 — Propositions 1–2: the endpoints

`Δ(0)` and `Δ(1)` in closed form (general `γ`), the doc's two inequalities, the fixed-point
characterisations at the endpoints and in the interior (Claim 1.1's iffs), Proposition 1
(abstention is a fixed point under (H)), Proposition 2 (smoking is not), and the scope
witness: at the session parameters (H) fails and the smoke label **is** a fixed point.
Serves [[dp-two-lesions-mandate]] T3 (dp-core-073/074, 083, 116(1)).
-/

namespace Cleanroom.Decision.DpTwoLesions

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

namespace DlParams

variable (P : DlParams K)

/-! ## The endpoint values -/

/-- `1 − ρδL > 0`. Source: none: infrastructure. Kind: L -/
theorem one_sub_ρδL_pos : 0 < 1 - P.ρ * P.δL := by
  have : P.ρ * P.δL ≤ P.ρ := by nlinarith [P.ρ_pos, P.δL_le_one]
  linarith [P.ρ_add_ρA_lt_one, P.ρA_pos]

/-- `1 − ρAδA > 0`. Source: none: infrastructure. Kind: L -/
theorem one_sub_ρAδA_pos : 0 < 1 - P.ρA * P.δA := by
  have : P.ρA * P.δA ≤ P.ρA := by nlinarith [P.ρA_pos, P.δA_le_one]
  linarith [P.ρ_add_ρA_lt_one, P.ρ_pos]

/-- **`Δ(0) = β(1 − ρ)(γ₁ − γ₀)/(1 − ρδL)`** — the doc's `C(1 − ε_L)/(1 − ε_Lδ)` at
`γ = (1, 0)`.
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 1 ("`Δ(0) = C(1 − ε_L)/(1 − ε_Lδ)`")
Kind: P
Fidelity: exact (general `γ`)
Hyps: none -/
theorem Delta_zero : P.Delta 0 = P.β * ((1 - P.ρ) * (P.γ₁ - P.γ₀) / (1 - P.ρ * P.δL)) := by
  rw [Delta_eq P 0 le_rfl zero_le_one]
  unfold condSmoke condAbstain
  have ha : P.ρ * P.δL ≠ 0 := (mul_pos P.ρ_pos P.δL_pos).ne'
  have hb : P.ρA * P.δA + P.kappa * (1 - 0) ≠ 0 := (P.denomAbstain_pos 0 le_rfl zero_le_one).ne'
  have hc : (1 - P.ρ * P.δL) ≠ 0 := P.one_sub_ρδL_pos.ne'
  have hk : P.ρA * P.δA + P.kappa * (1 - 0) = 1 - P.ρ * P.δL := by unfold kappa; ring
  rw [hk] at hb ⊢
  congr 1
  simp only [mul_zero, add_zero, sub_zero]
  rw [div_sub_div _ _ ha hc, div_eq_div_iff (mul_ne_zero ha hc) hc]
  unfold kcC
  ring

/-- **`Δ(1) = βρ(γ₁ − γ₀)/(1 − ρAδA)`** — the doc's `Cε_L/(1 − ε_Aδ)` at `γ = (1, 0)`.
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 2 ("`Δ(1) = Cε_L/(1 − ε_Aδ)`")
Kind: P
Fidelity: exact (general `γ`)
Hyps: none -/
theorem Delta_one : P.Delta 1 = P.β * (P.ρ * (P.γ₁ - P.γ₀) / (1 - P.ρA * P.δA)) := by
  rw [Delta_eq P 1 zero_le_one le_rfl]
  unfold condSmoke condAbstain
  have hb : P.ρA * P.δA ≠ 0 := (mul_pos P.ρA_pos P.δA_pos).ne'
  have hc : (1 - P.ρA * P.δA) ≠ 0 := P.one_sub_ρAδA_pos.ne'
  have hk : P.ρ * P.δL + P.kappa * 1 = 1 - P.ρA * P.δA := by unfold kappa; ring
  rw [hk]
  congr 1
  simp only [mul_one, sub_self, mul_zero, add_zero]
  rw [div_sub_div _ _ hc hb, div_eq_div_iff (mul_ne_zero hc hb) hc]
  unfold kcC
  ring

/-- **The doc's first inequality**: `Δ(0) ≥ β(γ₁ − γ₀)(1 − ρ)`, since `1 − ρδL ≤ 1`.
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 1 proof ("Since `1 − ε_Lδ ≤ 1` we have
`Δ(0) ≥ C(1 − ε_L)`")
Kind: P
Fidelity: exact (general `γ`)
Hyps: none -/
theorem Delta_zero_ge : P.β * (P.γ₁ - P.γ₀) * (1 - P.ρ) ≤ P.Delta 0 := by
  rw [Delta_zero]
  have hc := P.one_sub_ρδL_pos
  have hnum : 0 ≤ (1 - P.ρ) * (P.γ₁ - P.γ₀) := by
    apply mul_nonneg <;> linarith [P.ρ_add_ρA_lt_one, P.ρA_pos, P.γ₀_le_γ₁]
  have hle : (1 - P.ρ) * (P.γ₁ - P.γ₀) ≤ (1 - P.ρ) * (P.γ₁ - P.γ₀) / (1 - P.ρ * P.δL) := by
    rw [le_div_iff₀ hc]
    nlinarith [mul_pos P.ρ_pos P.δL_pos]
  calc P.β * (P.γ₁ - P.γ₀) * (1 - P.ρ) = P.β * ((1 - P.ρ) * (P.γ₁ - P.γ₀)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hle P.β_pos.le

/-- **The doc's second inequality**: `Δ(1) ≥ β(γ₁ − γ₀)ρ`, since `1 − ρAδA ≤ 1`.
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 2 proof ("Since `1 − ε_Aδ ≤ 1` we have
`Δ(1) ≥ Cε_L`")
Kind: P
Fidelity: exact (general `γ`)
Hyps: none -/
theorem Delta_one_ge : P.β * (P.γ₁ - P.γ₀) * P.ρ ≤ P.Delta 1 := by
  rw [Delta_one]
  have hc := P.one_sub_ρAδA_pos
  have hnum : 0 ≤ P.ρ * (P.γ₁ - P.γ₀) := mul_nonneg P.ρ_pos.le (by linarith [P.γ₀_le_γ₁])
  have hle : P.ρ * (P.γ₁ - P.γ₀) ≤ P.ρ * (P.γ₁ - P.γ₀) / (1 - P.ρA * P.δA) := by
    rw [le_div_iff₀ hc]
    nlinarith [mul_pos P.ρA_pos P.δA_pos]
  calc P.β * (P.γ₁ - P.γ₀) * P.ρ = P.β * (P.ρ * (P.γ₁ - P.γ₀)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hle P.β_pos.le

/-! ## Fixed points at the endpoints and in the interior (Claim 1.1's iffs) -/

/-- **Abstention is a fixed point iff `α ≤ Δ(0)`** (the tie `α = Δ(0)` included, where
`β(0) = [0, 1] ∋ 0`).
Source: [[smoking-lesion-exploration-and-boundaries]] §1 Claim 1.1 (the sign of the gap at the
pure labels); doc §3 (the best response)
Kind: P
Fidelity: exact
Hyps: none -/
theorem isFixedPt_zero_iff : P.IsFixedPt 0 ↔ P.α ≤ P.Delta 0 := by
  unfold IsFixedPt bestResp
  rw [Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, -, -, -⟩
    by_contra hlt
    exact zero_ne_one (h (lt_of_not_ge hlt))
  · intro h
    exact ⟨fun hgt => absurd hgt (not_lt.mpr h), fun _ => rfl, le_rfl, zero_le_one⟩

/-- **Smoking is a fixed point iff `Δ(1) ≤ α`**.
Source: [[smoking-lesion-exploration-and-boundaries]] §1 Claim 1.1; doc §3
Kind: P
Fidelity: exact
Hyps: none -/
theorem isFixedPt_one_iff : P.IsFixedPt 1 ↔ P.Delta 1 ≤ P.α := by
  unfold IsFixedPt bestResp
  rw [Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, h, -, -⟩
    by_contra hlt
    exact one_ne_zero (h (lt_of_not_ge hlt))
  · intro h
    exact ⟨fun _ => rfl, fun hlt => absurd hlt (not_lt.mpr h), zero_le_one, le_rfl⟩

/-- **An interior policy is a fixed point iff it is a tie**: for `0 < p < 1`,
`p ∈ β(p) ↔ Δ(p) = α`.
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 3(iii) proof ("the fixed points are `0`
together with the crossings, at which the agent is indifferent")
Kind: P
Fidelity: exact
Hyps: none -/
theorem isFixedPt_interior_iff {p : K} (h0 : 0 < p) (h1 : p < 1) :
    P.IsFixedPt p ↔ P.Delta p = P.α := by
  unfold IsFixedPt bestResp
  rw [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hgt, hlt, -, -⟩
    rcases lt_trichotomy P.α (P.Delta p) with h | h | h
    · exact absurd (hlt h) h0.ne'
    · exact h.symm
    · exact absurd (hgt h) h1.ne
  · intro h
    exact ⟨fun hgt => absurd hgt (by rw [h]; exact lt_irrefl _),
      fun hlt => absurd hlt (by rw [h]; exact lt_irrefl _), h0.le, h1.le⟩

/-! ## (H) and its bite -/

/-- Under (H), `α < Δ(0)`.
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 1 proof
Kind: L -/
theorem alpha_lt_Delta_zero (hH : P.HypH) : P.α < P.Delta 0 := by
  unfold HypH at hH
  have h1 : P.β * (P.γ₁ - P.γ₀) * min P.ρ (1 - P.ρ) ≤ P.β * (P.γ₁ - P.γ₀) * (1 - P.ρ) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _)
      (mul_nonneg P.β_pos.le (by linarith [P.γ₀_le_γ₁]))
  linarith [P.Delta_zero_ge]

/-- Under (H), `α < Δ(1)`.
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 2 proof
Kind: L -/
theorem alpha_lt_Delta_one (hH : P.HypH) : P.α < P.Delta 1 := by
  unfold HypH at hH
  have h1 : P.β * (P.γ₁ - P.γ₀) * min P.ρ (1 - P.ρ) ≤ P.β * (P.γ₁ - P.γ₀) * P.ρ :=
    mul_le_mul_of_nonneg_left (min_le_left _ _)
      (mul_nonneg P.β_pos.le (by linarith [P.γ₀_le_γ₁]))
  linarith [P.Delta_one_ge]

/-- **Proposition 1 (abstention is a fixed point)**: under (H), `0 ∈ β(0)` for every grip —
and strictly so (`β(0) = {0}`, since `Δ(0) > α`).
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 1
Kind: P
Fidelity: exact (general `γ`; every `δL, δA ∈ (0, 1]` by the parameter bounds)
Hyps: (a) (H) is the doc's standing hypothesis, stated -/
theorem prop1 (hH : P.HypH) : P.IsFixedPt 0 :=
  P.isFixedPt_zero_iff.mpr (P.alpha_lt_Delta_zero hH).le

/-- Under (H) the best response at `0` is exactly `{0}`.
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 1 proof ("so `β(0) = {0}`")
Kind: P
Fidelity: exact
Hyps: (a) (H) -/
theorem prop1_bestResp (hH : P.HypH) : P.bestResp 0 = {0} := by
  have h := P.alpha_lt_Delta_zero hH
  ext b
  unfold bestResp
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, hb, -, -⟩; exact hb h
  · rintro rfl; exact ⟨fun hgt => absurd hgt (not_lt.mpr h.le), fun _ => rfl, le_rfl, zero_le_one⟩

/-- **Proposition 2 (smoking is not a fixed point)**: under (H), `1 ∉ β(1)` for every grip.
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 2
Kind: P
Fidelity: exact (general `γ`)
Hyps: (a) (H) -/
theorem prop2 (hH : P.HypH) : ¬ P.IsFixedPt 1 := by
  rw [isFixedPt_one_iff]
  exact not_le.mpr (P.alpha_lt_Delta_one hH)

/-- Under (H) the best response at `1` is exactly `{0}`.
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 2 proof ("so `β(1) = {0}`")
Kind: P
Fidelity: exact
Hyps: (a) (H) -/
theorem prop2_bestResp (hH : P.HypH) : P.bestResp 1 = {0} := by
  have h := P.alpha_lt_Delta_one hH
  ext b
  unfold bestResp
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, hb, -, -⟩; exact hb h
  · rintro rfl; exact ⟨fun hgt => absurd hgt (not_lt.mpr h.le), fun _ => rfl, le_rfl, zero_le_one⟩

end DlParams

/-! ## Witnesses: (H) holds at the doc's parameters, fails at the session's -/

/-- **(H) holds at the doc's parameters** for every grip: `1 < 100·1·min(1/5, 4/5) = 20`.
Source: [[two-lesions-doc-2026-09-18]] §4 ("These are the standard numbers of the problem")
Kind: N+ -/
theorem docP_hypH (δ : K) (h0 : 0 < δ) (h1 : δ ≤ 1) : (docP δ h0 h1).HypH := by
  unfold DlParams.HypH docP
  simp only
  rw [min_eq_left (by norm_num)]
  norm_num

/-- **(H) fails at the session parameters**: `10·(11/20)·min(1/10, 9/10) = 11/20 < 1 = α`.
Source: [[iv-design-draw-as-instrument]] §5 ("(H) fails since `βρ(γ₁−γ₀) = 0.55 < α`")
Kind: N+ -/
theorem sessP_not_hypH : ¬ (sessP : DlParams K).HypH := by
  unfold DlParams.HypH sessP
  simp only
  rw [min_eq_left (by norm_num)]
  norm_num

/-- **`Δ(1) = 110/199` at the session parameters** (`≈ 0.553 < 1`).
Source: mandate T3 ("`Δ(1) = 0.0553·10 < 1`")
Kind: N+ -/
theorem sessP_Delta_one : (sessP : DlParams ℚ).Delta 1 = 110/199 := by
  rw [DlParams.Delta_one]
  simp [sessP]; norm_num

/-- **The scope witness (dp-core-116(1)): outside (H) the smoke label is a fixed point.** At the
session parameters `Δ(1) = 110/199 < 1 = α`, so `1 ∈ β(1)`: Proposition 2 and moral two hold
only under (H).
Source: [[smoking-lesion-exploration-and-boundaries]] §1 (the session regime);
[[iv-design-draw-as-instrument]] §5 ("the smoke label *is* a fixed point"); mandate T3
Kind: N+
Fidelity: exact -/
theorem prop2_fails_outsideH : (sessP : DlParams ℚ).IsFixedPt 1 := by
  rw [DlParams.isFixedPt_one_iff, sessP_Delta_one]
  show (110/199 : ℚ) ≤ 1
  norm_num

/-- Abstention is also a fixed point at the session parameters (`Δ(0) = 99/20 > 1`): both pure
labels are fixed points there.
Source: [[iv-design-draw-as-instrument]] §9 ("both pure labels fixed")
Kind: N+ -/
theorem sessP_isFixedPt_zero : (sessP : DlParams ℚ).IsFixedPt 0 := by
  rw [DlParams.isFixedPt_zero_iff, DlParams.Delta_zero]
  simp [sessP]; norm_num

/-- At the doc's parameters abstention is a fixed point and smoking is not, for every grip
(Propositions 1–2 instantiated; N+ for (H)-theorems).
Source: [[two-lesions-doc-2026-09-18]] §4
Kind: N+ -/
theorem docP_prop12 (δ : K) (h0 : 0 < δ) (h1 : δ ≤ 1) :
    (docP δ h0 h1).IsFixedPt 0 ∧ ¬ (docP δ h0 h1).IsFixedPt 1 :=
  ⟨DlParams.prop1 _ (docP_hypH δ h0 h1), DlParams.prop2 _ (docP_hypH δ h0 h1)⟩

end Cleanroom.Decision.DpTwoLesions

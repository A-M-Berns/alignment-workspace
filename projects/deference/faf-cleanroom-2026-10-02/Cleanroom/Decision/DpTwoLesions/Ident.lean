import Cleanroom.Decision.DpTwoLesions.Laws

/-!
# T9 — Identification from policy variation

The three observables `(P_p(m=1), P_p(k∧m=1), P_p(k∧m=0))` as one triple `obs`, each
coordinate affine in the label with named intercepts and slopes (`ident_affine`); two labels
identify `(ρδL, ρAδA, κ, γ₁, γ₀, c_C)` (`ident_two_labels`, an injectivity statement over the
typed family `DlParams`), the ITT-null identity, `ρ` and `δL` separately iff `γ₁ ≠ γ₀`
(`ident_rho_sep`), `ρA` and `δA` only as a product (`ident_rhoA_not_separately`: two parameter
sets with the same observables at every label), and one label identifies nothing
(`ident_one_label_nothing`: the forcing-free **recorded** tree `slOneCausal` of
`dp-smoking-lesion` fits the three numbers exactly). `oneLaw` restated at every finite set of
labels (`channel_bypass_overwrite_indist`).
Serves [[dp-two-lesions-mandate]] T9 (dp-core-093, 098, 2-003, 2-008(a)).
-/

namespace Cleanroom.Decision.DpTwoLesions

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

namespace DlParams

variable (P : DlParams K)

/-- **The observables at label `p`**: `(P_p(smoke), P_p(cancer ∧ smoke), P_p(cancer ∧ abstain))`
on the overwrite tree (equal on the bypass tree by `oneLaw`).
Source: [[iv-design-draw-as-instrument]] §2 (B1) ("the pooled record is three numbers")
Kind: D -/
def obs (p : K) : K × K × K :=
  (P.nuP p evSmoke, P.nuP p (evCancer ∩ evSmoke), P.nuP p (evCancer ∩ evAbstain))

/-- **(a) Each observable is affine in the label**, with intercepts `(ρδL, ρδLγ₁, ρAδAγ₀ + κc_C)`
and slopes `(κ, κc_C, −κc_C)`.
Source: [[iv-design-draw-as-instrument]] §2 (B1) ("each observable is affine in `p`");
[[two-lesions-doc-2026-09-18]] §5 ("the joint frequencies `P_p` are affine in `p`")
Kind: P
Fidelity: exact
Hyps: none -/
theorem ident_affine (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    P.obs p = (P.ρ * P.δL + P.kappa * p, P.ρ * P.δL * P.γ₁ + P.kcC * p,
      (P.ρA * P.δA * P.γ₀ + P.kcC) + (-P.kcC) * p) := by
  unfold obs
  rw [nuP_smoke P p h0 h1, nuP_cancer_smoke P p h0 h1, nuP_cancer_abstain P p h0 h1]
  congr 2; ring

/-- **The ITT-null identity**: the slopes of `P_p(k ∧ m=1)` and `P_p(k ∧ m=0)` sum to `0`
(the label moves cancer mass between the two acts without changing the total).
Source: [[iv-design-draw-as-instrument]] §2 (B2) ("the two slopes sum to exactly `0` — the
ITT-null test")
Kind: P
Fidelity: exact
Hyps: none -/
theorem ident_ittNull (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    P.nuP p (evCancer ∩ evSmoke) + P.nuP p (evCancer ∩ evAbstain) =
      P.ρ * P.δL * P.γ₁ + P.ρA * P.δA * P.γ₀ + P.kcC := by
  rw [nuP_cancer_smoke P p h0 h1, nuP_cancer_abstain P p h0 h1]; ring

/-- Two values of an affine function at distinct points determine its intercept and slope.
Source: none: infrastructure
Kind: L -/
theorem affine_inj {i s i' s' p₁ p₂ : K} (hne : p₁ ≠ p₂) (h₁ : i + s * p₁ = i' + s' * p₁)
    (h₂ : i + s * p₂ = i' + s' * p₂) : i = i' ∧ s = s' := by
  have hs : (s - s') * (p₁ - p₂) = 0 := by linear_combination h₁ - h₂
  have hs' : s = s' := by
    have := (mul_eq_zero.mp hs).resolve_right (sub_ne_zero.mpr hne)
    linarith
  exact ⟨by rw [hs'] at h₁; linarith, hs'⟩

/-- **(b) Two labels identify the forcing structure**: if two parameter sets give the same
three observables at two distinct labels in `[0, 1]`, then `ρδL`, `ρAδA`, `κ`, `γ₁`, `γ₀` and
`c_C` agree. An injectivity statement over `DlParams`, never a numerical recovery.
Source: [[iv-design-draw-as-instrument]] §2 (B2) ("From `p = 3/10` and `7/10`: forced-smoke mass
`ρδ_L`, forced-abstain mass `ρ_Aδ_A`, complier mass `κ`, cancer among forced smokes `γ₁`, among
forced abstentions `γ₀`, among compliers `c_C`"); [[two-lesions-exchange-2026-09-19]]
Kind: P
Fidelity: exact
Hyps: none -/
theorem ident_two_labels (P' : DlParams K) {p₁ p₂ : K} (h10 : 0 ≤ p₁) (h11 : p₁ ≤ 1)
    (h20 : 0 ≤ p₂) (h21 : p₂ ≤ 1) (hne : p₁ ≠ p₂) (e₁ : P.obs p₁ = P'.obs p₁)
    (e₂ : P.obs p₂ = P'.obs p₂) :
    P.ρ * P.δL = P'.ρ * P'.δL ∧ P.ρA * P.δA = P'.ρA * P'.δA ∧ P.kappa = P'.kappa ∧
    P.γ₁ = P'.γ₁ ∧ P.γ₀ = P'.γ₀ ∧ P.cC = P'.cC := by
  rw [P.ident_affine p₁ h10 h11, P'.ident_affine p₁ h10 h11] at e₁
  rw [P.ident_affine p₂ h20 h21, P'.ident_affine p₂ h20 h21] at e₂
  simp only [Prod.mk.injEq] at e₁ e₂
  obtain ⟨a1, b1, c1⟩ := e₁
  obtain ⟨a2, b2, c2⟩ := e₂
  obtain ⟨ia, sa⟩ := affine_inj hne a1 a2
  obtain ⟨ib, sb⟩ := affine_inj hne b1 b2
  obtain ⟨ic, sc⟩ := affine_inj hne c1 c2
  have hρδ : P.ρ * P.δL = P'.ρ * P'.δL := ia
  have hκ : P.kappa = P'.kappa := sa
  have hc : P.kcC = P'.kcC := sb
  have hγ₁ : P.γ₁ = P'.γ₁ := by
    have hpos : P.ρ * P.δL ≠ 0 := (mul_pos P.ρ_pos P.δL_pos).ne'
    have : P.ρ * P.δL * P.γ₁ = P.ρ * P.δL * P'.γ₁ := by rw [ib, hρδ]
    exact mul_left_cancel₀ hpos this
  have hρAδA : P.ρA * P.δA = P'.ρA * P'.δA := by
    have h := P.kappa; unfold kappa at hκ; linarith
  have hγ₀ : P.γ₀ = P'.γ₀ := by
    have hpos : P.ρA * P.δA ≠ 0 := (mul_pos P.ρA_pos P.δA_pos).ne'
    have : P.ρA * P.δA * P.γ₀ = P.ρA * P.δA * P'.γ₀ := by
      have := ic; rw [hc, hρAδA] at this; rw [hρAδA]; linarith
    exact mul_left_cancel₀ hpos this
  refine ⟨hρδ, hρAδA, hκ, hγ₁, hγ₀, ?_⟩
  unfold cC; rw [hc, hκ]

/-- **`ρ` and `δL` separately, when `γ₁ ≠ γ₀`**: the identified quantities give
`ρ(1 − δL) = κ(c_C − γ₀)/(γ₁ − γ₀)`, hence `ρ = ρ(1−δL) + ρδL` and `δL = ρδL/ρ`.
Source: [[iv-design-draw-as-instrument]] §2 (B2) ("`ρ(1−δ_L) = κ(c_C − γ₀)/(γ₁ − γ₀)`, hence `ρ`
and `δ_L` separately when `γ₁ ≠ γ₀`")
Kind: P
Fidelity: exact
Hyps: none -/
theorem ident_rho_sep (P' : DlParams K) {p₁ p₂ : K} (h10 : 0 ≤ p₁) (h11 : p₁ ≤ 1)
    (h20 : 0 ≤ p₂) (h21 : p₂ ≤ 1) (hne : p₁ ≠ p₂) (e₁ : P.obs p₁ = P'.obs p₁)
    (e₂ : P.obs p₂ = P'.obs p₂) (hγ : P.γ₁ ≠ P.γ₀) :
    P.ρ = P'.ρ ∧ P.δL = P'.δL := by
  obtain ⟨hρδ, hρAδA, hκ, hγ₁, hγ₀, hcC⟩ := P.ident_two_labels P' h10 h11 h20 h21 hne e₁ e₂
  -- `κ c_C − κγ₀ = ρ(1 − δL)(γ₁ − γ₀)` on both sides
  have h1 := P.kcC_sub_kappa_mul
  have h2 := P'.kcC_sub_kappa_mul
  have hkc : P.kcC = P'.kcC := by
    have := hcC; unfold cC at this
    rw [hκ] at this
    exact (div_left_inj' P'.kappa_pos.ne').mp this
  have hγ' : P.γ₁ - P.γ₀ ≠ 0 := sub_ne_zero.mpr hγ
  have hρ1 : P.ρ * (1 - P.δL) = P'.ρ * (1 - P'.δL) := by
    have e : P.kcC - P.kappa * P.γ₀ = P'.kcC - P'.kappa * P'.γ₀ := by rw [hkc, hκ, hγ₀]
    rw [h1, h2, hγ₁, hγ₀] at e
    have hγ'' : P'.γ₁ - P'.γ₀ ≠ 0 := by rw [← hγ₁, ← hγ₀]; exact hγ'
    exact mul_right_cancel₀ hγ'' e
  have hρ : P.ρ = P'.ρ := by linarith
  refine ⟨hρ, ?_⟩
  have : P.ρ * P.δL = P.ρ * P'.δL := by rw [hρδ, hρ]
  exact mul_left_cancel₀ P.ρ_pos.ne' this

/-- The session parameters with `(ρA, δA) = (1/20, 1/10)` in place of `(1/10, 1/20)` (same
product). Source: [[iv-design-draw-as-instrument]] §2 (B2). Kind: D -/
def sessPSwap : DlParams ℚ where
  ρ := 1/10
  ρA := 1/20
  δL := 1/20
  δA := 1/10
  γ₁ := 3/5
  γ₀ := 1/20
  α := 1
  β := 10
  ρ_pos := by norm_num
  ρA_pos := by norm_num
  ρ_add_ρA_lt_one := by norm_num
  δL_pos := by norm_num
  δL_le_one := by norm_num
  δA_pos := by norm_num
  δA_le_one := by norm_num
  γ₀_nonneg := by norm_num
  γ₀_le_γ₁ := by norm_num
  γ₁_le_one := by norm_num
  α_pos := by norm_num
  β_pos := by norm_num

/-- **`ρA` and `δA` are identified only as a product**: the observables depend on `(ρA, δA)`
through `ρAδA` alone. Witness: at the session parameters, `(ρA, δA) = (1/10, 1/20)` and
`(1/20, 1/10)` give the same `obs` at every label.
Source: [[iv-design-draw-as-instrument]] §2 (B2) ("`ρ_A` and `δ_A` only as a product unless
`δ_A = δ_L` is assumed")
Kind: N+
Fidelity: exact -/
theorem ident_rhoA_not_separately :
    ∃ P₁ P₂ : DlParams ℚ, P₁.ρA ≠ P₂.ρA ∧ P₁.δA ≠ P₂.δA ∧
      ∀ p : ℚ, 0 ≤ p → p ≤ 1 → P₁.obs p = P₂.obs p := by
  refine ⟨sessP, sessPSwap, by norm_num [sessP, sessPSwap], by norm_num [sessP, sessPSwap],
    fun p h0 h1 => ?_⟩
  rw [DlParams.ident_affine _ p h0 h1, DlParams.ident_affine _ p h0 h1]
  simp only [sessP, sessPSwap, kappa, kcC]
  norm_num

/-- **(c) One label identifies nothing**: for every `P` and every `p ∈ [0, 1]` there is a
forcing-free **recorded** tree — `dp-smoking-lesion`'s `slOneCausal` (lesion absent, cancer
`Bern(κ_m)` after the act, which records at `d` for every procedure) — and a label `p'` giving
the same three observables: `p' := ρδL + κp`, `κ₁ := P_p(k | m=1)`, `κ₀ := P_p(k | m=0)`.
"Smoking causes cancer" fits one label's record exactly.
Source: [[iv-design-draw-as-instrument]] §2 (B2) ("At **one** policy the pooled record is three
numbers, fitted exactly by 'smoking causes cancer' — nothing is identified")
Kind: P
Fidelity: exact (at `K := ℚ`, the carrier of `slOneCausal`)
Hyps: none -/
theorem ident_one_label_nothing (P : DlParams ℚ) (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ∃ (κ₁ : ℚ) (k10 : 0 ≤ κ₁) (k11 : κ₁ ≤ 1) (κ₀ : ℚ) (k00 : 0 ≤ κ₀) (k01 : κ₀ ≤ 1)
      (p' : ℚ) (h0' : 0 ≤ p') (h1' : p' ≤ 1),
      let T := Cleanroom.Decision.DpSmokingLesion.slOneCausal κ₁ k10 k11 κ₀ k00 k01 P.α P.β
      RecordsFor Cleanroom.Decision.DpSmokingLesion.slObs
        Cleanroom.Decision.DpSmokingLesion.slActEv (procBool p' h0' h1') T () ∧
      P.obs p = (nu (procBool p' h0' h1') T (Cleanroom.Found.DpCoreTree.evM true),
        nu (procBool p' h0' h1') T
          (Cleanroom.Found.DpCoreTree.evK ∩ Cleanroom.Found.DpCoreTree.evM true),
        nu (procBool p' h0' h1') T
          (Cleanroom.Found.DpCoreTree.evK ∩ Cleanroom.Found.DpCoreTree.evM false)) := by
  have hs := P.nuP_smoke_pos p h0 h1
  have ha := P.nuP_abstain_pos p h0 h1
  have hks : P.nuP p (evCancer ∩ evSmoke) ≤ P.nuP p evSmoke := by
    rw [P.nuP_eq h0 h1, P.nuP_eq h0 h1]
    exact nu_mono _ _ Finset.inter_subset_right
  have hka : P.nuP p (evCancer ∩ evAbstain) ≤ P.nuP p evAbstain := by
    rw [P.nuP_eq h0 h1, P.nuP_eq h0 h1]
    exact nu_mono _ _ Finset.inter_subset_right
  have hks0 : 0 ≤ P.nuP p (evCancer ∩ evSmoke) := by rw [P.nuP_eq h0 h1]; exact nu_nonneg _ _ _
  have hka0 : 0 ≤ P.nuP p (evCancer ∩ evAbstain) := by
    rw [P.nuP_eq h0 h1]; exact nu_nonneg _ _ _
  have hsum : P.nuP p evSmoke + P.nuP p evAbstain = 1 := by
    rw [nuP_smoke P p h0 h1, nuP_abstain P p h0 h1]; unfold kappa; ring
  refine ⟨P.nuP p (evCancer ∩ evSmoke) / P.nuP p evSmoke, div_nonneg hks0 hs.le,
    (div_le_one hs).mpr hks, P.nuP p (evCancer ∩ evAbstain) / P.nuP p evAbstain,
    div_nonneg hka0 ha.le, (div_le_one ha).mpr hka, P.nuP p evSmoke,
    hs.le, by linarith, ?_, ?_⟩
  · exact Cleanroom.Decision.DpSmokingLesion.slOneCausal_recordsFor _ _ _ _ _ _ _ _ _
  · obtain ⟨hm, hkm⟩ := Cleanroom.Decision.DpSmokingLesion.slOneCausal_nu_values
      (P.nuP p (evCancer ∩ evSmoke) / P.nuP p evSmoke) (div_nonneg hks0 hs.le)
      ((div_le_one hs).mpr hks) (P.nuP p (evCancer ∩ evAbstain) / P.nuP p evAbstain)
      (div_nonneg hka0 ha.le) ((div_le_one ha).mpr hka) P.α P.β
      (procBool (P.nuP p evSmoke) hs.le (by linarith))
    simp only [obs]
    rw [hm true, hkm true, hkm false]
    simp only [procBool, FinDistr.bool_true, FinDistr.bool_false, if_true, Bool.false_eq_true,
      if_false]
    rw [mul_div_cancel₀ _ hs.ne']
    have : 1 - P.nuP p evSmoke = P.nuP p evAbstain := by linarith
    rw [this, mul_div_cancel₀ _ ha.ne']

/-- **(d) Bypass and overwrite are indistinguishable at every finite set of labels** (`oneLaw`
restated): the pooled `(m, world)` statistics agree at every label in a list.
Source: [[iv-design-draw-as-instrument]] §5 (the channel table: "the 2a/2b distinction no — same
run law at every `p`")
Kind: L (a restatement of `oneLaw`)
Fidelity: exact -/
theorem channel_bypass_overwrite_indist (ps : List K) :
    ∀ p ∈ ps, ∀ (h0 : 0 ≤ p) (h1 : p ≤ 1) (X : Finset DlW),
      nu (procBoolK p h0 h1) P.bypass X = nu (procBoolK p h0 h1) P.overwrite X :=
  fun p _ h0 h1 X => P.oneLaw p h0 h1 X

end DlParams

end Cleanroom.Decision.DpTwoLesions

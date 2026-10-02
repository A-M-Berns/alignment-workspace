import Cleanroom.Bli.UdtBliCore.Product

/-!
# `udt-bli-core` · ProductUtil: value formulas on independent-policy priors with a product
policy law

For `D : IndepData` whose policy law is a product law `prodLaw g`, the derived values reduce to
sums over the base outcome space for the two utility shapes the witnesses use:

* **home-only** utilities `U₀ ω₀ π = f ω₀ (π (state₀ ω₀))` (the utility reads the policy only
  at the branch that obtains): `homeEU T a = 𝔼_{μ₀}[f · a | state₀ = T]`, the other branches'
  expectations do not depend on the point (`NoCrossBranch`), and `cellEU T π` depends on `π`
  only through `π T` (`LocalUtility`);
* **single-point** utilities `U₀ ω₀ π = u ω₀ (π T₀)` (the utility reads one fixed policy point,
  as in the mugging): `EU T₀ a = ∑ μ₀ · u · a`, `condEU T' T₀ a = 𝔼_{μ₀}[u · a | state₀ = T']`,
  `exAnteValue π = ∑ μ₀ · u · (π T₀)`.
-/

namespace Cleanroom.Bli.UdtBliCore

open Cleanroom.Bli.BliFinite Finset

namespace IndepData

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [Fintype A] [DecidableEq A]
variable (D : IndepData 𝒮 m 𝒟 A)

/-- The integral of the utility over a rectangle, as an iterated sum.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma integralOf_U_rect (E₀ : D.Ω₀ → Prop) [DecidablePred E₀] (F : Policy 𝒟 A → Prop)
    [DecidablePred F] :
    integralOf D.μ (fun ω => D.U₀ ω.1 ω.2) (fun ω => E₀ ω.1 ∧ F ω.2) =
      ∑ ω₀, if E₀ ω₀ then D.μ₀ ω₀ * ∑ π, (if F π then D.ν π * D.U₀ ω₀ π else 0) else 0 := by
  unfold integralOf
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω₀ _
  by_cases h₀ : E₀ ω₀
  · simp only [h₀, true_and, if_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro π _
    by_cases hF : F π <;> simp [μ, hF, mul_assoc]
  · simp [h₀]

/-- The utility integral over `state₀ = T' ∧ π T = a` for a utility given by `w : Ω₀ → Policy → ℚ`
on the cell, under a product law: the policy sum is `∑_π prodLaw g π · [π T = a] · w ω₀ π`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jointUtil_toPrior (T' T : ↥𝒟) (a : A) :
    D.toPrior.jointUtil T' T a =
      ∑ ω₀, if D.state₀ ω₀ = T' then
        D.μ₀ ω₀ * ∑ π, (if π T = a then D.ν π * D.U₀ ω₀ π else 0) else 0 :=
  D.integralOf_U_rect (fun ω₀ => D.state₀ ω₀ = T') (fun π => π T = a)

/-- The utility integral over a whole policy: `cellUtil T π = ∑_{state₀ = T} μ₀ · ν π · U₀ ω₀ π`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellUtil_toPrior (T : ↥𝒟) (π : Policy 𝒟 A) :
    D.toPrior.cellUtil T π =
      ∑ ω₀, if D.state₀ ω₀ = T then D.μ₀ ω₀ * (D.ν π * D.U₀ ω₀ π) else 0 := by
  have := D.integralOf_U_rect (fun ω₀ => D.state₀ ω₀ = T) (fun π' => π' = π)
  change integralOf D.μ (fun ω => D.U₀ ω.1 ω.2) (fun ω => D.state₀ ω.1 = T ∧ ω.2 = π) = _
  rw [this]
  apply Finset.sum_congr rfl
  intro ω₀ _
  by_cases h : D.state₀ ω₀ = T
  · simp [h]
  · simp [h]

/-- The utility integral over a policy point: `ppUtil T a = ∑_{ω₀} μ₀ · ∑_π [π T = a] ν π U₀ ω₀ π`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ppUtil_toPrior (T : ↥𝒟) (a : A) :
    D.toPrior.ppUtil T a =
      ∑ ω₀, D.μ₀ ω₀ * ∑ π, (if π T = a then D.ν π * D.U₀ ω₀ π else 0) := by
  have := D.integralOf_U_rect (fun _ => True) (fun π => π T = a)
  simp only [true_and, if_true] at this
  exact this

/-- The utility integral over a whole policy without the state: `policyUtil π = ν π · ∑ μ₀ · U₀ · π`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyUtil_toPrior (π : Policy 𝒟 A) :
    D.toPrior.policyUtil π = D.ν π * ∑ ω₀, D.μ₀ ω₀ * D.U₀ ω₀ π := by
  have := D.integralOf_U_rect (fun _ => True) (fun π' => π' = π)
  simp only [true_and, if_true] at this
  change integralOf D.μ (fun ω => D.U₀ ω.1 ω.2) (fun ω => ω.2 = π) = _
  rw [this, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω₀ _
  rw [Finset.sum_eq_single π]
  · simp; ring
  · intro π' _ hne; simp [hne]
  · intro habs; exact absurd (Finset.mem_univ _) habs

/-- **Single-point utility: the cell value** is the base's conditional expectation of
`u · (π T₀)` on the branch, at every positive policy.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellEU_single (T₀ : ↥𝒟) (u : D.Ω₀ → A → ℚ) (hU : ∀ ω₀ π, D.U₀ ω₀ π = u ω₀ (π T₀))
    (T : ↥𝒟) (π : Policy 𝒟 A) (hπ : 0 < D.ν π) :
    D.toPrior.cellEU T π = condExp D.μ₀ (fun ω₀ => u ω₀ (π T₀)) (fun ω₀ => D.state₀ ω₀ = T) := by
  unfold FiniteBLIPrior.cellEU condExp
  change D.toPrior.cellUtil T π / D.toPrior.cellMass T π = _
  rw [D.cellUtil_toPrior, D.cellMass_toPrior]
  unfold integralOf
  have e : (∑ ω₀, if D.state₀ ω₀ = T then D.μ₀ ω₀ * (D.ν π * D.U₀ ω₀ π) else 0) =
      D.ν π * ∑ ω₀, if D.state₀ ω₀ = T then D.μ₀ ω₀ * u ω₀ (π T₀) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω₀ _
    by_cases h : D.state₀ ω₀ = T
    · simp only [h, if_true, hU]; ring
    · simp [h]
  rw [e, mul_comm (massOf _ _) (D.ν π), mul_div_mul_left _ _ (ne_of_gt hπ)]

section ProdLaw

variable (g : ↥𝒟 → A → ℚ) (hg1 : ∀ T, ∑ a, g T a = 1) (hν : D.ν = prodLaw g)
include hg1 hν

/-! ### Home-only utilities -/

/-- **Home-only utility, home cell**: `jointUtil T T a = g T a · ∫_{state₀ = T} f · a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jointUtil_home_self (f : D.Ω₀ → A → ℚ)
    (hU : ∀ ω₀ π, D.U₀ ω₀ π = f ω₀ (π (D.state₀ ω₀))) (T : ↥𝒟) (a : A) :
    D.toPrior.jointUtil T T a =
      g T a * integralOf D.μ₀ (fun ω₀ => f ω₀ a) (fun ω₀ => D.state₀ ω₀ = T) := by
  rw [D.jointUtil_toPrior]
  unfold integralOf
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω₀ _
  by_cases h : D.state₀ ω₀ = T
  · simp only [h, if_true, hU, hν]
    have e : ∀ π : Policy 𝒟 A, (if π T = a then prodLaw g π * f ω₀ (π T) else 0) =
        prodLaw g π * (if π T = a then f ω₀ (π T) else 0) := by
      intro π; by_cases hp : π T = a <;> simp [hp]
    simp only [e]
    rw [sum_prodLaw_mul_fun hg1 T (fun j => if j = a then f ω₀ j else 0)]
    rw [Finset.sum_eq_single a]
    · simp; ring
    · intro b _ hb; simp [hb]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  · simp [h]

/-- **Home-only utility, other cells**: for `T' ≠ T`,
`jointUtil T' T a = g T a · ∫_{state₀ = T'} (∑_b g T' b · f · b)` — no dependence on `a` beyond the
factor `g T a` that the mass also carries.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jointUtil_home_other (f : D.Ω₀ → A → ℚ)
    (hU : ∀ ω₀ π, D.U₀ ω₀ π = f ω₀ (π (D.state₀ ω₀))) (T' T : ↥𝒟) (hne : T ≠ T') (a : A) :
    D.toPrior.jointUtil T' T a =
      g T a * integralOf D.μ₀ (fun ω₀ => ∑ b, g T' b * f ω₀ b) (fun ω₀ => D.state₀ ω₀ = T') := by
  rw [D.jointUtil_toPrior]
  unfold integralOf
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω₀ _
  by_cases h : D.state₀ ω₀ = T'
  · simp only [h, if_true, hU, hν]
    have e : ∀ π : Policy 𝒟 A, (if π T = a then prodLaw g π * f ω₀ (π T') else 0) =
        prodLaw g π * (if π T = a then f ω₀ (π T') else 0) := by
      intro π; by_cases hp : π T = a <;> simp [hp]
    simp only [e]
    rw [sum_prodLaw_mul_fun₂ hg1 hne (fun j₀ j₁ => if j₀ = a then f ω₀ j₁ else 0)]
    rw [Finset.sum_eq_single a]
    · simp only [if_true, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    · intro b _ hb; simp [hb]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  · simp [h]

/-- **Home-only utility: the updateful value is the base's conditional expectation**
`homeEU T a = 𝔼_{μ₀}[f · a | state₀ = T]` (at a positive point weight `g T a`).
Source: mandate T2 (the tent prior's updateful values are the table's own expectations)
Kind: L
Fidelity: n/a -/
lemma homeEU_home (f : D.Ω₀ → A → ℚ) (hU : ∀ ω₀ π, D.U₀ ω₀ π = f ω₀ (π (D.state₀ ω₀)))
    (T : ↥𝒟) (a : A) (hg : 0 < g T a) :
    D.toPrior.homeEU T a = condExp D.μ₀ (fun ω₀ => f ω₀ a) (fun ω₀ => D.state₀ ω₀ = T) := by
  unfold FiniteBLIPrior.homeEU FiniteBLIPrior.condEU condExp
  change D.toPrior.jointUtil T T a / D.toPrior.jointMass T T a = _
  rw [D.jointUtil_home_self g hg1 hν f hU T a, D.jointMass_toPrior, hν,
    massOf_prodLaw_point g hg1]
  rw [mul_comm (massOf _ _) (g T a), mul_div_mul_left _ _ (ne_of_gt hg)]

/-- **Home-only utility: `NoCrossBranch` holds** (with a product policy law): the other branches'
expectations do not depend on the point at `T`.
Source: mandate T2 (the tent prior is `NoCrossBranch`)
Kind: P
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem noCrossBranch_home (f : D.Ω₀ → A → ℚ)
    (hU : ∀ ω₀ π, D.U₀ ω₀ π = f ω₀ (π (D.state₀ ω₀))) : D.toPrior.NoCrossBranch := by
  intro T T' a b hne hpa hpb
  have hne' : T ≠ T' := fun h => hne h.symm
  unfold FiniteBLIPrior.condEU condExp
  change D.toPrior.jointUtil T' T a / D.toPrior.jointMass T' T a =
    D.toPrior.jointUtil T' T b / D.toPrior.jointMass T' T b
  rw [D.jointUtil_home_other g hg1 hν f hU T' T hne' a, D.jointUtil_home_other g hg1 hν f hU T' T hne' b,
    D.jointMass_toPrior, D.jointMass_toPrior, hν,
    massOf_prodLaw_point g hg1, massOf_prodLaw_point g hg1]
  have hga : 0 < g T a := by
    rw [D.jointMass_toPrior, hν, massOf_prodLaw_point g hg1] at hpa
    exact pos_of_mul_pos_right hpa (massOf_nonneg _ D.μ₀_nonneg _)
  have hgb : 0 < g T b := by
    rw [D.jointMass_toPrior, hν, massOf_prodLaw_point g hg1] at hpb
    exact pos_of_mul_pos_right hpb (massOf_nonneg _ D.μ₀_nonneg _)
  rw [mul_comm (massOf _ _) (g T a), mul_div_mul_left _ _ (ne_of_gt hga),
    mul_comm (massOf _ _) (g T b), mul_div_mul_left _ _ (ne_of_gt hgb)]

/-- **Home-only utility: `cellEU T π` depends on `π` only through `π T`** — the cell value is
`𝔼_{μ₀}[f · (π T) | state₀ = T]` at every positive policy.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellEU_home (f : D.Ω₀ → A → ℚ) (hU : ∀ ω₀ π, D.U₀ ω₀ π = f ω₀ (π (D.state₀ ω₀)))
    (T : ↥𝒟) (π : Policy 𝒟 A) (hπ : 0 < D.ν π) :
    D.toPrior.cellEU T π = condExp D.μ₀ (fun ω₀ => f ω₀ (π T)) (fun ω₀ => D.state₀ ω₀ = T) := by
  unfold FiniteBLIPrior.cellEU condExp
  change D.toPrior.cellUtil T π / D.toPrior.cellMass T π = _
  rw [D.cellUtil_toPrior, D.cellMass_toPrior]
  unfold integralOf
  have e : (∑ ω₀, if D.state₀ ω₀ = T then D.μ₀ ω₀ * (D.ν π * D.U₀ ω₀ π) else 0) =
      D.ν π * ∑ ω₀, if D.state₀ ω₀ = T then D.μ₀ ω₀ * f ω₀ (π T) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω₀ _
    by_cases h : D.state₀ ω₀ = T
    · simp only [h, if_true, hU]; ring
    · simp [h]
  rw [e, mul_comm (massOf _ _) (D.ν π), mul_div_mul_left _ _ (ne_of_gt hπ)]

/-- **Home-only utility: `LocalUtility` holds.**
Source: bli-soto-b-2-016 (T1) (the tree-without-entanglement condition, satisfied by construction)
Kind: P
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem localUtility_home (f : D.Ω₀ → A → ℚ)
    (hU : ∀ ω₀ π, D.U₀ ω₀ π = f ω₀ (π (D.state₀ ω₀))) : D.toPrior.LocalUtility := by
  intro T π π' he hπ hπ'
  have hνπ : 0 < D.ν π := by
    rw [D.cellMass_toPrior] at hπ
    exact pos_of_mul_pos_right hπ (massOf_nonneg _ D.μ₀_nonneg _)
  have hνπ' : 0 < D.ν π' := by
    rw [D.cellMass_toPrior] at hπ'
    exact pos_of_mul_pos_right hπ' (massOf_nonneg _ D.μ₀_nonneg _)
  rw [D.cellEU_home g hg1 hν f hU T π hνπ, D.cellEU_home g hg1 hν f hU T π' hνπ', he]

/-! ### Single-point utilities -/

/-- **Single-point utility: the one-step value at the read point** is the full base expectation
of `u · a`: `EU T₀ a = ∑_{ω₀} μ₀ ω₀ · u ω₀ a` (at a positive point weight).
Source: bli-slides-034 (`𝔼_0(u | give-on-Ask) = 0.49·(−10) + 0.49·100`)
Kind: L
Fidelity: n/a -/
lemma EU_single (T₀ : ↥𝒟) (u : D.Ω₀ → A → ℚ) (hU : ∀ ω₀ π, D.U₀ ω₀ π = u ω₀ (π T₀)) (a : A)
    (hg : 0 < g T₀ a) :
    D.toPrior.EU T₀ a = ∑ ω₀, D.μ₀ ω₀ * u ω₀ a := by
  unfold FiniteBLIPrior.EU condExp
  change D.toPrior.ppUtil T₀ a / D.toPrior.ppMass T₀ a = _
  rw [D.ppUtil_toPrior, D.ppMass_toPrior, hν, massOf_prodLaw_point g hg1]
  have e : ∀ ω₀, (∑ π, if π T₀ = a then prodLaw g π * D.U₀ ω₀ π else 0) = g T₀ a * u ω₀ a := by
    intro ω₀
    have e' : ∀ π : Policy 𝒟 A, (if π T₀ = a then prodLaw g π * D.U₀ ω₀ π else 0) =
        prodLaw g π * (if π T₀ = a then u ω₀ (π T₀) else 0) := by
      intro π; by_cases hp : π T₀ = a <;> simp [hp, hU]
    simp only [e']
    rw [sum_prodLaw_mul_fun hg1 T₀ (fun j => if j = a then u ω₀ j else 0)]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [hb]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  simp only [e]
  rw [div_eq_iff (ne_of_gt hg), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω₀ _
  ring

/-- **Single-point utility: the branch value at the read point** is the base's conditional
expectation of `u · a` on the branch: `condEU T' T₀ a = 𝔼_{μ₀}[u · a | state₀ = T']`.
Source: bli-soto-a-077 (the branch beliefs of the mugging), via bli-slides-034
Kind: L
Fidelity: n/a -/
lemma condEU_single (T₀ : ↥𝒟) (u : D.Ω₀ → A → ℚ) (hU : ∀ ω₀ π, D.U₀ ω₀ π = u ω₀ (π T₀))
    (T' : ↥𝒟) (a : A) (hg : 0 < g T₀ a) :
    D.toPrior.condEU T' T₀ a = condExp D.μ₀ (fun ω₀ => u ω₀ a) (fun ω₀ => D.state₀ ω₀ = T') := by
  unfold FiniteBLIPrior.condEU condExp
  change D.toPrior.jointUtil T' T₀ a / D.toPrior.jointMass T' T₀ a = _
  rw [D.jointUtil_toPrior, D.jointMass_toPrior, hν, massOf_prodLaw_point g hg1]
  have e : ∀ ω₀, (∑ π, if π T₀ = a then prodLaw g π * D.U₀ ω₀ π else 0) = g T₀ a * u ω₀ a := by
    intro ω₀
    have e' : ∀ π : Policy 𝒟 A, (if π T₀ = a then prodLaw g π * D.U₀ ω₀ π else 0) =
        prodLaw g π * (if π T₀ = a then u ω₀ (π T₀) else 0) := by
      intro π; by_cases hp : π T₀ = a <;> simp [hp, hU]
    simp only [e']
    rw [sum_prodLaw_mul_fun hg1 T₀ (fun j => if j = a then u ω₀ j else 0)]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [hb]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  simp only [e]
  unfold integralOf
  have e2 : (∑ ω₀, if D.state₀ ω₀ = T' then D.μ₀ ω₀ * (g T₀ a * u ω₀ a) else 0) =
      g T₀ a * ∑ ω₀, if D.state₀ ω₀ = T' then D.μ₀ ω₀ * u ω₀ a else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω₀ _
    by_cases h : D.state₀ ω₀ = T' <;> simp [h] <;> ring
  rw [e2, mul_comm (massOf _ _) (g T₀ a), mul_div_mul_left _ _ (ne_of_gt hg)]

/-- **Single-point utility: the ex-ante value of a policy** is `∑_{ω₀} μ₀ ω₀ · u ω₀ (π T₀)` at
every positive policy.
Source: bli-slides-034
Kind: L
Fidelity: n/a -/
lemma exAnteValue_single (T₀ : ↥𝒟) (u : D.Ω₀ → A → ℚ)
    (hU : ∀ ω₀ π, D.U₀ ω₀ π = u ω₀ (π T₀)) (π : Policy 𝒟 A) (hπ : 0 < D.ν π) :
    D.toPrior.exAnteValue π = ∑ ω₀, D.μ₀ ω₀ * u ω₀ (π T₀) := by
  unfold FiniteBLIPrior.exAnteValue condExp
  change D.toPrior.policyUtil π / D.toPrior.policyMass π = _
  rw [D.policyUtil_toPrior, D.policyMass_toPrior, mul_div_cancel_left₀ _ (ne_of_gt hπ)]
  apply Finset.sum_congr rfl
  intro ω₀ _
  rw [hU]

end ProdLaw

end IndepData

end Cleanroom.Bli.UdtBliCore

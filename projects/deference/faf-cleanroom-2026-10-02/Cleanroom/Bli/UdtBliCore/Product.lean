import Cleanroom.Bli.UdtBliCore.Basic

/-!
# `udt-bli-core` · Product: product laws on policies and the independent-policy constructor

Two pieces of infrastructure every witness of this package is built from.

1. **Product laws** `prodLaw g x := ∏ i, g i (x i)` on a finite function type `ι → κ`, with the
   Fubini identity (`Fintype.prod_sum`) turned into the marginal lemmas that make every sum over
   the `2^|𝒟|` (or `|A|^|𝒟|`) policies symbolic: the one-coordinate marginal is `g i₀ ·`, two
   distinct coordinates are independent.
2. **`IndepData`**: a base finite prior `(Ω₀, μ₀, state₀, small₀)` with faith, a law `ν` on
   policies, and a utility `U₀ : Ω₀ → Policy → ℚ`. `IndepData.toPrior` puts them together on
   `Ω₀ × Policy` with `μ (ω₀, π) = μ₀ ω₀ · ν π` and `pp (ω₀, π) = π`. **By construction** such a
   prior is `Reflective`, `ReflectivePolicy` and `FaithGivenPoints` (the policy coordinate is
   independent of the state and the world), and it is `IndependentPoints` when `ν` is a product
   law. Every cross-branch influence in such a prior is carried by `U₀` alone — that is the
   disclosed modelling scope of `ofSkeleton` (T2) and of the mugging prior (T3); priors where
   policy points *move branch probabilities* are hand-built separately (`WitnessCorr.lean`).
-/

namespace Cleanroom.Bli.UdtBliCore

open Cleanroom.Bli.BliFinite Finset

/-! ## Product laws on finite function types -/

section ProdLaw

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The product law with coordinate weights `g`: `prodLaw g x := ∏ i, g i (x i)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def prodLaw (g : ι → κ → ℚ) (x : ι → κ) : ℚ := ∏ i, g i (x i)

/-- Product laws of nonnegative weights are nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prodLaw_nonneg {g : ι → κ → ℚ} (hg : ∀ i j, 0 ≤ g i j) (x : ι → κ) : 0 ≤ prodLaw g x :=
  Finset.prod_nonneg fun i _ => hg i (x i)

/-- Product laws of positive weights are positive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prodLaw_pos {g : ι → κ → ℚ} (hg : ∀ i j, 0 < g i j) (x : ι → κ) : 0 < prodLaw g x :=
  Finset.prod_pos fun i _ => hg i (x i)

/-- **Fubini for indicators**: summing the product law against the indicator that the coordinates
in `S` take prescribed values `v` gives the product of the prescribed weights.
Source: none: infrastructure
Kind: P
Fidelity: n/a
Hyps: (a) none -/
lemma sum_prodLaw_mul_prod_ind {g : ι → κ → ℚ} (hg1 : ∀ i, ∑ j, g i j = 1) (S : Finset ι)
    (v : ι → κ) :
    ∑ x : ι → κ, prodLaw g x * ∏ i ∈ S, (if x i = v i then (1 : ℚ) else 0) =
      ∏ i ∈ S, g i (v i) := by
  have h : ∀ x : ι → κ, prodLaw g x * ∏ i ∈ S, (if x i = v i then (1 : ℚ) else 0) =
      ∏ i, (g i (x i) * if i ∈ S then (if x i = v i then (1 : ℚ) else 0) else 1) := by
    intro x
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter]
    rfl
  simp only [h]
  rw [← Fintype.prod_sum (fun i j => g i j * if i ∈ S then (if j = v i then (1 : ℚ) else 0) else 1)]
  have hfac : ∀ i, (∑ j, g i j * if i ∈ S then (if j = v i then (1 : ℚ) else 0) else 1) =
      if i ∈ S then g i (v i) else 1 := by
    intro i
    by_cases hi : i ∈ S
    · simp only [hi, if_true]
      rw [Finset.sum_eq_single (v i)]
      · simp
      · intro j _ hj; simp [hj]
      · intro habs; exact absurd (Finset.mem_univ _) habs
    · simp only [hi, if_false, mul_one]
      exact hg1 i
  simp only [hfac]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

/-- **One-coordinate marginal**: `∑_x prodLaw g x · [x i₀ = j₀] = g i₀ j₀`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_prodLaw_mul_ind {g : ι → κ → ℚ} (hg1 : ∀ i, ∑ j, g i j = 1) (i₀ : ι) (j₀ : κ) :
    ∑ x : ι → κ, prodLaw g x * (if x i₀ = j₀ then (1 : ℚ) else 0) = g i₀ j₀ := by
  have := sum_prodLaw_mul_prod_ind hg1 {i₀} (fun _ => j₀)
  simpa using this

/-- **Two-coordinate marginal**: distinct coordinates of a product law are independent.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_prodLaw_mul_ind₂ {g : ι → κ → ℚ} (hg1 : ∀ i, ∑ j, g i j = 1) {i₀ i₁ : ι}
    (hne : i₀ ≠ i₁) (j₀ j₁ : κ) :
    ∑ x : ι → κ, prodLaw g x * ((if x i₀ = j₀ then (1 : ℚ) else 0) *
      (if x i₁ = j₁ then (1 : ℚ) else 0)) = g i₀ j₀ * g i₁ j₁ := by
  have := sum_prodLaw_mul_prod_ind hg1 {i₀, i₁} (fun i => if i = i₀ then j₀ else j₁)
  simp only [Finset.prod_pair hne, eq_self_iff_true, if_true, Ne.symm hne, if_false] at this
  exact this

/-- The product law sums to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_prodLaw {g : ι → κ → ℚ} (hg1 : ∀ i, ∑ j, g i j = 1) :
    ∑ x : ι → κ, prodLaw g x = 1 := by
  unfold prodLaw
  rw [← Fintype.prod_sum g]
  simp [hg1]

/-- **Marginalizing a one-coordinate function**: `∑_x prodLaw g x · F (x i₀) = ∑_j g i₀ j · F j`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_prodLaw_mul_fun {g : ι → κ → ℚ} (hg1 : ∀ i, ∑ j, g i j = 1) (i₀ : ι) (F : κ → ℚ) :
    ∑ x : ι → κ, prodLaw g x * F (x i₀) = ∑ j, g i₀ j * F j := by
  have hF : ∀ x : ι → κ, F (x i₀) = ∑ j, (if x i₀ = j then (1 : ℚ) else 0) * F j := by
    intro x
    rw [Finset.sum_eq_single (x i₀)]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  simp only [hF, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← sum_prodLaw_mul_ind hg1 i₀ j, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- **Marginalizing a two-coordinate function** at distinct coordinates.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_prodLaw_mul_fun₂ {g : ι → κ → ℚ} (hg1 : ∀ i, ∑ j, g i j = 1) {i₀ i₁ : ι}
    (hne : i₀ ≠ i₁) (F : κ → κ → ℚ) :
    ∑ x : ι → κ, prodLaw g x * F (x i₀) (x i₁) = ∑ j₀, ∑ j₁, g i₀ j₀ * g i₁ j₁ * F j₀ j₁ := by
  have hF : ∀ x : ι → κ, F (x i₀) (x i₁) = ∑ j₀, ∑ j₁,
      ((if x i₀ = j₀ then (1 : ℚ) else 0) * (if x i₁ = j₁ then (1 : ℚ) else 0)) * F j₀ j₁ := by
    intro x
    rw [Finset.sum_eq_single (x i₀)]
    · rw [Finset.sum_eq_single (x i₁)]
      · simp
      · intro j _ hj; simp [Ne.symm hj]
      · intro habs; exact absurd (Finset.mem_univ _) habs
    · intro j _ hj; simp [Ne.symm hj]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  simp only [hF, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j₀ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j₁ _
  rw [← sum_prodLaw_mul_ind₂ hg1 hne j₀ j₁, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

end ProdLaw

/-! ## The independent-policy constructor -/

/-- **Data for a prior whose policy coordinate is independent of everything else**: a base finite
prior with a state and a world coordinate satisfying faith, a law `ν` on whole policies, and a
utility that may read both the base outcome and the whole policy (so cross-branch utility
influence is representable; cross-branch *probability* influence is not — disclosed).
Source: [[bli-program]] §2.8 (`ofSkeleton` = `trajLaw ⊗ …`), mandate T2 ("`× Policy` if you want
the policy coordinate explicit")
Kind: D
Fidelity: variant: the policy coordinate is independent of the state by construction -/
structure IndepData (𝒮 : SmallIndex) (m : ℕ) (𝒟 : Finset (Table 𝒮 m)) (A : Type) [Fintype A]
    [DecidableEq A] where
  /-- The base outcome space. -/
  Ω₀ : Type
  [fin : Fintype Ω₀]
  /-- The base law. -/
  μ₀ : Ω₀ → ℚ
  /-- Nonnegativity of the base law. -/
  μ₀_nonneg : ∀ ω, 0 ≤ μ₀ ω
  /-- The base law has mass one. -/
  μ₀_sum_one : ∑ ω, μ₀ ω = 1
  /-- Which table obtains. -/
  state₀ : Ω₀ → ↥𝒟
  /-- The world's small truths. -/
  small₀ : Ω₀ → ↥(𝒮.S m) → Bool
  /-- Faith of the base. -/
  faith₀ : ∀ (T : ↥𝒟) (φ : ↥(𝒮.S m)),
    integralOf μ₀ (fun ω => ind (small₀ ω φ)) (fun ω => state₀ ω = T) =
      T.1 φ * massOf μ₀ (fun ω => state₀ ω = T)
  /-- The law on policies. -/
  ν : Policy 𝒟 A → ℚ
  /-- Nonnegativity of the policy law. -/
  ν_nonneg : ∀ π, 0 ≤ ν π
  /-- The policy law has mass one. -/
  ν_sum_one : ∑ π, ν π = 1
  /-- The utility, reading the base outcome and the whole policy. -/
  U₀ : Ω₀ → Policy 𝒟 A → ℚ

attribute [instance] IndepData.fin

namespace IndepData

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [Fintype A] [DecidableEq A]
variable (D : IndepData 𝒮 m 𝒟 A)

/-- The joint law `μ (ω₀, π) := μ₀ ω₀ · ν π`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def μ (ω : D.Ω₀ × Policy 𝒟 A) : ℚ := D.μ₀ ω.1 * D.ν ω.2

/-- A sum over the product space of a product function factorizes.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_prod_mul (f : D.Ω₀ → ℚ) (h : Policy 𝒟 A → ℚ) :
    ∑ ω : D.Ω₀ × Policy 𝒟 A, f ω.1 * h ω.2 = (∑ ω₀, f ω₀) * ∑ π, h π := by
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- The mass of a rectangle `E₀ × F` under `μ` is the product of the masses.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_rect (E₀ : D.Ω₀ → Prop) [DecidablePred E₀] (F : Policy 𝒟 A → Prop)
    [DecidablePred F] :
    massOf D.μ (fun ω => E₀ ω.1 ∧ F ω.2) = massOf D.μ₀ E₀ * massOf D.ν F := by
  unfold massOf
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro ω₀ _
  apply Finset.sum_congr rfl
  intro π _
  by_cases h₀ : E₀ ω₀ <;> by_cases hF : F π <;> simp [μ, h₀, hF]

/-- The integral of a product function over a rectangle factorizes.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma integralOf_rect (f : D.Ω₀ → ℚ) (h : Policy 𝒟 A → ℚ) (E₀ : D.Ω₀ → Prop)
    [DecidablePred E₀] (F : Policy 𝒟 A → Prop) [DecidablePred F] :
    integralOf D.μ (fun ω => f ω.1 * h ω.2) (fun ω => E₀ ω.1 ∧ F ω.2) =
      integralOf D.μ₀ f E₀ * integralOf D.ν h F := by
  unfold integralOf
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro ω₀ _
  apply Finset.sum_congr rfl
  intro π _
  by_cases h₀ : E₀ ω₀ <;> by_cases hF : F π <;> simp [μ, h₀, hF] <;> ring

/-- **The prior built from independent-policy data.** Faith is inherited from the base (the
policy coordinate integrates out).
Source: [[bli-program]] §2.8; mandate T2
Kind: D
Fidelity: variant: policy coordinate independent of the state (disclosed) -/
def toPrior : FiniteBLIPrior 𝒮 m 𝒟 A where
  Ω := D.Ω₀ × Policy 𝒟 A
  μ := D.μ
  μ_nonneg := fun ω => mul_nonneg (D.μ₀_nonneg ω.1) (D.ν_nonneg ω.2)
  μ_sum_one := by
    show ∑ ω : D.Ω₀ × Policy 𝒟 A, D.μ₀ ω.1 * D.ν ω.2 = 1
    rw [D.sum_prod_mul, D.μ₀_sum_one, D.ν_sum_one, one_mul]
  state := fun ω => D.state₀ ω.1
  pp := fun ω => ω.2
  U := fun ω => D.U₀ ω.1 ω.2
  small := fun ω => D.small₀ ω.1
  faith := by
    intro T φ
    have h1 := D.integralOf_rect (fun ω₀ => ind (D.small₀ ω₀ φ)) (fun _ => 1)
      (fun ω₀ => D.state₀ ω₀ = T) (fun _ => True)
    have h2 := D.massOf_rect (fun ω₀ => D.state₀ ω₀ = T) (fun _ => True)
    simp only [and_true, mul_one] at h1 h2
    have hν : massOf D.ν (fun _ => True) = 1 := by
      unfold massOf; simp [D.ν_sum_one]
    have hν' : integralOf D.ν (fun _ => (1 : ℚ)) (fun _ => True) = 1 := by
      rw [integralOf_const, hν, mul_one]
    change integralOf D.μ (fun ω => ind (D.small₀ ω.1 φ)) (fun ω => D.state₀ ω.1 = T) =
      T.1 φ * massOf D.μ (fun ω => D.state₀ ω.1 = T)
    rw [h1, h2, hν, hν', mul_one, mul_one]
    exact D.faith₀ T φ

/-! ### The derived masses of `toPrior` -/

/-- The state mass of `toPrior` is the base's.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateMass_toPrior (T : ↥𝒟) :
    D.toPrior.stateMass T = massOf D.μ₀ (fun ω₀ => D.state₀ ω₀ = T) := by
  have := D.massOf_rect (fun ω₀ => D.state₀ ω₀ = T) (fun _ => True)
  have hν : massOf D.ν (fun _ => True) = 1 := by unfold massOf; simp [D.ν_sum_one]
  simp only [and_true, hν, mul_one] at this
  exact this

/-- The policy-point mass of `toPrior` is `ν`'s.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ppMass_toPrior (T : ↥𝒟) (a : A) :
    D.toPrior.ppMass T a = massOf D.ν (fun π => π T = a) := by
  have := D.massOf_rect (fun _ => True) (fun π => π T = a)
  have hμ : massOf D.μ₀ (fun _ => True) = 1 := by unfold massOf; simp [D.μ₀_sum_one]
  simp only [true_and, hμ, one_mul] at this
  exact this

/-- The joint mass of `toPrior` factorizes.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jointMass_toPrior (T' T : ↥𝒟) (a : A) :
    D.toPrior.jointMass T' T a =
      massOf D.μ₀ (fun ω₀ => D.state₀ ω₀ = T') * massOf D.ν (fun π => π T = a) :=
  D.massOf_rect (fun ω₀ => D.state₀ ω₀ = T') (fun π => π T = a)

/-- The policy mass of `toPrior` is `ν`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyMass_toPrior (π : Policy 𝒟 A) : D.toPrior.policyMass π = D.ν π := by
  have := D.massOf_rect (fun _ => True) (fun π' => π' = π)
  have hμ : massOf D.μ₀ (fun _ => True) = 1 := by unfold massOf; simp [D.μ₀_sum_one]
  simp only [true_and, hμ, one_mul] at this
  change massOf D.μ (fun ω => ω.2 = π) = D.ν π
  rw [this]
  unfold massOf
  simp

/-- The cell mass of `toPrior` factorizes.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellMass_toPrior (T : ↥𝒟) (π : Policy 𝒟 A) :
    D.toPrior.cellMass T π = massOf D.μ₀ (fun ω₀ => D.state₀ ω₀ = T) * D.ν π := by
  have := D.massOf_rect (fun ω₀ => D.state₀ ω₀ = T) (fun π' => π' = π)
  change massOf D.μ (fun ω => D.state₀ ω.1 = T ∧ ω.2 = π) = _
  rw [this]
  congr 1
  unfold massOf
  simp

/-- The pair mass of `toPrior` is `ν`'s.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pairMass_toPrior (T T' : ↥𝒟) (a b : A) :
    D.toPrior.pairMass T T' a b = massOf D.ν (fun π => π T = a ∧ π T' = b) := by
  have := D.massOf_rect (fun _ => True) (fun π => π T = a ∧ π T' = b)
  have hμ : massOf D.μ₀ (fun _ => True) = 1 := by unfold massOf; simp [D.μ₀_sum_one]
  simp only [true_and, hμ, one_mul] at this
  exact this

/-- The triple mass of `toPrior` factorizes.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triMass_toPrior (S T T' : ↥𝒟) (a b : A) :
    D.toPrior.triMass S T T' a b =
      massOf D.μ₀ (fun ω₀ => D.state₀ ω₀ = S) * massOf D.ν (fun π => π T = a ∧ π T' = b) :=
  D.massOf_rect (fun ω₀ => D.state₀ ω₀ = S) (fun π => π T = a ∧ π T' = b)

/-! ### Structural predicates that hold by construction -/

/-- **`toPrior` is `Reflective`** for every base and every policy law: the policy coordinate is
independent of the state by construction. (This is the disclosed scope: an independent-policy
prior can never exhibit branch re-weighting.)
Source: mandate T2 (the tent prior is `Reflective`); [[bli-program]] §7 item 9
Kind: P
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem reflective_toPrior : D.toPrior.Reflective := by
  intro T T' a hpos
  rw [FiniteBLIPrior.branchProb, D.jointMass_toPrior, D.stateMass_toPrior]
  rw [D.ppMass_toPrior] at hpos ⊢
  rw [mul_div_assoc, div_self (ne_of_gt hpos), mul_one]

/-- **`toPrior` is `ReflectivePolicy`** for every base and every policy law.
Source: mandate T2; [[bli-program]] §7 item 9
Kind: P
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem reflectivePolicy_toPrior : D.toPrior.ReflectivePolicy := by
  intro T π hpos
  rw [D.cellMass_toPrior, D.stateMass_toPrior]
  rw [D.policyMass_toPrior] at hpos ⊢
  rw [mul_div_assoc, div_self (ne_of_gt hpos), mul_one]

/-- **`toPrior` is `FaithGivenPoints`**: faith survives conditioning on any policy point, because
the world coordinate is independent of the policy given the state.
Source: mandate T12 extension ("`FaithGivenPoints` derived when the world coordinate is
`μ`-independent of `pp` given `state`")
Kind: P
Fidelity: exact
Hyps: (a) none; uses the base's faith -/
theorem faithGivenPoints_toPrior : D.toPrior.FaithGivenPoints := by
  intro T T' a φ _
  have h1 := D.integralOf_rect (fun ω₀ => ind (D.small₀ ω₀ φ)) (fun _ => 1)
    (fun ω₀ => D.state₀ ω₀ = T) (fun π => π T' = a)
  simp only [mul_one] at h1
  rw [D.jointMass_toPrior]
  change integralOf D.μ (fun ω => ind (D.small₀ ω.1 φ)) (fun ω => D.state₀ ω.1 = T ∧ ω.2 T' = a) =
    T.1 φ * (massOf D.μ₀ (fun ω₀ => D.state₀ ω₀ = T) * massOf D.ν (fun π => π T' = a))
  rw [h1, D.faith₀ T φ, integralOf_const, one_mul]
  ring

/-- **`toPrior` is `IndependentPoints` when `ν` is a product law** (any coordinate weights
summing to one).
Source: [[bli-program-desiderata]] (I); mandate T7
Kind: P
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem independentPoints_toPrior_of_prodLaw (g : ↥𝒟 → A → ℚ) (hg1 : ∀ T, ∑ a, g T a = 1)
    (hν : D.ν = prodLaw g) : D.toPrior.IndependentPoints := by
  intro T T' a b hne
  rw [D.pairMass_toPrior, D.ppMass_toPrior, D.ppMass_toPrior, hν]
  unfold massOf
  have e1 : ∀ π : Policy 𝒟 A, (if π T = a ∧ π T' = b then prodLaw g π else 0) =
      prodLaw g π * ((if π T = a then (1 : ℚ) else 0) * (if π T' = b then (1 : ℚ) else 0)) := by
    intro π
    by_cases h1 : π T = a <;> by_cases h2 : π T' = b <;> simp [h1, h2]
  have e2 : ∀ (S : ↥𝒟) (c : A) (π : Policy 𝒟 A), (if π S = c then prodLaw g π else 0) =
      prodLaw g π * (if π S = c then (1 : ℚ) else 0) := by
    intro S c π
    by_cases h : π S = c <;> simp [h]
  simp only [e1, e2]
  rw [sum_prodLaw_mul_ind₂ hg1 hne, sum_prodLaw_mul_ind hg1, sum_prodLaw_mul_ind hg1]

/-- **`toPrior` is `IndependentPointsGivenState` when `ν` is a product law**.
Source: mandate T7
Kind: P
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem independentPointsGivenState_toPrior_of_prodLaw (g : ↥𝒟 → A → ℚ)
    (hg1 : ∀ T, ∑ a, g T a = 1) (hν : D.ν = prodLaw g) :
    D.toPrior.IndependentPointsGivenState := by
  intro S T T' a b hne
  have hI := D.independentPoints_toPrior_of_prodLaw g hg1 hν T T' a b hne
  rw [D.pairMass_toPrior, D.ppMass_toPrior, D.ppMass_toPrior] at hI
  rw [D.triMass_toPrior, D.stateMass_toPrior, D.jointMass_toPrior, D.jointMass_toPrior, hI]
  ring

/-- `NDPOL` for `toPrior` when every point has positive `ν`-mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ndpol_toPrior (h : ∀ T a, 0 < massOf D.ν (fun π => π T = a)) : D.toPrior.NDPOL := by
  intro T a; rw [D.ppMass_toPrior]; exact h T a

/-- `NDPOLICY` for `toPrior` when `ν` is positive everywhere.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ndpolicy_toPrior (h : ∀ π, 0 < D.ν π) : D.toPrior.NDPOLICY := by
  intro π; rw [D.policyMass_toPrior]; exact h π

/-- `NDHOME` for `toPrior` when every state and every point have positive mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ndhome_toPrior (hs : ∀ T, 0 < massOf D.μ₀ (fun ω₀ => D.state₀ ω₀ = T))
    (h : ∀ T a, 0 < massOf D.ν (fun π => π T = a)) : D.toPrior.NDHOME := by
  intro T a; rw [D.jointMass_toPrior]; exact mul_pos (hs T) (h T a)

/-- The point mass of a product law is the coordinate weight.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_prodLaw_point (g : ↥𝒟 → A → ℚ) (hg1 : ∀ T, ∑ a, g T a = 1) (T : ↥𝒟) (a : A) :
    massOf (prodLaw g) (fun π : Policy 𝒟 A => π T = a) = g T a := by
  unfold massOf
  have e : ∀ π : Policy 𝒟 A, (if π T = a then prodLaw g π else 0) =
      prodLaw g π * (if π T = a then (1 : ℚ) else 0) := by
    intro π; by_cases h : π T = a <;> simp [h]
  simp only [e]
  exact sum_prodLaw_mul_ind hg1 T a

end IndepData

end Cleanroom.Bli.UdtBliCore

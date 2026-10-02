import Cleanroom.Bli.UdtBliCore.Defs

/-!
# `udt-bli-core` · Basic: finite-probability lemmas under the definitions of record

Generic facts about `massOf`, `integralOf`, `condExp` (nonnegativity, the junk value at a null
event, the fiberwise / tower identity over any finite partition, the "equal parts" lemma, the
`|U| ≤ M` bound), and the sum identities relating the prior's derived masses
(`ppMass = ∑ jointMass`, `stateMass = ∑ jointMass`, `jointMass = ∑ cellMass`, `∑ branchProb = 1`).
Everything here is `L` (plumbing) or infrastructure; the headlines are in the target files.
-/

namespace Cleanroom.Bli.UdtBliCore

open Cleanroom.Bli.BliFinite Finset

section Generic

variable {Ω : Type} [Fintype Ω]

/-- The indicator is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ind_nonneg (b : Bool) : 0 ≤ ind b := by
  unfold ind; split_ifs <;> norm_num

/-- The indicator is at most one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ind_le_one (b : Bool) : ind b ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

/-- `ind true = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma ind_true : ind true = 1 := rfl

/-- `ind false = 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma ind_false : ind false = 0 := rfl

/-- Masses of nonnegative weights are nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_nonneg (μ : Ω → ℚ) (hμ : ∀ ω, 0 ≤ μ ω) (E : Ω → Prop) [DecidablePred E] :
    0 ≤ massOf μ E := by
  unfold massOf
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact hμ ω
  · exact le_rfl

/-- The mass of an event is at most the total mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_le_sum (μ : Ω → ℚ) (hμ : ∀ ω, 0 ≤ μ ω) (E : Ω → Prop) [DecidablePred E] :
    massOf μ E ≤ ∑ ω, μ ω := by
  unfold massOf
  apply Finset.sum_le_sum
  intro ω _
  split_ifs
  · exact le_rfl
  · exact hμ ω

/-- Two extensionally equal events have the same mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_congr (μ : Ω → ℚ) {E E' : Ω → Prop} [DecidablePred E] [DecidablePred E']
    (h : ∀ ω, E ω ↔ E' ω) : massOf μ E = massOf μ E' := by
  unfold massOf
  apply Finset.sum_congr rfl
  intro ω _
  simp only [h ω]

/-- Two extensionally equal events have the same integral.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma integralOf_congr (μ f : Ω → ℚ) {E E' : Ω → Prop} [DecidablePred E] [DecidablePred E']
    (h : ∀ ω, E ω ↔ E' ω) : integralOf μ f E = integralOf μ f E' := by
  unfold integralOf
  apply Finset.sum_congr rfl
  intro ω _
  simp only [h ω]

/-- Two functions agreeing on the event have the same integral over it.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma integralOf_congr_fun (μ f g : Ω → ℚ) (E : Ω → Prop) [DecidablePred E]
    (h : ∀ ω, E ω → f ω = g ω) : integralOf μ f E = integralOf μ g E := by
  unfold integralOf
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hE : E ω
  · simp only [hE, if_true, h ω hE]
  · simp only [hE, if_false]

/-- Two extensionally equal events have the same conditional expectation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condExp_congr (μ f : Ω → ℚ) {E E' : Ω → Prop} [DecidablePred E] [DecidablePred E']
    (h : ∀ ω, E ω ↔ E' ω) : condExp μ f E = condExp μ f E' := by
  unfold condExp
  rw [massOf_congr μ h, integralOf_congr μ f h]

/-- The integral of a constant is the constant times the mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma integralOf_const (μ : Ω → ℚ) (c : ℚ) (E : Ω → Prop) [DecidablePred E] :
    integralOf μ (fun _ => c) E = c * massOf μ E := by
  unfold integralOf massOf
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> ring

/-- Linearity of the integral in the integrand (sum).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma integralOf_add (μ f g : Ω → ℚ) (E : Ω → Prop) [DecidablePred E] :
    integralOf μ (fun ω => f ω + g ω) E = integralOf μ f E + integralOf μ g E := by
  unfold integralOf
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> ring

/-- Linearity of the integral in the integrand (scalar).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma integralOf_smul (μ f : Ω → ℚ) (c : ℚ) (E : Ω → Prop) [DecidablePred E] :
    integralOf μ (fun ω => c * f ω) E = c * integralOf μ f E := by
  unfold integralOf
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> ring

/-- Linearity of the integral over a finite sum of integrands.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma integralOf_finset_sum {ι : Type} (s : Finset ι) (μ : Ω → ℚ) (f : ι → Ω → ℚ)
    (E : Ω → Prop) [DecidablePred E] :
    integralOf μ (fun ω => ∑ i ∈ s, f i ω) E = ∑ i ∈ s, integralOf μ (f i) E := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [show (fun _ : Ω => (0 : ℚ)) = fun _ => (0 : ℚ) from rfl]
      unfold integralOf; simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, ← ih, ← integralOf_add]
      congr 1
      funext ω
      rw [Finset.sum_insert ha]

/-- A null event (nonnegative weights) has every weight zero on it.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_eq_zero_iff (μ : Ω → ℚ) (hμ : ∀ ω, 0 ≤ μ ω) (E : Ω → Prop) [DecidablePred E] :
    massOf μ E = 0 ↔ ∀ ω, E ω → μ ω = 0 := by
  unfold massOf
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun ω _ => by split_ifs; exact hμ ω; exact le_rfl)]
  constructor
  · intro h ω hE
    have := h ω (Finset.mem_univ ω)
    simpa [hE] using this
  · intro h ω _
    split_ifs with hE
    · exact h ω hE
    · rfl

/-- A positive event carries a world of positive weight.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_pos_iff (μ : Ω → ℚ) (hμ : ∀ ω, 0 ≤ μ ω) (E : Ω → Prop) [DecidablePred E] :
    0 < massOf μ E ↔ ∃ ω, E ω ∧ 0 < μ ω := by
  constructor
  · intro h
    by_contra hcon
    have hz : massOf μ E = 0 := by
      rw [massOf_eq_zero_iff μ hμ E]
      intro ω hE
      by_contra hne
      exact hcon ⟨ω, hE, lt_of_le_of_ne (hμ ω) (Ne.symm hne)⟩
    rw [hz] at h
    exact lt_irrefl _ h
  · rintro ⟨ω, hE, hpos⟩
    have hne : massOf μ E ≠ 0 := by
      rw [Ne, massOf_eq_zero_iff μ hμ E]
      intro h
      exact ne_of_gt hpos (h ω hE)
    exact lt_of_le_of_ne (massOf_nonneg μ hμ E) (Ne.symm hne)

/-- **The junk value's companion**: the integral over a null event is zero.
Source: none: infrastructure (mandate §3.1, junk values)
Kind: L
Fidelity: n/a -/
lemma integralOf_eq_zero_of_massOf_eq_zero (μ f : Ω → ℚ) (hμ : ∀ ω, 0 ≤ μ ω) (E : Ω → Prop)
    [DecidablePred E] (h : massOf μ E = 0) : integralOf μ f E = 0 := by
  rw [massOf_eq_zero_iff μ hμ E] at h
  unfold integralOf
  apply Finset.sum_eq_zero
  intro ω _
  split_ifs with hE
  · rw [h ω hE, zero_mul]
  · rfl

/-- `𝔼[f | E] · μ(E) = ∫_E f`, **also at a null event** (both sides are `0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condExp_mul_massOf (μ f : Ω → ℚ) (hμ : ∀ ω, 0 ≤ μ ω) (E : Ω → Prop) [DecidablePred E] :
    condExp μ f E * massOf μ E = integralOf μ f E := by
  unfold condExp
  by_cases h : massOf μ E = 0
  · rw [h, mul_zero, integralOf_eq_zero_of_massOf_eq_zero μ f hμ E h]
  · exact div_mul_cancel₀ _ h

/-- The conditional expectation of a constant on a positive event is the constant.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condExp_const (μ : Ω → ℚ) (c : ℚ) (E : Ω → Prop) [DecidablePred E]
    (hpos : 0 < massOf μ E) : condExp μ (fun _ => c) E = c := by
  unfold condExp
  rw [integralOf_const, mul_div_assoc, div_self (ne_of_gt hpos), mul_one]

/-- Monotonicity of the integral in the integrand on the event.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma integralOf_le_integralOf (μ f g : Ω → ℚ) (hμ : ∀ ω, 0 ≤ μ ω) (E : Ω → Prop)
    [DecidablePred E] (hfg : ∀ ω, E ω → f ω ≤ g ω) : integralOf μ f E ≤ integralOf μ g E := by
  unfold integralOf
  apply Finset.sum_le_sum
  intro ω _
  split_ifs with hE
  · exact mul_le_mul_of_nonneg_left (hfg ω hE) (hμ ω)
  · exact le_rfl

/-- `|∫_E f| ≤ M · μ(E)` when `|f| ≤ M` on `E`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma abs_integralOf_le (μ f : Ω → ℚ) (hμ : ∀ ω, 0 ≤ μ ω) (E : Ω → Prop) [DecidablePred E]
    (M : ℚ) (hf : ∀ ω, E ω → |f ω| ≤ M) : |integralOf μ f E| ≤ M * massOf μ E := by
  unfold integralOf massOf
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ω _ => ?_)
  split_ifs with hE
  · rw [abs_mul, abs_of_nonneg (hμ ω), mul_comm]
    exact mul_le_mul_of_nonneg_right (hf ω hE) (hμ ω)
  · simp

/-- `|𝔼[f | E]| ≤ M` when `|f| ≤ M` on `E` and `0 ≤ M` (also at a null event, where it is `0`).
Source: none: infrastructure (the `|U| ≤ M` bound of the ε-form, mandate T5)
Kind: L
Fidelity: n/a -/
lemma abs_condExp_le (μ f : Ω → ℚ) (hμ : ∀ ω, 0 ≤ μ ω) (E : Ω → Prop) [DecidablePred E]
    (M : ℚ) (hM : 0 ≤ M) (hf : ∀ ω, E ω → |f ω| ≤ M) : |condExp μ f E| ≤ M := by
  unfold condExp
  by_cases h : massOf μ E = 0
  · rw [h, div_zero, abs_zero]; exact hM
  · have hpos : 0 < massOf μ E := lt_of_le_of_ne (massOf_nonneg μ hμ E) (Ne.symm h)
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    exact abs_integralOf_le μ f hμ E M hf

/-! ### The fiberwise (tower) identity over any finite partition -/

variable {B : Type} [Fintype B] [DecidableEq B]

/-- The mass of `E` is the sum of the masses of its fibers under `β`.
Source: none: infrastructure (bli-soto-b-2-023, "a weighted sum over any partition")
Kind: L
Fidelity: n/a -/
lemma massOf_fiberwise (μ : Ω → ℚ) (E : Ω → Prop) [DecidablePred E] (β : Ω → B) :
    massOf μ E = ∑ b, massOf μ (fun ω => E ω ∧ β ω = b) := by
  unfold massOf
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hE : E ω
  · simp only [hE, true_and, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · simp only [hE, false_and, if_false, Finset.sum_const_zero]

/-- The integral over `E` is the sum of the integrals over its fibers under `β`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma integralOf_fiberwise (μ f : Ω → ℚ) (E : Ω → Prop) [DecidablePred E] (β : Ω → B) :
    integralOf μ f E = ∑ b, integralOf μ f (fun ω => E ω ∧ β ω = b) := by
  unfold integralOf
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hE : E ω
  · simp only [hE, true_and, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · simp only [hE, false_and, if_false, Finset.sum_const_zero]

omit [Fintype B] in
/-- Each fiber's weight times its conditional expectation is its integral over the total mass
(no positivity needed: a null fiber contributes `0` on both sides).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma fiber_weight_mul_condExp (μ f : Ω → ℚ) (hμ : ∀ ω, 0 ≤ μ ω) (E : Ω → Prop)
    [DecidablePred E] (β : Ω → B) (b : B) :
    massOf μ (fun ω => E ω ∧ β ω = b) / massOf μ E * condExp μ f (fun ω => E ω ∧ β ω = b) =
      integralOf μ f (fun ω => E ω ∧ β ω = b) / massOf μ E := by
  rw [div_mul_eq_mul_div, mul_comm, condExp_mul_massOf μ f hμ]

/-- **The tower identity over any finite partition**: `𝔼[f | E] = ∑_b μ(β = b | E) · 𝔼[f | E ∧ β = b]`
(with the junk conventions, unconditionally; meaningful when `μ(E) > 0`).
Source: bli-slides-037 (`𝔼_P(u | φ) = ∑_o P(o | φ) 𝔼_P(u | φ, o)`); bli-soto-b-2-023
(decomposition invariance: "UDT cares about a weighted sum over any partition")
Kind: L
Fidelity: exact -/
theorem condExp_fiberwise (μ f : Ω → ℚ) (hμ : ∀ ω, 0 ≤ μ ω) (E : Ω → Prop) [DecidablePred E]
    (β : Ω → B) :
    condExp μ f E = ∑ b, massOf μ (fun ω => E ω ∧ β ω = b) / massOf μ E *
      condExp μ f (fun ω => E ω ∧ β ω = b) := by
  simp only [fiber_weight_mul_condExp μ f hμ E β]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  unfold condExp
  rw [integralOf_fiberwise μ f E β, div_eq_mul_inv]

/-- **Equal parts**: if every positive fiber of a positive event has conditional expectation
`c`, so does the event.
Source: none: infrastructure (the averaging step of Good's theorem, mandate T6(i))
Kind: L
Fidelity: n/a -/
lemma condExp_eq_of_fibers (μ f : Ω → ℚ) (hμ : ∀ ω, 0 ≤ μ ω) (E : Ω → Prop) [DecidablePred E]
    (β : Ω → B) (c : ℚ) (hpos : 0 < massOf μ E)
    (h : ∀ b, 0 < massOf μ (fun ω => E ω ∧ β ω = b) → condExp μ f (fun ω => E ω ∧ β ω = b) = c) :
    condExp μ f E = c := by
  have key : integralOf μ f E = c * massOf μ E := by
    rw [integralOf_fiberwise μ f E β, massOf_fiberwise μ E β, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : 0 < massOf μ (fun ω => E ω ∧ β ω = b)
    · rw [← condExp_mul_massOf μ f hμ, h b hb]
    · have hz : massOf μ (fun ω => E ω ∧ β ω = b) = 0 :=
        le_antisymm (not_lt.mp hb) (massOf_nonneg μ hμ _)
      rw [hz, integralOf_eq_zero_of_massOf_eq_zero μ f hμ _ hz, mul_zero]
  unfold condExp
  rw [key, mul_div_assoc, div_self (ne_of_gt hpos), mul_one]

/-- The mass of `E ∧ (b = true)` is the integral of the indicator of `b` over `E`.
Source: none: infrastructure (faith as an integral)
Kind: L
Fidelity: n/a -/
lemma massOf_and_true_eq_integralOf_ind (μ : Ω → ℚ) (E : Ω → Prop) [DecidablePred E]
    (b : Ω → Bool) :
    massOf μ (fun ω => E ω ∧ b ω = true) = integralOf μ (fun ω => ind (b ω)) E := by
  unfold massOf integralOf
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hE : E ω
  · by_cases hb : b ω = true
    · simp [hE, hb, ind]
    · simp [hE, hb, ind]
  · simp [hE]

end Generic

/-! ## Sum identities on a prior -/

namespace FiniteBLIPrior

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [DecidableEq A]
variable (P : FiniteBLIPrior 𝒮 m 𝒟 A)

/-- `stateMass ≥ 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateMass_nonneg (T : ↥𝒟) : 0 ≤ P.stateMass T := massOf_nonneg _ P.μ_nonneg _

/-- `ppMass ≥ 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ppMass_nonneg (T : ↥𝒟) (a : A) : 0 ≤ P.ppMass T a := massOf_nonneg _ P.μ_nonneg _

/-- `jointMass ≥ 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jointMass_nonneg (T' T : ↥𝒟) (a : A) : 0 ≤ P.jointMass T' T a :=
  massOf_nonneg _ P.μ_nonneg _

/-- `policyMass ≥ 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyMass_nonneg (π : Policy 𝒟 A) : 0 ≤ P.policyMass π := massOf_nonneg _ P.μ_nonneg _

/-- `cellMass ≥ 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellMass_nonneg (T : ↥𝒟) (π : Policy 𝒟 A) : 0 ≤ P.cellMass T π :=
  massOf_nonneg _ P.μ_nonneg _

/-- The total mass of the prior is one, as a `massOf` of the trivial event.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_true : massOf P.μ (fun _ => True) = 1 := by
  unfold massOf; simp [P.μ_sum_one]

/-- The state masses sum to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_stateMass : ∑ T, P.stateMass T = 1 := by
  have := massOf_fiberwise P.μ (fun _ => True) P.state
  rw [P.massOf_true] at this
  rw [this]
  apply Finset.sum_congr rfl
  intro T _
  unfold stateMass
  exact massOf_congr _ (fun ω => by simp)

/-- `ppMass T a = ∑_{T'} jointMass T' T a`: the policy point's mass splits over the branches.
Source: bli-soto-a-2-012 (ii) (law of total probability)
Kind: L
Fidelity: exact -/
lemma ppMass_eq_sum_jointMass (T : ↥𝒟) (a : A) : P.ppMass T a = ∑ T', P.jointMass T' T a := by
  unfold ppMass jointMass
  rw [massOf_fiberwise P.μ _ P.state]
  apply Finset.sum_congr rfl
  intro T' _
  exact massOf_congr _ (fun ω => and_comm)

/-- `ppUtil T a = ∑_{T'} jointUtil T' T a`.
Source: bli-soto-a-2-012 (ii)
Kind: L
Fidelity: exact -/
lemma ppUtil_eq_sum_jointUtil (T : ↥𝒟) (a : A) : P.ppUtil T a = ∑ T', P.jointUtil T' T a := by
  unfold ppUtil jointUtil
  rw [integralOf_fiberwise P.μ P.U _ P.state]
  apply Finset.sum_congr rfl
  intro T' _
  exact integralOf_congr _ _ (fun ω => and_comm)

/-- `stateMass T' = ∑_a jointMass T' T a`: the branch's mass splits over the values of any point.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateMass_eq_sum_jointMass [Fintype A] (T' T : ↥𝒟) :
    P.stateMass T' = ∑ a, P.jointMass T' T a := by
  unfold stateMass jointMass
  exact massOf_fiberwise P.μ _ (fun ω => P.pp ω T)

/-- `jointMass T' T a = ∑_{π : π T = a} cellMass T' π` (written as a sum over all policies with
an indicator).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jointMass_eq_sum_cellMass [Fintype A] (T' T : ↥𝒟) (a : A) :
    P.jointMass T' T a = ∑ π, if π T = a then P.cellMass T' π else 0 := by
  unfold jointMass cellMass
  rw [massOf_fiberwise P.μ _ P.pp]
  apply Finset.sum_congr rfl
  intro π _
  by_cases hπ : π T = a
  · rw [if_pos hπ]
    exact massOf_congr _ (fun ω => by
      constructor
      · rintro ⟨⟨hs, _⟩, hp⟩; exact ⟨hs, hp⟩
      · rintro ⟨hs, hp⟩; exact ⟨⟨hs, hp ▸ hπ⟩, hp⟩)
  · rw [if_neg hπ]
    unfold massOf
    apply Finset.sum_eq_zero
    intro ω _
    rw [if_neg]
    rintro ⟨⟨_, hpa⟩, hp⟩
    exact hπ (hp ▸ hpa)

/-- `jointUtil T' T a = ∑_{π : π T = a} cellUtil T' π`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jointUtil_eq_sum_cellUtil [Fintype A] (T' T : ↥𝒟) (a : A) :
    P.jointUtil T' T a = ∑ π, if π T = a then P.cellUtil T' π else 0 := by
  unfold jointUtil cellUtil
  rw [integralOf_fiberwise P.μ P.U _ P.pp]
  apply Finset.sum_congr rfl
  intro π _
  by_cases hπ : π T = a
  · rw [if_pos hπ]
    exact integralOf_congr _ _ (fun ω => by
      constructor
      · rintro ⟨⟨hs, _⟩, hp⟩; exact ⟨hs, hp⟩
      · rintro ⟨hs, hp⟩; exact ⟨⟨hs, hp ▸ hπ⟩, hp⟩)
  · rw [if_neg hπ]
    unfold integralOf
    apply Finset.sum_eq_zero
    intro ω _
    rw [if_neg]
    rintro ⟨⟨_, hpa⟩, hp⟩
    exact hπ (hp ▸ hpa)

/-- `policyMass π = ∑_T cellMass T π`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyMass_eq_sum_cellMass (π : Policy 𝒟 A) : P.policyMass π = ∑ T, P.cellMass T π := by
  unfold policyMass cellMass
  rw [massOf_fiberwise P.μ _ P.state]
  apply Finset.sum_congr rfl
  intro T _
  exact massOf_congr _ (fun ω => and_comm)

/-- `stateMass T = ∑_π cellMass T π`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateMass_eq_sum_cellMass [Fintype A] (T : ↥𝒟) : P.stateMass T = ∑ π, P.cellMass T π := by
  unfold stateMass cellMass
  exact massOf_fiberwise P.μ _ P.pp

/-- Branch probabilities are nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma branchProb_nonneg (T' T : ↥𝒟) (a : A) : 0 ≤ P.branchProb T' T a :=
  div_nonneg (P.jointMass_nonneg T' T a) (P.ppMass_nonneg T a)

/-- The branch probabilities of a positive policy point sum to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_branchProb (T : ↥𝒟) (a : A) (hpos : 0 < P.ppMass T a) :
    ∑ T', P.branchProb T' T a = 1 := by
  unfold branchProb
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← P.ppMass_eq_sum_jointMass, mul_inv_cancel₀ (ne_of_gt hpos)]

/-- A positive cell sits inside a positive branch.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateMass_pos_of_jointMass_pos [Fintype A] {T' T : ↥𝒟} {a : A}
    (h : 0 < P.jointMass T' T a) : 0 < P.stateMass T' := by
  rw [P.stateMass_eq_sum_jointMass T' T]
  exact lt_of_lt_of_le h (Finset.single_le_sum (fun b _ => P.jointMass_nonneg T' T b)
    (Finset.mem_univ a))

/-- A positive cell sits inside a positive policy point.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ppMass_pos_of_jointMass_pos {T' T : ↥𝒟} {a : A} (h : 0 < P.jointMass T' T a) :
    0 < P.ppMass T a := by
  rw [P.ppMass_eq_sum_jointMass T a]
  exact lt_of_lt_of_le h (Finset.single_le_sum (fun S _ => P.jointMass_nonneg S T a)
    (Finset.mem_univ T'))

/-- `jointMass ≤ ppMass`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jointMass_le_ppMass (T' T : ↥𝒟) (a : A) : P.jointMass T' T a ≤ P.ppMass T a := by
  rw [P.ppMass_eq_sum_jointMass T a]
  exact Finset.single_le_sum (fun S _ => P.jointMass_nonneg S T a) (Finset.mem_univ T')

/-- `branchProb ≤ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma branchProb_le_one (T' T : ↥𝒟) (a : A) : P.branchProb T' T a ≤ 1 := by
  unfold branchProb
  by_cases h : P.ppMass T a = 0
  · rw [h, div_zero]; exact zero_le_one
  · have hpos : 0 < P.ppMass T a := lt_of_le_of_ne (P.ppMass_nonneg T a) (Ne.symm h)
    rw [div_le_one hpos]
    exact P.jointMass_le_ppMass T' T a

/-- `NDHOME` implies every state has positive mass (given a point value to look at).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma NDHOME.stateMass_pos [Fintype A] [Nonempty A] (h : P.NDHOME) (T : ↥𝒟) :
    0 < P.stateMass T :=
  P.stateMass_pos_of_jointMass_pos (h T (Classical.arbitrary A))

/-- `NDHOME` implies `NDPOL`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma NDHOME.ndpol (h : P.NDHOME) : P.NDPOL :=
  fun T a => P.ppMass_pos_of_jointMass_pos (h T a)

/-- `condEU T' T a · jointMass T' T a = jointUtil T' T a` (also at a null cell).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condEU_mul_jointMass (T' T : ↥𝒟) (a : A) :
    P.condEU T' T a * P.jointMass T' T a = P.jointUtil T' T a :=
  condExp_mul_massOf P.μ P.U P.μ_nonneg _

/-- **`FaithGivenPoints` implies the `faith` field's statement** (summing the refined identity
over the values of any point). So the field is the weaker of the two; the converse fails
(`WitnessLayers.lean`, `fng_not_faithGivenPoints`).
Source: mandate §3.4
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem faith_of_faithGivenPoints [Fintype A] (h : P.FaithGivenPoints) (T T' : ↥𝒟)
    (φ : ↥(𝒮.S m)) :
    integralOf P.μ (fun ω => ind (P.small ω φ)) (fun ω => P.state ω = T) =
      T.1 φ * P.stateMass T := by
  rw [integralOf_fiberwise P.μ _ _ (fun ω => P.pp ω T'), P.stateMass_eq_sum_jointMass T T',
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hpos : 0 < P.jointMass T T' a
  · exact h T T' a φ hpos
  · have hz : P.jointMass T T' a = 0 :=
      le_antisymm (not_lt.mp hpos) (P.jointMass_nonneg T T' a)
    rw [hz, mul_zero]
    exact integralOf_eq_zero_of_massOf_eq_zero P.μ _ P.μ_nonneg _ hz

end FiniteBLIPrior

end Cleanroom.Bli.UdtBliCore

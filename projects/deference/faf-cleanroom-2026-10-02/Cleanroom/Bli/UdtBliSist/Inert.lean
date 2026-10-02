import Cleanroom.Bli.UdtBliSist.Sist

/-!
# `udt-bli-sist` · Inert: the per-node class lemma for reference-point utilities

The reusable form of "the other tables never observe `Q̂`" (bli-soto-a-2-015's inertness of the PH
tables, bli-soto-b-2-012's inertness of the other nodes): over an `IndepData` prior with
**independent points** and a **reference-point utility** `U₀ ω₀ π = f ω₀ (π (ref ω₀))`,

* a branch whose outcomes never read `Q` is inert at `Q` (`condEU_ref_of_ne`), so a class `𝒞`
  is `ClassInert` at `Q` as soon as every state outside `𝒞` reads a table other than `Q`
  (`classInert_of_ref`);
* a branch whose outcomes all read `Q` has `condEU T Q a = 𝔼_{μ₀}[f · a | state₀ = T]`
  (`condEU_ref_of_eq`, the `T ≠ Q` form of `homeEU_ref_self`);
* and the two combine with `classCut` into **the per-node class lemma** `classCut_ref`: when the
  class is exactly the set of states reading `Q`, `EU Q a − EU Q b = ∑_{T ∈ 𝒞} μ(state = T) ·
  (𝔼[f · a | T] − 𝔼[f · b | T])`. Both the CM/PH witness (`PhCm.lean`, T3(b)) and the
  `K`-node family (`Iterated.lean`, T6(a)) are instances; `udt-bli-learning` is told to reuse it.

Source: repair round 1 (audit A2/B1); mandate T3(b), T6(a); bli-soto-a-2-015; bli-soto-b-2-012.
-/

namespace Cleanroom.Bli.UdtBliSist

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

section Inert

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [Fintype A] [DecidableEq A]

omit [Fintype A] in
/-- **Independent points make the conditional point law the marginal**: for `T ≠ Q` at a positive
point, `μ(pp·T = b | pp·Q = a) = μ(pp·T = b)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condPoint_of_independentPoints (P : FiniteBLIPrior 𝒮 m 𝒟 A) (hI : P.IndependentPoints)
    {T Q : ↥𝒟} (hne : T ≠ Q) (b a : A) (ha : 0 < P.ppMass Q a) :
    condPoint P T Q b a = P.ppMass T b := by
  unfold condPoint
  rw [hI T Q b a hne, mul_div_assoc, div_self (ne_of_gt ha), mul_one]

variable (D : IndepData 𝒮 m 𝒟 A)

/-- **A branch that never reads `Q` is inert at `Q`** under independent points: for a
reference-point utility, if every outcome with `state₀ = T` reads a table other than `Q`, then
`condEU T Q a = condEU T Q b` at positive points.
Source: bli-soto-a-2-015 ("the PH tables never observe `Q̂`"); mandate T3(b), T6(a)
Kind: L
Fidelity: exact -/
lemma condEU_ref_of_ne (hI : D.toPrior.IndependentPoints) (ref : D.Ω₀ → ↥𝒟) (f : D.Ω₀ → A → ℚ)
    (hU : ∀ ω₀ π, D.U₀ ω₀ π = f ω₀ (π (ref ω₀))) (T Q : ↥𝒟)
    (hT : ∀ ω₀, D.state₀ ω₀ = T → ref ω₀ ≠ Q) (a b : A)
    (ha : 0 < D.toPrior.ppMass Q a) (hb : 0 < D.toPrior.ppMass Q b) :
    D.toPrior.condEU T Q a = D.toPrior.condEU T Q b := by
  rw [condEU_ref D ref f hU T Q a, condEU_ref D ref f hU T Q b]
  unfold condExp
  congr 1
  apply integralOf_congr_fun
  intro ω₀ hω
  apply Finset.sum_congr rfl
  intro c _
  rw [condPoint_of_independentPoints _ hI (hT ω₀ hω) c a ha,
    condPoint_of_independentPoints _ hI (hT ω₀ hω) c b hb]

/-- **Class inertness from the reference map**: a class `𝒞` is `ClassInert` at `Q` whenever every
state outside `𝒞` reads a table other than `Q` (independent points, reference-point utility).
Source: bli-soto-a-2-015; bli-soto-b-2-012 ("inertness of the other nodes' tables"); mandate
T3(b), T6(a)
Kind: L
Fidelity: exact -/
lemma classInert_of_ref (hI : D.toPrior.IndependentPoints) (ref : D.Ω₀ → ↥𝒟) (f : D.Ω₀ → A → ℚ)
    (hU : ∀ ω₀ π, D.U₀ ω₀ π = f ω₀ (π (ref ω₀))) (𝒞 : Finset ↥𝒟) (Q : ↥𝒟)
    (hout : ∀ ω₀, D.state₀ ω₀ ∉ 𝒞 → ref ω₀ ≠ Q) : ClassInert D.toPrior 𝒞 Q := by
  intro T hT a b ha hb
  exact condEU_ref_of_ne D hI ref f hU T Q (fun ω₀ hω => hout ω₀ (hω ▸ hT)) a b
    (D.toPrior.ppMass_pos_of_jointMass_pos ha) (D.toPrior.ppMass_pos_of_jointMass_pos hb)

/-- **A branch that always reads `Q`** has the branch value `𝔼_{μ₀}[f · a | state₀ = T]` at a
positive point (the `T ≠ Q` form of `homeEU_ref_self`).
Source: bli-soto-a-2-012 (i); mandate §3.5
Kind: L
Fidelity: exact -/
lemma condEU_ref_of_eq (ref : D.Ω₀ → ↥𝒟) (f : D.Ω₀ → A → ℚ)
    (hU : ∀ ω₀ π, D.U₀ ω₀ π = f ω₀ (π (ref ω₀))) (T Q : ↥𝒟)
    (hT : ∀ ω₀, D.state₀ ω₀ = T → ref ω₀ = Q) (a : A)
    (ha : 0 < massOf D.ν (fun π => π Q = a)) :
    D.toPrior.condEU T Q a = condExp D.μ₀ (fun ω₀ => f ω₀ a) (fun ω₀ => D.state₀ ω₀ = T) := by
  rw [condEU_ref D ref f hU T Q a]
  unfold condExp
  congr 1
  apply integralOf_congr_fun
  intro ω₀ hω
  rw [hT ω₀ hω]
  have hpp : 0 < D.toPrior.ppMass Q a := by rw [D.ppMass_toPrior]; exact ha
  simp only [condPoint_self D.toPrior Q _ a hpp]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The branch weight of `toPrior` at a positive point is the state mass (`Reflective`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma branchProb_toPrior (T Q : ↥𝒟) (a : A) (ha : 0 < massOf D.ν (fun π => π Q = a)) :
    D.toPrior.branchProb T Q a = D.toPrior.stateMass T :=
  D.reflective_toPrior T Q a (by rw [D.ppMass_toPrior]; exact ha)

/-- **The per-node class lemma.** Over an `IndepData` prior with independent points and a
reference-point utility, if the class `𝒞` is exactly the set of states that read `Q` (states in
`𝒞` read `Q`, states outside read another table), then at points positive under `a` and `b`
`EU Q a − EU Q b = ∑_{T ∈ 𝒞} μ(state = T) · (𝔼_{μ₀}[f · a | T] − 𝔼_{μ₀}[f · b | T])`:
the class-cut with the branch weights and the branch values evaluated.
Source: bli-soto-a-2-015 (the CM class decides the argmax); bli-soto-b-2-012 (i) (SIST at every
node); mandate T3(b), T6(a) ("by `classCut` with `𝒞_k = {Ask_k, Rec_k}` and inertness of the
other nodes' tables")
Kind: C (`classCut` with `condEU_ref_of_ne` off the class and `condEU_ref_of_eq` on it)
Fidelity: exact
Hyps: (a) independent points, the reference shape, the two reading conditions, positivity of the
two points; does not use faith -/
theorem classCut_ref (hI : D.toPrior.IndependentPoints) (ref : D.Ω₀ → ↥𝒟) (f : D.Ω₀ → A → ℚ)
    (hU : ∀ ω₀ π, D.U₀ ω₀ π = f ω₀ (π (ref ω₀))) (𝒞 : Finset ↥𝒟) (Q : ↥𝒟)
    (hin : ∀ ω₀, D.state₀ ω₀ ∈ 𝒞 → ref ω₀ = Q)
    (hout : ∀ ω₀, D.state₀ ω₀ ∉ 𝒞 → ref ω₀ ≠ Q) (a b : A)
    (ha : 0 < massOf D.ν (fun π => π Q = a)) (hb : 0 < massOf D.ν (fun π => π Q = b)) :
    D.toPrior.EU Q a - D.toPrior.EU Q b =
      ∑ T ∈ 𝒞, D.toPrior.stateMass T *
        (condExp D.μ₀ (fun ω₀ => f ω₀ a) (fun ω₀ => D.state₀ ω₀ = T) -
          condExp D.μ₀ (fun ω₀ => f ω₀ b) (fun ω₀ => D.state₀ ω₀ = T)) := by
  rw [classCut D.toPrior 𝒞 Q a b
    (fun T => by rw [branchProb_toPrior D T Q a ha, branchProb_toPrior D T Q b hb])
    (fun T hT _ _ => condEU_ref_of_ne D hI ref f hU T Q (fun ω₀ hω => hout ω₀ (hω ▸ hT)) a b
      (by rw [D.ppMass_toPrior]; exact ha) (by rw [D.ppMass_toPrior]; exact hb))]
  apply Finset.sum_congr rfl
  intro T hT
  rw [branchProb_toPrior D T Q a ha, condEU_ref_of_eq D ref f hU T Q (fun ω₀ hω => hin ω₀ (hω ▸ hT)) a ha,
    condEU_ref_of_eq D ref f hU T Q (fun ω₀ hω => hin ω₀ (hω ▸ hT)) b hb]

/-- A conditional expectation on a singleton event of positive mass is the value there.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condExp_eq_single {Ω : Type} [Fintype Ω] [DecidableEq Ω] (μ f : Ω → ℚ) (s₀ : Ω)
    (h : μ s₀ ≠ 0) : condExp μ f (fun s => s = s₀) = f s₀ := by
  unfold condExp integralOf massOf
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  field_simp

/-- The state mass of `toPrior` at an injective state coordinate is the base weight.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateMass_toPrior_of_injective [DecidableEq D.Ω₀] (hinj : Function.Injective D.state₀)
    (s : D.Ω₀) : D.toPrior.stateMass (D.state₀ s) = D.μ₀ s := by
  rw [D.stateMass_toPrior]
  unfold massOf
  simp only [hinj.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **The per-node class lemma on an injective state coordinate**: with `state₀` injective, every
in-class term is `μ₀ s · (f s a − f s b)` (a null base weight contributes `0` on both sides).
Source: as `classCut_ref`
Kind: C
Fidelity: exact
Hyps: (a) as `classCut_ref` plus injectivity of the state coordinate -/
theorem classCut_ref_injective [DecidableEq D.Ω₀] (hinj : Function.Injective D.state₀)
    (hI : D.toPrior.IndependentPoints) (ref : D.Ω₀ → ↥𝒟) (f : D.Ω₀ → A → ℚ)
    (hU : ∀ ω₀ π, D.U₀ ω₀ π = f ω₀ (π (ref ω₀))) (S : Finset D.Ω₀) (Q : ↥𝒟)
    (hin : ∀ s ∈ S, ref s = Q) (hout : ∀ s ∉ S, ref s ≠ Q) (a b : A)
    (ha : 0 < massOf D.ν (fun π => π Q = a)) (hb : 0 < massOf D.ν (fun π => π Q = b)) :
    D.toPrior.EU Q a - D.toPrior.EU Q b = ∑ s ∈ S, D.μ₀ s * (f s a - f s b) := by
  rw [classCut_ref D hI ref f hU (S.image D.state₀) Q
    (fun ω₀ hω => hin ω₀ (by
      obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hω
      rw [← hinj he]; exact hs))
    (fun ω₀ hω => hout ω₀ (fun hs => hω (Finset.mem_image_of_mem _ hs))) a b ha hb]
  rw [Finset.sum_image (fun s _ s' _ h => hinj h)]
  apply Finset.sum_congr rfl
  intro s _
  rw [stateMass_toPrior_of_injective D hinj s]
  by_cases h0 : D.μ₀ s = 0
  · rw [h0, zero_mul, zero_mul]
  · rw [condExp_congr _ _ (fun ω₀ => hinj.eq_iff), condExp_eq_single _ _ s h0,
      condExp_congr _ _ (fun ω₀ => hinj.eq_iff), condExp_eq_single _ _ s h0]

/-- **A single-outcome branch reading `Q`** has the branch value `f s₀ a`: with `state₀` injective,
`condEU (state₀ s₀) Q a = f s₀ a` at a positive point and a positive base weight.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condEU_ref_of_eq_single [DecidableEq D.Ω₀] (hinj : Function.Injective D.state₀)
    (ref : D.Ω₀ → ↥𝒟) (f : D.Ω₀ → A → ℚ) (hU : ∀ ω₀ π, D.U₀ ω₀ π = f ω₀ (π (ref ω₀)))
    (s₀ : D.Ω₀) (T : ↥𝒟) (hT : D.state₀ s₀ = T) (Q : ↥𝒟) (hs : ref s₀ = Q) (a : A)
    (ha : 0 < massOf D.ν (fun π => π Q = a)) (h0 : D.μ₀ s₀ ≠ 0) :
    D.toPrior.condEU T Q a = f s₀ a := by
  subst hT
  rw [condEU_ref_of_eq D ref f hU _ Q (fun ω₀ hω => by rw [hinj hω]; exact hs) a ha,
    condExp_congr _ _ (fun ω₀ => hinj.eq_iff), condExp_eq_single _ _ s₀ h0]

/-- The cell mass at an injective state coordinate is the base weight times the point mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jointMass_toPrior_of_injective [DecidableEq D.Ω₀] (hinj : Function.Injective D.state₀)
    (s₀ : D.Ω₀) (T : ↥𝒟) (hT : D.state₀ s₀ = T) (Q : ↥𝒟) (a : A) :
    D.toPrior.jointMass T Q a = D.μ₀ s₀ * massOf D.ν (fun π => π Q = a) := by
  subst hT
  rw [D.jointMass_toPrior]
  congr 1
  unfold massOf
  simp only [hinj.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Inert

end Cleanroom.Bli.UdtBliSist

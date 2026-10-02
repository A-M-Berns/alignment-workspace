import Cleanroom.Udt.UdtCondenseDd.Latent

/-!
# `Cleanroom.Udt.UdtCondenseDd.Markov`: DD is the ordered-Markov clause of Theorem 4.9(B) (T9(b))

Work package `udt-condense-dd`, target T9(b) (udt-rep-045). Over the policy latent model
`polLatent S` (`Latent.lean`):

* `orderedMarkov_polLatent_iff_dd`: FAF's ordered Markov condition (Definition 4.8) for the latent
  random variable model **is** `CondIndepFun S.E S.DIB S.polE` — i.e. clause (2) of
  decision-determination (T7(b)). Unfolding `OrderedMarkov` over the three elements of `P⁺ (Fin 2)`:
  at `A = P0` the clause is `CondIndepFun D_{I,B} E Π̈`, at `A = P1` its mirror, at `A = P01` it is
  trivial (nothing is incomparable to, or strictly above, the top).
* `perfectlyCondenses_polLatent_iff_of_dd`: under DD, perfect condensation by the policy latent
  **is** Theorem 4.9(B)'s function clause; and since every instance of that clause other than
  "`Π̈` is a function of `E`" holds by construction, under DD
  `PerfectlyCondenses ↔ IsSubvariable S.E S.polE` (`perfectlyCondenses_polLatent_iff_isSubvariable_of_dd`).

So: **the corpus's DD is the ordered-Markov clause of Theorem 4.9(B) without its function clause**;
"`Π̈` is a perfect condensation variable" (the note's sentence, T9(a)) is exactly that missing
clause, which fails whenever `Π̈` is not a function of `E`.

The transport lemmas (`condIndepFun_comp_left_iff`, `_mid_iff`, `_cond_iff`, `condIndepFun_symm`,
`condIndepFun_of_isEmpty_mid`) move PFR's `CondIndepFun` along the injective codings of
`Latent.lean` and the singleton/empty index families of the joint latents; they are generic
(any finite measure on any measurable space, countable discrete conditioning ranges).
-/

namespace Cleanroom.Udt.UdtCondenseDd

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust MeasureTheory ProbabilityTheory Finset
open Condensation

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Transport of conditional independence -/

section Transport

variable {Ω' : Type} [MeasurableSpace Ω'] {μ : Measure Ω'} [IsFiniteMeasure μ]
variable {V W U V' W' U' : Type} [MeasurableSpace V] [MeasurableSpace W] [MeasurableSpace U]
  [MeasurableSpace V'] [MeasurableSpace W'] [MeasurableSpace U']

/-- **Conditional independence is symmetric in its two variables.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condIndepFun_symm {X : Ω' → V} {Y : Ω' → W} {Z : Ω' → U} (h : CondIndepFun X Y Z μ) :
    CondIndepFun Y X Z μ := by
  rw [condIndepFun_iff] at h ⊢
  filter_upwards [h] with z hz
  exact hz.symm

/-- **Transport along a coding of the first variable**: for `g` with a measurable left inverse,
`CondIndepFun (g ∘ X) Y Z μ ↔ CondIndepFun X Y Z μ`.
Source: none: infrastructure (mandate T9(b), `condIndepFun_comp_equiv`-style)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condIndepFun_comp_left_iff {X : Ω' → V} {Y : Ω' → W} {Z : Ω' → U} {g : V → V'}
    {g' : V' → V} (hg : Measurable g) (hg' : Measurable g') (hgg : ∀ v, g' (g v) = v) :
    CondIndepFun (g ∘ X) Y Z μ ↔ CondIndepFun X Y Z μ := by
  constructor
  · intro h
    rw [condIndepFun_iff] at h ⊢
    filter_upwards [h] with z hz
    have h1 := hz.comp hg' measurable_id
    have hX : g' ∘ (g ∘ X) = X := funext fun ω => hgg (X ω)
    rw [hX] at h1
    exact h1
  · intro h
    rw [condIndepFun_iff] at h ⊢
    filter_upwards [h] with z hz
    exact hz.comp hg measurable_id

/-- **Transport along a coding of the second variable.**
Source: none: infrastructure (mandate T9(b))
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condIndepFun_comp_mid_iff {X : Ω' → V} {Y : Ω' → W} {Z : Ω' → U} {g : W → W'}
    {g' : W' → W} (hg : Measurable g) (hg' : Measurable g') (hgg : ∀ w, g' (g w) = w) :
    CondIndepFun X (g ∘ Y) Z μ ↔ CondIndepFun X Y Z μ := by
  constructor
  · intro h
    rw [condIndepFun_iff] at h ⊢
    filter_upwards [h] with z hz
    have h1 := hz.comp measurable_id hg'
    have hY : g' ∘ (g ∘ Y) = Y := funext fun ω => hgg (Y ω)
    rw [hY] at h1
    exact h1
  · intro h
    rw [condIndepFun_iff] at h ⊢
    filter_upwards [h] with z hz
    exact hz.comp measurable_id hg

/-- **Transport along an injective coding of the conditioning variable** (countable discrete
ranges): `CondIndepFun X Y (ψ ∘ Z) μ ↔ CondIndepFun X Y Z μ`.
Source: none: infrastructure (mandate T9(b))
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condIndepFun_comp_cond_iff [Countable U] [MeasurableSingletonClass U] [Countable U']
    [MeasurableSingletonClass U'] {X : Ω' → V} {Y : Ω' → W} {Z : Ω' → U} {ψ : U → U'}
    (hZ : Measurable Z) (hψ : Measurable ψ) (hinj : Function.Injective ψ) :
    CondIndepFun X Y (ψ ∘ Z) μ ↔ CondIndepFun X Y Z μ := by
  have hpre : ∀ z, (ψ ∘ Z) ⁻¹' {ψ z} = Z ⁻¹' {z} := fun z => by
    ext ω
    simp [hinj.eq_iff]
  constructor
  · intro h
    rw [condIndepFun_iff, ae_iff_of_countable] at h ⊢
    intro z hz
    rw [Measure.map_apply hZ (measurableSet_singleton z)] at hz
    have hz' : (μ.map (ψ ∘ Z)) {ψ z} ≠ 0 := by
      rw [Measure.map_apply (hψ.comp hZ) (measurableSet_singleton _), hpre]
      exact hz
    have := h (ψ z) hz'
    rwa [hpre] at this
  · intro h
    rw [condIndepFun_iff, ae_iff_of_countable] at h ⊢
    intro z' hz'
    rw [Measure.map_apply (hψ.comp hZ) (measurableSet_singleton z')] at hz'
    obtain ⟨ω, hω⟩ := exists_of_measure_ne_zero _ hz'
    have hω' : ψ (Z ω) = z' := hω
    subst hω'
    rw [hpre]
    refine h (Z ω) ?_
    rw [Measure.map_apply hZ (measurableSet_singleton _)]
    rwa [hpre] at hz'

/-- **A variable into a function type over an empty index is conditionally independent of
anything** (it is constant).
Source: none: infrastructure (mandate T9(b), the `A = {0,1}` clause)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condIndepFun_of_isEmpty_mid [Countable U] [MeasurableSingletonClass U] {X : Ω' → V}
    {Z : Ω' → U} (hZ : Measurable Z) {ι : Type} [IsEmpty ι] (Y : Ω' → (ι → W)) :
    CondIndepFun X Y Z μ := by
  rw [condIndepFun_iff, ae_iff_of_countable]
  intro z hz
  rw [Measure.map_apply hZ (measurableSet_singleton z)] at hz
  haveI : IsProbabilityMeasure (μ[|Z ⁻¹' {z}]) := cond_isProbabilityMeasure hz
  have hY : Y = fun _ => fun i : ι => (IsEmpty.false i).elim :=
    funext fun _ => funext fun i => (IsEmpty.false i).elim
  rw [hY]
  exact indepFun_const_right X _

end Transport

/-! ### The index families of `P⁺ (Fin 2)` -/

/-- `incomparable P0 = {P1}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem incomparable_P0 : ∀ B, B ∈ incomparable P0 ↔ B = P1 := by
  intro B
  rw [mem_incomparable, PPlus.le_iff, PPlus.le_iff]
  revert B
  decide

/-- `incomparable P1 = {P0}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem incomparable_P1 : ∀ B, B ∈ incomparable P1 ↔ B = P0 := by
  intro B
  rw [mem_incomparable, PPlus.le_iff, PPlus.le_iff]
  revert B
  decide

/-- `incomparable P01 = ∅`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem incomparable_P01 : ∀ B, B ∉ incomparable P01 := by
  intro B
  rw [mem_incomparable, PPlus.le_iff, PPlus.le_iff]
  revert B
  decide

/-- `strictAbove {0} = {P01}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem strictAbove_P0 : ∀ B, B ∈ strictAbove P0.toFinset ↔ B = P01 := by
  intro B
  rw [mem_strictAbove]
  revert B
  decide

/-- `strictAbove {1} = {P01}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem strictAbove_P1 : ∀ B, B ∈ strictAbove P1.toFinset ↔ B = P01 := by
  intro B
  rw [mem_strictAbove]
  revert B
  decide

/-- `strictAbove {0,1} = ∅`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem strictAbove_P01 : ∀ B, B ∉ strictAbove P01.toFinset := by
  intro B
  rw [mem_strictAbove]
  revert B
  decide

/-! ### The joint latents over singleton families -/

section Structure

variable {Ω OI OE AI AE DI DE DB OH OC : Type}
variable [Fintype Ω] [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable [Fintype OE] [DecidableEq OE] [Fintype AE] [DecidableEq AE] [Fintype DE] [DecidableEq DE]
  [Fintype DI] [DecidableEq DI] [Fintype DB] [DecidableEq DB]
variable [MeasurableSpace OE] [MeasurableSingletonClass OE] [MeasurableSpace AE]
  [MeasurableSingletonClass AE] [MeasurableSpace DE] [MeasurableSingletonClass DE]
  [MeasurableSpace DI] [MeasurableSingletonClass DI] [MeasurableSpace DB]
  [MeasurableSingletonClass DB]
variable (S : AbstractDS Ω OI OE AI AE DI DE DB OH OC)

/-- The joint latent over a one-element family is the latent, wrapped.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem latRV_jointOn_single (F : Set (PPlus Idx)) (B₀ : PPlus Idx) (hF : ∀ B, B ∈ F ↔ B = B₀) :
    (latRV S).jointOn F = (fun v (_ : ↥F) => v) ∘ latY S B₀ := by
  funext ω B
  show latY S (↑B) ω = latY S B₀ ω
  rw [(hF ↑B).1 B.2]

/-- The wrap `v ↦ (_ ↦ v)` has the evaluation at any member as a left inverse.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem wrap_eval {F : Set (PPlus Idx)} (B₀ : ↥F) (v : LatVal OE AE DE DI DB) :
    (fun v (_ : ↥F) => v) v B₀ = v := rfl

/-- **The `A = P0` clause of the ordered Markov condition is `CondIndepFun D_{I,B} E Π̈`.**
Source: FAF Definition 4.8 at `I = Fin 2` (udt-rep-045)
Kind: L
Fidelity: exact
Hyps: none -/
theorem clause_P0_iff :
    CondIndepFun ((latRV S).X P0) ((latRV S).jointOn (incomparable P0))
        ((latRV S).jointOn (strictAbove P0.toFinset)) (latRV S).P ↔
      CondIndepFun S.DIB S.E S.polE (dsMeasure S) := by
  have hPol : Measurable S.polE := measurable_of_countable _
  rw [latRV_jointOn_single S _ P1 incomparable_P0, latRV_jointOn_single S _ P01 strictAbove_P0]
  have hX : (latRV S).X P0 = Sum.inl ∘ S.DIB := by
    show latY S P0 = _
    rw [latY_P0]
    rfl
  have hY : (fun v (_ : ↥(incomparable P0)) => v) ∘ latY S P1 =
      ((fun v (_ : ↥(incomparable P0)) => v) ∘ (Sum.inr ∘ Sum.inl)) ∘ S.E := by
    rw [latY_P1]
    rfl
  have hZ : (fun v (_ : ↥(strictAbove P0.toFinset)) => v) ∘ latY S P01 =
      ((fun v (_ : ↥(strictAbove P0.toFinset)) => v) ∘ (Sum.inr ∘ Sum.inr)) ∘ S.polE := by
    rw [latY_P01]
    rfl
  rw [hX, hY, hZ]
  exact (condIndepFun_comp_left_iff (g' := dDIB S) (measurable_of_countable _)
      (measurable_of_countable _) fun _ => rfl).trans
    ((condIndepFun_comp_mid_iff (g' := fun w => dE S (w ⟨P1, (incomparable_P0 P1).2 rfl⟩))
      (measurable_of_countable _) (measurable_of_countable _) fun _ => rfl).trans
      (condIndepFun_comp_cond_iff hPol (measurable_of_countable _) fun π π' h =>
        Sum.inr_injective (Sum.inr_injective (congrFun h ⟨P01, (strictAbove_P0 P01).2 rfl⟩))))

/-- **The `A = P1` clause of the ordered Markov condition is `CondIndepFun E D_{I,B} Π̈`.**
Source: FAF Definition 4.8 at `I = Fin 2` (udt-rep-045)
Kind: L
Fidelity: exact
Hyps: none -/
theorem clause_P1_iff :
    CondIndepFun ((latRV S).X P1) ((latRV S).jointOn (incomparable P1))
        ((latRV S).jointOn (strictAbove P1.toFinset)) (latRV S).P ↔
      CondIndepFun S.E S.DIB S.polE (dsMeasure S) := by
  have hPol : Measurable S.polE := measurable_of_countable _
  rw [latRV_jointOn_single S _ P0 incomparable_P1, latRV_jointOn_single S _ P01 strictAbove_P1]
  have hX : (latRV S).X P1 = (Sum.inr ∘ Sum.inl) ∘ S.E := by
    show latY S P1 = _
    rw [latY_P1]
    rfl
  have hY : (fun v (_ : ↥(incomparable P1)) => v) ∘ latY S P0 =
      ((fun v (_ : ↥(incomparable P1)) => v) ∘ Sum.inl) ∘ S.DIB := by
    rw [latY_P0]
    rfl
  have hZ : (fun v (_ : ↥(strictAbove P1.toFinset)) => v) ∘ latY S P01 =
      ((fun v (_ : ↥(strictAbove P1.toFinset)) => v) ∘ (Sum.inr ∘ Sum.inr)) ∘ S.polE := by
    rw [latY_P01]
    rfl
  rw [hX, hY, hZ]
  exact (condIndepFun_comp_left_iff (g' := dE S) (measurable_of_countable _)
      (measurable_of_countable _) fun _ => rfl).trans
    ((condIndepFun_comp_mid_iff (g' := fun w => dDIB S (w ⟨P0, (incomparable_P1 P0).2 rfl⟩))
      (measurable_of_countable _) (measurable_of_countable _) fun _ => rfl).trans
      (condIndepFun_comp_cond_iff hPol (measurable_of_countable _) fun π π' h =>
        Sum.inr_injective (Sum.inr_injective (congrFun h ⟨P01, (strictAbove_P1 P01).2 rfl⟩))))

/-- **The `A = P01` clause of the ordered Markov condition holds trivially** (nothing is
incomparable to the top).
Source: FAF Definition 4.8 at `I = Fin 2` (udt-rep-045)
Kind: L
Fidelity: exact
Hyps: none -/
theorem clause_P01 :
    CondIndepFun ((latRV S).X P01) ((latRV S).jointOn (incomparable P01))
      ((latRV S).jointOn (strictAbove P01.toFinset)) (latRV S).P := by
  haveI : IsEmpty ↥(incomparable P01) := ⟨fun B => incomparable_P01 B.1 B.2⟩
  exact condIndepFun_of_isEmpty_mid (μ := dsMeasure S) (measurable_of_countable _) _

/-! ### T9(b): DD is the ordered-Markov clause -/

/-- **The ordered Markov condition of the policy latent model is DD's clause (2)
(T9(b), load-bearing 3)**: FAF's `RVModel.OrderedMarkov` (Definition 4.8) for `polLatent S`
is exactly `CondIndepFun S.E S.DIB S.polE`, i.e. (T7(b)) the conditional-independence clause of
`udt-comm-trust`'s `DecisionDetermined`. Docstring of record: *the corpus's DD is the
ordered-Markov clause of Theorem 4.9(B) without its function clause.*
Source: [[topics/decision-determination]] line 99 (udt-rep-045); FAF Definition 4.8, Theorem 4.9
Kind: P
Fidelity: exact
Hyps: (a); `udt-comm-trust` §3 (c) by reference -/
theorem orderedMarkov_polLatent_iff_dd :
    (polLatent S).L.OrderedMarkov ↔ CondIndepFun S.E S.DIB S.polE (dsMeasure S) := by
  constructor
  · intro h
    exact (clause_P1_iff S).1 (h P1)
  · intro h A
    rcases pplus_cases A with rfl | rfl | rfl
    · exact (clause_P0_iff S).2 (condIndepFun_symm h)
    · exact (clause_P1_iff S).2 h
    · exact clause_P01 S

/-- **The ordered Markov condition of the policy latent model, in DD's own terms.**
Source: [[topics/decision-determination]] line 99 (udt-rep-045)
Kind: C
Fidelity: exact
Hyps: (a); `udt-comm-trust` §3 (c) by reference -/
theorem orderedMarkov_polLatent_of_dd (h : S.DecisionDetermined) :
    (polLatent S).L.OrderedMarkov :=
  (orderedMarkov_polLatent_iff_dd S).2 ((decisionDetermined_iff_condIndepFun S).1 h).2

/-- **Under DD, perfect condensation by the policy latent is Theorem 4.9(B)'s function clause**
(`perfect_tfae_B` with the Markov clause discharged by DD).
Source: [[topics/decision-determination]] line 99 (udt-rep-045); FAF Theorem 4.9
Kind: C
Fidelity: exact
Hyps: (a) `h`; `udt-comm-trust` §3 (c) by reference -/
theorem perfectlyCondenses_polLatent_iff_of_dd (h : S.DecisionDetermined) :
    (polLatent S).PerfectlyCondenses ↔
      ∀ (i : Idx) (A : PPlus Idx), i ∈ A →
        AEFunctionOf ((rvModel S).X i ∘ (polLatent S).π) ((polLatent S).Y A) (polLatent S).P := by
  rw [LatentModel.perfect_tfae_B]
  exact and_iff_left (orderedMarkov_polLatent_of_dd S h)

/-- **Under DD, perfect condensation by the policy latent is exactly `Π̈ ⊑ E`**: every other
instance of the function clause holds by construction (`Y P0 = X 0`, `Y P1 = X 1`, and
`Π̈ = [[D_{I,B}]]_Π̈` is a function of `X 0 = D_{I,B}`), so under DD "Π̈ is a perfect condensation
variable" reduces to "the environment determines the policy". The note's sentence is therefore
true precisely for decision-determined structures in which `Π̈` is a function of `E` — and
false otherwise (`WitnessLatent.lean`).
Source: [[topics/decision-determination]] line 99 (udt-rep-045)
Kind: C
Fidelity: exact
Hyps: (a) `h`; `udt-comm-trust` §3 (c) by reference -/
theorem perfectlyCondenses_polLatent_iff_isSubvariable_of_dd (h : S.DecisionDetermined) :
    (polLatent S).PerfectlyCondenses ↔ IsSubvariable S.E S.polE := by
  constructor
  · exact isSubvariable_polE_of_perfectlyCondenses S
  · intro hsub
    rw [perfectlyCondenses_polLatent_iff_of_dd S h]
    intro i A hiA
    have hfun : ∀ (X : Ω → LatVal OE AE DE DI DB) (g : LatVal OE AE DE DI DB → LatVal OE AE DE DI DB),
        AEFunctionOf X (g ∘ X) (dsMeasure S) := fun X g =>
      AEFunctionOf.of_functionOf ⟨g, measurable_of_countable g, fun _ => rfl⟩
    have hE : AEFunctionOf (cE S) (cPolE S) (dsMeasure S) := by
      haveI : Nonempty (OE → AE) := ⟨S.polE S.w₀⟩
      obtain ⟨f, hf⟩ := (isSubvariable_iff_exists S.E S.polE).1 hsub
      have : cPolE S = (Sum.inr ∘ Sum.inr ∘ f ∘ dE S) ∘ cE S := by
        funext ω
        show Sum.inr (Sum.inr (S.polE ω)) = Sum.inr (Sum.inr (f (S.E ω)))
        rw [hf ω]
      rw [this]
      exact hfun _ _
    have hD : AEFunctionOf (cDIB S) (cPolE S) (dsMeasure S) := by
      have : cPolE S = (Sum.inr ∘ Sum.inr ∘ S.polOf ∘ dDIB S) ∘ cDIB S := by
        funext ω
        rfl
      rw [this]
      exact hfun _ _
    show AEFunctionOf (rvX S i ∘ id) (latY S A) (dsMeasure S)
    rcases pplus_cases A with rfl | rfl | rfl
    · have hi : i = 0 := Finset.mem_singleton.1 (PPlus.mem_iff.1 hiA)
      subst hi
      rw [latY_P0, rvX_zero]
      exact aeFunctionOf_self
    · have hi : i = 1 := Finset.mem_singleton.1 (PPlus.mem_iff.1 hiA)
      subst hi
      rw [latY_P1, rvX_one]
      exact aeFunctionOf_self
    · rw [latY_P01]
      revert i
      rw [Fin.forall_fin_two]
      refine ⟨fun _ => ?_, fun _ => ?_⟩
      · rw [rvX_zero]; exact hD
      · rw [rvX_one]; exact hE

end Structure

end

end Cleanroom.Udt.UdtCondenseDd

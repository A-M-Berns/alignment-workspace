import Cleanroom.Udt.UdtCommTrust.Determination
import Condensation.Probability
import ShannonInformation.API
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# `Cleanroom.Udt.UdtCondenseDd.Bridge`: from the finite decision structure to FAF's measure-theoretic objects (T7)

Work package `udt-condense-dd`, target T7 (udt-rep-2-032, 2-027, 2-028, 2-029, 041). The one bridge
the area needs: `udt-comm-trust`'s finite `AbstractDS` (a `FinDist` on a finite support `Ω`) is
carried to a `MeasureTheory.Measure` (`FinDist.toMeasure`, the recipe of
`Cleanroom/Info/InfoVoiLatents/Bridge.lean:44–70`), where

* every a.e. statement of FAF is an everywhere statement (`FinDist.ae_iff_forall_of_pos`,
  because `Ω` is the support);
* `IsSubvariable X Y` **is** `Condensation.AEFunctionOf X Y` (`isSubvariable_iff_aeFunctionOf`,
  T7(a)) — the equality `udt-comm-trust` §3 promised;
* clause (2) of `DecisionDetermined` **is** PFR's `CondIndepFun S.E S.DIB S.polE`
  (`decisionDetermined_iff_condIndepFun`, T7(b)), atom by atom;
* hence DD **is** `IsSubvariable S.E S.U ∧ I[S.E : S.DIB | S.polE ; S.toMeasure] = 0`
  (`decisionDetermined_iff_condMutualInfo_eq_zero`, T7(c)) by FAF's
  `ShannonInformation.condMutualInfo_eq_zero`.

**No `(c)` here.** The support carrier is `udt-comm-trust`'s disclosed variant (its §3 (c), cited
by reference); every bridge below is an equivalence.

Measurable structure: `Ω` and the value types carry any `MeasurableSpace` with measurable
singletons (on a countable type every set and every function is then measurable:
`measurable_of_countable`). Witnesses use `Fin n` and products, whose instances Mathlib provides.
-/

namespace Cleanroom.Udt.UdtCondenseDd

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust MeasureTheory ProbabilityTheory Finset
open Condensation

noncomputable section

set_option linter.unusedSectionVars false

/-! ### `FinDist` as a measure -/

section FinDistMeasure

variable {Ω : Type} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- A finite distribution as a `PMF`: `ω ↦ ENNReal.ofReal (μ.w ω)`.
Source: none: infrastructure (mandate §3, layer B; the recipe of `Cleanroom/Info/InfoVoiLatents/Bridge.lean:44–70`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def distPMF (μ : FinDist Ω) : PMF Ω :=
  PMF.ofFintype (fun ω => ENNReal.ofReal (μ.w ω)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun ω _ => μ.nonneg ω, μ.sum_one, ENNReal.ofReal_one])

/-- **A finite distribution as a probability measure** on `Ω`.
Source: none: infrastructure (mandate §3, layer B)
Kind: D
Fidelity: exact
Hyps: n/a -/
def distMeasure (μ : FinDist Ω) : Measure Ω := (distPMF μ).toMeasure

instance distMeasure_isProbabilityMeasure (μ : FinDist Ω) :
    IsProbabilityMeasure (distMeasure μ) := by
  unfold distMeasure
  infer_instance

/-- Point masses of `toMeasure`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem distMeasure_singleton (μ : FinDist Ω) (ω : Ω) :
    distMeasure μ {ω} = ENNReal.ofReal (μ.w ω) := by
  rw [distMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton ω)]
  rfl

/-- The measure of a finite event is the `ofReal` of its mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem distMeasure_finset (μ : FinDist Ω) (E : Finset Ω) :
    distMeasure μ ↑E = ENNReal.ofReal (mass μ.w E) := by
  rw [distMeasure, PMF.toMeasure_apply_finset, mass,
    ENNReal.ofReal_sum_of_nonneg fun ω _ => μ.nonneg ω]
  rfl

/-- The measure of `{ω | P ω}` is the `ofReal` of the mass of `event P`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem distMeasure_setOf (μ : FinDist Ω) (P : Ω → Prop) [DecidablePred P] :
    distMeasure μ {ω | P ω} = ENNReal.ofReal (mass μ.w (event P)) := by
  have h : ({ω | P ω} : Set Ω) = ↑(event P) := by
    ext ω
    simp
  rw [h, distMeasure_finset]

/-- **On the support, almost everywhere is everywhere**: when every weight is positive, an a.e.
statement under `toMeasure` is a universal statement. This is the lemma that makes every a.e.
statement of FAF an everywhere statement over `udt-comm-trust`'s structures.
Source: none: infrastructure (mandate §3, layer B; `udt-comm-trust` §3 (c) by reference)
Kind: L
Fidelity: exact
Hyps: none -/
theorem distMeasure_ae_iff_forall_of_pos (μ : FinDist Ω) (hpos : ∀ ω, 0 < μ.w ω) (P : Ω → Prop) :
    (∀ᵐ ω ∂distMeasure μ, P ω) ↔ ∀ ω, P ω := by
  rw [ae_iff_of_countable]
  constructor
  · intro h ω
    refine h ω ?_
    rw [distMeasure_singleton]
    exact (ENNReal.ofReal_pos.2 (hpos ω)).ne'
  · intro h ω _
    exact h ω

/-- Supporting lemma: a set of positive `toMeasure` has a point.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem exists_of_measure_ne_zero {Ω' : Type} [MeasurableSpace Ω'] (ν : Measure Ω') {s : Set Ω'}
    (h : ν s ≠ 0) : ∃ ω, ω ∈ s := by
  by_contra hne
  have : s = ∅ := Set.eq_empty_iff_forall_notMem.2 fun ω hω => hne ⟨ω, hω⟩
  rw [this, measure_empty] at h
  exact h rfl

end FinDistMeasure

/-! ### Independence on a countable discrete space, atom by atom -/

/-- **Independence is the product rule on singletons** (countable discrete ranges, finite measure).
Source: none: infrastructure (mandate T7(b), `indepFun_iff_of_finite`)
Kind: L
Fidelity: exact
Hyps: none -/
theorem indepFun_iff_singleton {Ω' : Type} [MeasurableSpace Ω'] (ν : Measure Ω') [IsFiniteMeasure ν]
    {V W : Type} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
    [MeasurableSpace W] [Countable W] [MeasurableSingletonClass W] {X : Ω' → V} {Y : Ω' → W}
    (hX : Measurable X) (hY : Measurable Y) :
    IndepFun X Y ν ↔ ∀ v w, ν (X ⁻¹' {v} ∩ Y ⁻¹' {w}) = ν (X ⁻¹' {v}) * ν (Y ⁻¹' {w}) := by
  have hpre : ∀ v w, (fun ω => (X ω, Y ω)) ⁻¹' {(v, w)} = X ⁻¹' {v} ∩ Y ⁻¹' {w} := by
    intro v w
    ext ω
    simp [Prod.ext_iff]
  rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable,
    Measure.ext_iff_singleton]
  constructor
  · intro h v w
    have := h (v, w)
    rw [Measure.map_apply (hX.prodMk hY) (measurableSet_singleton _), hpre] at this
    rwa [← Set.singleton_prod_singleton, Measure.prod_prod,
      Measure.map_apply hX (measurableSet_singleton _),
      Measure.map_apply hY (measurableSet_singleton _)] at this
  · rintro h ⟨v, w⟩
    rw [Measure.map_apply (hX.prodMk hY) (measurableSet_singleton _), hpre,
      ← Set.singleton_prod_singleton, Measure.prod_prod,
      Measure.map_apply hX (measurableSet_singleton _),
      Measure.map_apply hY (measurableSet_singleton _)]
    exact h v w

/-- **The conditional product rule on a fibre, division-free**: for `μ P ≠ 0` (finite), sets
`A ⊆ P` and `C ⊆ P`, `μ[A | P] = μ[B | P] · μ[C | P] ↔ μ A · μ P = μ (P ∩ B) · μ C`.
Source: none: infrastructure (mandate T7(b))
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cond_product_iff {Ω' : Type} [MeasurableSpace Ω'] (μ : Measure Ω') [IsFiniteMeasure μ]
    {P A B C : Set Ω'} (hP : MeasurableSet P) (hP0 : μ P ≠ 0) (hA : A ⊆ P) (hC : C ⊆ P) :
    μ[A | P] = μ[B | P] * μ[C | P] ↔ μ A * μ P = μ (P ∩ B) * μ C := by
  have hPt : μ P ≠ ⊤ := measure_ne_top μ P
  rw [cond_apply hP, cond_apply hP, cond_apply hP, Set.inter_eq_right.2 hA, Set.inter_eq_right.2 hC]
  constructor
  · intro h
    have h' := congrArg (fun x => μ P * μ P * x) h
    calc μ A * μ P = μ P * μ P * ((μ P)⁻¹ * μ A) := by
          rw [mul_assoc (μ P), ← mul_assoc (μ P) (μ P)⁻¹, ENNReal.mul_inv_cancel hP0 hPt, one_mul,
            mul_comm]
      _ = μ P * μ P * ((μ P)⁻¹ * μ (P ∩ B) * ((μ P)⁻¹ * μ C)) := h'
      _ = μ (P ∩ B) * μ C := by
          calc μ P * μ P * ((μ P)⁻¹ * μ (P ∩ B) * ((μ P)⁻¹ * μ C))
              = (μ P * (μ P)⁻¹) * (μ P * (μ P)⁻¹) * (μ (P ∩ B) * μ C) := by ring
            _ = μ (P ∩ B) * μ C := by rw [ENNReal.mul_inv_cancel hP0 hPt, one_mul, one_mul]
  · intro h
    calc (μ P)⁻¹ * μ A = (μ P)⁻¹ * (μ P)⁻¹ * (μ A * μ P) := by
          rw [mul_assoc, mul_comm (μ A), ← mul_assoc (μ P)⁻¹ (μ P), ENNReal.inv_mul_cancel hP0 hPt,
            one_mul]
      _ = (μ P)⁻¹ * (μ P)⁻¹ * (μ (P ∩ B) * μ C) := by rw [h]
      _ = (μ P)⁻¹ * μ (P ∩ B) * ((μ P)⁻¹ * μ C) := by ring

/-- Supporting lemma: `ofReal a · ofReal b = ofReal c · ofReal d ↔ a b = c d` for non-negative reals.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem ofReal_mul_eq_ofReal_mul_iff {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) :
    ENNReal.ofReal a * ENNReal.ofReal b = ENNReal.ofReal c * ENNReal.ofReal d ↔ a * b = c * d := by
  rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hc,
    ENNReal.ofReal_eq_ofReal_iff (mul_nonneg ha hb) (mul_nonneg hc hd)]

/-! ### The abstract decision structure as a probability space (T7) -/

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

/-- **The prior of an abstract decision structure as a probability measure** on its support `Ω`.
Source: none: infrastructure (mandate §3, layer B; `udt-comm-trust` §3 (c) by reference)
Kind: D
Fidelity: exact
Hyps: n/a -/
def dsMeasure : Measure Ω := distMeasure S.μ

instance dsMeasure_isProbabilityMeasure : IsProbabilityMeasure (dsMeasure S) := by
  unfold dsMeasure
  infer_instance

/-- On a structure, a.e. is everywhere (`Ω` is the support).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem dsMeasure_ae_iff (P : Ω → Prop) : (∀ᵐ ω ∂dsMeasure S, P ω) ↔ ∀ ω, P ω :=
  distMeasure_ae_iff_forall_of_pos S.μ S.pos P

/-- The measure of `{ω | P ω}` is the `ofReal` of the mass of `event P`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem dsMeasure_setOf (P : Ω → Prop) [DecidablePred P] :
    dsMeasure S {ω | P ω} = ENNReal.ofReal (mass S.μ.w (event P)) :=
  distMeasure_setOf S.μ P

/-- **`IsSubvariable` is `AEFunctionOf` (T7(a))**: on a structure (a finite support carrier, any
measurable structure with measurable singletons on the domain value type), `udt-comm-trust`'s
"function of on the support" is exactly FAF's "a.e. a measurable function of". Fidelity: exact —
this is the equality `udt-comm-trust` §3 promised.
Source: [[communication-trust-translated]] lines 200–206 vs FAF `Condensation.AEFunctionOf` (udt-rep-2-028, 2-032)
Kind: P
Fidelity: exact
Hyps: (a); `udt-comm-trust` §3 (c) by reference (the carrier is the support) -/
theorem isSubvariable_iff_aeFunctionOf {V W : Type} [MeasurableSpace V] [Countable V]
    [MeasurableSingletonClass V] [MeasurableSpace W] (X : Ω → V) (Y : Ω → W) :
    IsSubvariable X Y ↔ AEFunctionOf X Y (dsMeasure S) := by
  haveI : Nonempty W := ⟨Y S.w₀⟩
  rw [isSubvariable_iff_exists]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, measurable_of_countable f, (dsMeasure_ae_iff S _).2 hf⟩
  · rintro ⟨f, -, hf⟩
    exact ⟨f, (dsMeasure_ae_iff S _).1 hf⟩

/-- Supporting lemma: the `Π̈`-fibre of `[[d]]_Π̈` contains the `D_{I,B}`-fibre of `d` and any of its
subsets.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem preimage_DIB_subset_preimage_polE (d : DI × DB) :
    S.DIB ⁻¹' {d} ⊆ S.polE ⁻¹' {S.polOf d} := by
  intro ω hω
  have hd : S.DIB ω = d := hω
  show S.polE ω = S.polOf d
  rw [AbstractDS.polE_eq, hd]

/-- **Clause (2) of decision-determination is `CondIndepFun E D_{I,B} Π̈` (T7(b), the plumbing)**:
PFR's conditional independence — a.e. over the law of `Π̈`, independence under the conditional
measure on each fibre — is, on the support carrier, the division-free atom identity of
`udt-comm-trust`'s `DecisionDetermined` clause (2), atom by atom.
Source: [[communication-trust-translated]] lines 381–390 vs PFR `CondIndepFun` (udt-rep-2-032)
Kind: P
Fidelity: exact
Hyps: (a); `udt-comm-trust` §3 (c) by reference -/
theorem condIndepFun_iff_dd2 :
    CondIndepFun S.E S.DIB S.polE (dsMeasure S) ↔
      ∀ (e : AE × DE) (d : DI × DB),
        mass S.μ.w (event fun ω => S.E ω = e ∧ S.DIB ω = d) * mass S.μ.w (S.evPolE (S.polOf d)) =
          mass S.μ.w (event fun ω => S.E ω = e ∧ S.polE ω = S.polOf d) * mass S.μ.w (S.evDIB d) := by
  have hE : Measurable S.E := measurable_of_countable _
  have hD : Measurable S.DIB := measurable_of_countable _
  have hPol : Measurable S.polE := measurable_of_countable _
  have hP : ∀ z : OE → AE, MeasurableSet (S.polE ⁻¹' {z}) := fun z =>
    hPol (measurableSet_singleton z)
  -- the four sets, as masses
  have mA : ∀ (e : AE × DE) (d : DI × DB), dsMeasure S (S.E ⁻¹' {e} ∩ S.DIB ⁻¹' {d}) =
      ENNReal.ofReal (mass S.μ.w (event fun ω => S.E ω = e ∧ S.DIB ω = d)) := fun e d =>
    dsMeasure_setOf S fun ω => S.E ω = e ∧ S.DIB ω = d
  have mP : ∀ d : DI × DB, dsMeasure S (S.polE ⁻¹' {S.polOf d}) =
      ENNReal.ofReal (mass S.μ.w (S.evPolE (S.polOf d))) := fun d =>
    dsMeasure_setOf S fun ω => S.polE ω = S.polOf d
  have mB : ∀ (e : AE × DE) (d : DI × DB), dsMeasure S (S.polE ⁻¹' {S.polOf d} ∩ S.E ⁻¹' {e}) =
      ENNReal.ofReal (mass S.μ.w (event fun ω => S.E ω = e ∧ S.polE ω = S.polOf d)) := by
    intro e d
    have : S.polE ⁻¹' {S.polOf d} ∩ S.E ⁻¹' {e} = {ω | S.E ω = e ∧ S.polE ω = S.polOf d} :=
      Set.ext fun ω => and_comm
    rw [this]
    exact dsMeasure_setOf S _
  have mC : ∀ d : DI × DB, dsMeasure S (S.DIB ⁻¹' {d}) =
      ENNReal.ofReal (mass S.μ.w (S.evDIB d)) := fun d =>
    dsMeasure_setOf S fun ω => S.DIB ω = d
  have hnn := mass_nonneg S.μ.nonneg
  constructor
  · intro h e d
    by_cases hd : (S.evDIB d).Nonempty
    · have hPz : (S.evPolE (S.polOf d)).Nonempty := hd.mono (S.evDIB_subset_evPolE d)
      have hμP : dsMeasure S (S.polE ⁻¹' {S.polOf d}) ≠ 0 := by
        rw [mP]
        exact (ENNReal.ofReal_pos.2 (mass_pos_of_nonempty S.pos hPz)).ne'
      have hind : IndepFun S.E S.DIB ((dsMeasure S)[|S.polE ⁻¹' {S.polOf d}]) := by
        rw [condIndepFun_iff, ae_iff_of_countable] at h
        refine h (S.polOf d) ?_
        rw [Measure.map_apply hPol (measurableSet_singleton _)]
        exact hμP
      haveI : IsProbabilityMeasure ((dsMeasure S)[|S.polE ⁻¹' {S.polOf d}]) :=
        cond_isProbabilityMeasure hμP
      rw [indepFun_iff_singleton _ hE hD] at hind
      have key := hind e d
      rw [cond_product_iff (dsMeasure S) (hP _) hμP
        (Set.inter_subset_right.trans (preimage_DIB_subset_preimage_polE S d))
        (preimage_DIB_subset_preimage_polE S d), mA, mP, mB, mC,
        ofReal_mul_eq_ofReal_mul_iff (hnn _) (hnn _) (hnn _) (hnn _)] at key
      exact key
    · rw [Finset.not_nonempty_iff_eq_empty] at hd
      have h0 : (event fun ω => S.E ω = e ∧ S.DIB ω = d) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro ω hω
        rw [mem_event] at hω
        have : ω ∈ S.evDIB d := by rw [AbstractDS.mem_evDIB]; exact hω.2
        rw [hd] at this
        exact absurd this (Finset.notMem_empty ω)
      rw [h0, hd]
      simp [mass]
  · intro h
    rw [condIndepFun_iff, ae_iff_of_countable]
    intro z hz
    rw [Measure.map_apply hPol (measurableSet_singleton z)] at hz
    haveI : IsProbabilityMeasure ((dsMeasure S)[|S.polE ⁻¹' {z}]) := cond_isProbabilityMeasure hz
    rw [indepFun_iff_singleton _ hE hD]
    intro e d
    by_cases hdz : S.polOf d = z
    · subst hdz
      rw [cond_product_iff (dsMeasure S) (hP _) hz
        (Set.inter_subset_right.trans (preimage_DIB_subset_preimage_polE S d))
        (preimage_DIB_subset_preimage_polE S d), mA, mP, mB, mC,
        ofReal_mul_eq_ofReal_mul_iff (hnn _) (hnn _) (hnn _) (hnn _)]
      exact h e d
    · have hempty : S.polE ⁻¹' {z} ∩ S.DIB ⁻¹' {d} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro ω ⟨hω, hωd⟩
        have h1 : S.polE ω = z := hω
        have h2 : S.DIB ω = d := hωd
        apply hdz
        rw [← h2, ← AbstractDS.polE_eq, h1]
      have hC0 : (dsMeasure S)[S.DIB ⁻¹' {d} | S.polE ⁻¹' {z}] = 0 := by
        rw [cond_apply (hP z), hempty, measure_empty, mul_zero]
      have hA0 : (dsMeasure S)[S.E ⁻¹' {e} ∩ S.DIB ⁻¹' {d} | S.polE ⁻¹' {z}] = 0 := by
        rw [cond_apply (hP z)]
        have : S.polE ⁻¹' {z} ∩ (S.E ⁻¹' {e} ∩ S.DIB ⁻¹' {d}) = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro ω ⟨hω, -, hωd⟩
          have : ω ∈ S.polE ⁻¹' {z} ∩ S.DIB ⁻¹' {d} := ⟨hω, hωd⟩
          rw [hempty] at this
          exact this
        rw [this, measure_empty, mul_zero]
      rw [hA0, hC0, mul_zero]

/-- **Decision-determination is `U ⊑ E` together with PFR's `CondIndepFun E D_{I,B} Π̈` (T7(b))**.
Source: [[communication-trust-translated]] lines 381–390; [[topics/decision-determination]] lines 7–19 (udt-rep-2-032)
Kind: P
Fidelity: exact
Hyps: (a); `udt-comm-trust` §3 (c) by reference -/
theorem decisionDetermined_iff_condIndepFun :
    S.DecisionDetermined ↔ (IsSubvariable S.E S.U ∧ CondIndepFun S.E S.DIB S.polE (dsMeasure S)) := by
  unfold AbstractDS.DecisionDetermined
  rw [condIndepFun_iff_dd2]

/-- **Decision-determination is `U ⊑ E ∧ I[E : D_{I,B} | Π̈] = 0` (T7(c))**: the entropy form of
DD, by T7(b) and FAF's `ShannonInformation.condMutualInfo_eq_zero`. This is the form in which
T3/T4's approximate DD is to be *read* (`I[…] ≤ δ`); the entropy-level approximate DD theorem itself
is `Entropy.lean`'s `approxDD_entropy` (proved in repair round 1; the open list is empty). The
removed outline's `D_B` for `D_{I,B}` (udt-rep-2-032) is a slip:
the conditioning is on `Π̈` and the independent variable is `D_{I,B}`.
Source: [[topics/decision-determination]] lines 7–19, 99 (udt-rep-2-032); [[condensation-connection-attempt]] line 147 ("`I(E ; D | Π) = 0`")
Kind: C
Fidelity: exact
Hyps: (a); `udt-comm-trust` §3 (c) by reference -/
theorem decisionDetermined_iff_condMutualInfo_eq_zero :
    S.DecisionDetermined ↔
      (IsSubvariable S.E S.U ∧ I[S.E : S.DIB | S.polE ; dsMeasure S] = 0) := by
  rw [decisionDetermined_iff_condIndepFun,
    ShannonInformation.condMutualInfo_eq_zero (measurable_of_countable _) (measurable_of_countable _)
      (measurable_of_countable _)]

end Structure

end

end Cleanroom.Udt.UdtCondenseDd

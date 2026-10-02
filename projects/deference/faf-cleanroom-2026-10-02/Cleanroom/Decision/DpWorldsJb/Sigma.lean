import Cleanroom.Decision.DpWorldsJb.Worlds
import Cleanroom.Decision.DpWorldsJb.JoinForm
import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# σ-algebras: probabilities are measures (T1(iv)), Dirac worlds (T7), purely atomic (T8)

Carrier: `MSet X := Subtype (MeasurableSet : Set X → Prop)` with Mathlib's Boolean-algebra
instance; `Jσ X` designates every countable family (v2's convention that a σ-algebra carries
its canonical designation); `Jmax X` designates every family with an infimum.

* **T1(iv)** `prob_sigma_equiv`: `Prob (Jσ X) ≃ {μ : Measure X // IsProbabilityMeasure μ}`.
  The work is continuity-along-designated-meets ⟺ countable additivity for finite measures,
  both ways (`Antitone.measure_iInter` upward; the finite-sup lemma downward).
* **T7** `world_sigma_equiv_point`: for standard Borel `X`, `World (Jσ X) ≃ X` via
  `MeasureTheory.exists_eq_dirac`, round-tripping through both T1 bridges;
  `world_max_equiv_point`: the same for `Jmax`; `isLUB_val_eq_sUnion` (existing suprema are
  unions when singletons are measurable).
* **T8(b)** `purely_atomic_of_singleton_designation`; `no_diffuse_prob_of_singleton_designation`;
  Lebesgue on `[0,1]` is a `Prob (Jσ ℝ)` but no `Prob J` once the singleton family is designated
  (`lebesgue_not_prob_of_singleton_designation`); `diracProb` is a `Prob (Jmax X)`.
-/

namespace Cleanroom.Decision.DpWorldsJb

noncomputable section

open MeasureTheory Set Classical

/-- The σ-algebra of measurable subsets of `X` as a Boolean algebra (Mathlib's
`Subtype.instBooleanAlgebra`).
Source: [[decision-problems-v2]] §1 ("a σ-algebra of sets")
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev MSet (X : Type*) [MeasurableSpace X] : Type _ := Subtype (MeasurableSet : Set X → Prop)

variable {X : Type*} [MeasurableSpace X]

namespace MSet

theorem coe_inf (s t : MSet X) : ((s ⊓ t : MSet X) : Set X) = (s : Set X) ∩ t := rfl
theorem coe_sup (s t : MSet X) : ((s ⊔ t : MSet X) : Set X) = (s : Set X) ∪ t := rfl
theorem coe_compl (s : MSet X) : ((sᶜ : MSet X) : Set X) = (s : Set X)ᶜ := rfl
theorem coe_top : ((⊤ : MSet X) : Set X) = univ := rfl
theorem coe_bot : ((⊥ : MSet X) : Set X) = ∅ := rfl
theorem le_iff (s t : MSet X) : s ≤ t ↔ (s : Set X) ⊆ t := Iff.rfl

theorem disjoint_iff (s t : MSet X) : Disjoint s t ↔ Disjoint (s : Set X) t := by
  rw [_root_.disjoint_iff, _root_.disjoint_iff]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

end MSet

/-- Every countable family of measurable sets has an infimum in `MSet X`: its intersection.
Source: [[decision-problems-v2]] §1 (σ-algebras carry the countable designation)
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem isGLB_sInter (D : Set (MSet X)) (hD : D.Countable) :
    IsGLB D ⟨⋂₀ (Subtype.val '' D),
      MeasurableSet.sInter (hD.image _) (by rintro _ ⟨s, _, rfl⟩; exact s.2)⟩ := by
  constructor
  · intro A hA
    show ⋂₀ (Subtype.val '' D) ⊆ A.1
    exact Set.sInter_subset_of_mem ⟨A, hA, rfl⟩
  · intro b hb
    show b.1 ⊆ ⋂₀ (Subtype.val '' D)
    apply Set.subset_sInter
    rintro _ ⟨A, hA, rfl⟩
    exact hb hA

/-- The canonical designation of a σ-algebra: every countable family (v2's `Δ_σ(X)` convention).
Source: [[decision-problems-v2]] §1 ("a σ-algebra carries its canonical designation")
Kind: D
Fidelity: exact
Hyps: n/a -/
def Jσ (X : Type*) [MeasurableSpace X] : Designation (MSet X) :=
  ⟨{D | D.Countable}, fun D hD => ⟨_, isGLB_sInter D hD⟩⟩

theorem mem_Jσ (D : Set (MSet X)) : D ∈ (Jσ X).1 ↔ D.Countable := Iff.rfl

/-- The maximal designation: every family that has an infimum.
Source: [[decision-problems-v2]] Appendix A "The world/probability mismatch" ("all existing joins")
Kind: D
Fidelity: exact
Hyps: n/a -/
def Jmax (X : Type*) [MeasurableSpace X] : Designation (MSet X) :=
  ⟨{D | ∃ m, IsGLB D m}, fun _ hD => hD⟩

theorem Jσ_le_Jmax : (Jσ X).1 ⊆ (Jmax X).1 := fun D hD => ⟨_, isGLB_sInter D hD⟩

section Singletons

variable [MeasurableSingletonClass X]

/-- With measurable singletons, a point lies in an existing infimum iff it lies in every member
(`m ∪ {x}` would otherwise be a larger measurable lower bound).
Source: [[decision-problems-v2]] Appendix A "Annihilation" (Dirac worlds on Borel algebras)
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem mem_of_isGLB {D : Set (MSet X)} {m : MSet X} (hm : IsGLB D m) (x : X) :
    x ∈ (m : Set X) ↔ ∀ A ∈ D, x ∈ (A : Set X) := by
  constructor
  · intro hx A hA
    exact hm.1 hA hx
  · intro hall
    have : (⟨(m : Set X) ∪ {x}, m.2.union (measurableSet_singleton x)⟩ : MSet X) ≤ m := by
      apply hm.2
      intro A hA
      show (m : Set X) ∪ {x} ⊆ A
      exact Set.union_subset (hm.1 hA) (Set.singleton_subset_iff.2 (hall A hA))
    exact this (Set.mem_union_right _ (Set.mem_singleton x))

/-- With measurable singletons, a point lies in an existing supremum iff it lies in some member
(`m \ {x}` would otherwise be a smaller measurable upper bound).
Source: drafting chat line 1463 ("if `B = ⋁ Aᵢ ⊋ ⋃ Aᵢ`, delete a point of the difference")
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem mem_of_isLUB {D : Set (MSet X)} {m : MSet X} (hm : IsLUB D m) (x : X) :
    x ∈ (m : Set X) ↔ ∃ A ∈ D, x ∈ (A : Set X) := by
  constructor
  · intro hx
    by_contra h
    push Not at h
    have : m ≤ ⟨(m : Set X) \ {x}, m.2.diff (measurableSet_singleton x)⟩ := by
      apply hm.2
      intro A hA
      show (A : Set X) ⊆ (m : Set X) \ {x}
      intro y hy
      refine ⟨hm.1 hA hy, fun hyx => h A hA ?_⟩
      rw [Set.mem_singleton_iff] at hyx
      rw [hyx] at hy
      exact hy
    exact (this hx).2 (Set.mem_singleton x)
  · rintro ⟨A, hA, hx⟩
    exact hm.1 hA hx

/-- **T7, second claim.** In a σ-algebra of sets containing all singletons, every family with a
supremum in the algebra has supremum equal to its union.
Source: drafting chat `2026-07-02__formalizing-decision-problem-consistency-and-coherence` line 1463 | dp-core-2-059
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem isLUB_val_eq_sUnion {D : Set (MSet X)} {m : MSet X} (hm : IsLUB D m) :
    (m : Set X) = ⋃₀ (Subtype.val '' D) := by
  ext x
  rw [mem_of_isLUB hm, Set.mem_sUnion]
  constructor
  · rintro ⟨A, hA, hx⟩
    exact ⟨A, ⟨A, hA, rfl⟩, hx⟩
  · rintro ⟨_, ⟨A, hA, rfl⟩, hx⟩
    exact ⟨A, hA, hx⟩

/-- The point world `{s | x ∈ s}` on a σ-algebra with measurable singletons: a world for
**every** designation `J` (constraint 4 by `mem_of_isGLB`).
Source: [[decision-problems-v2]] Appendix A "Annihilation" ("exactly the Dirac worlds `δ_x`") | dp-core-2-059
Kind: P
Fidelity: exact
Hyps: (a) -/
def diracWorld (J : Designation (MSet X)) (x : X) : World J where
  carrier := {s | x ∈ (s : Set X)}
  exactly_one := fun s => by
    show x ∈ (s : Set X) ↔ ¬ x ∈ (s : Set X)ᶜ
    simp
  upward := fun _ _ h hle => hle h
  meet := fun _ _ h₁ h₂ => ⟨h₁, h₂⟩
  designated := fun _ _ hall _ hm => (mem_of_isGLB hm x).2 hall

theorem mem_diracWorld (J : Designation (MSet X)) (x : X) (s : MSet X) :
    s ∈ diracWorld J x ↔ x ∈ (s : Set X) := Iff.rfl

/-- The Dirac world is a world for the maximal designation (Appendix A: "designating countable
joins yields exactly the Dirac worlds", and designating every existing join changes nothing).
Source: [[decision-problems-v2]] Appendix A "Annihilation" | dp-core-2-059
Kind: C
Fidelity: exact
Hyps: (a) -/
def dirac_world_maximal (x : X) : World (Jmax X) := diracWorld (Jmax X) x

end Singletons

/-! ### T1(iv): probabilities on `(MSet X, Jσ X)` are probability measures -/

/-- A probability measure read as a `Prob (Jσ X)`: `P s := (μ s).toReal`. Continuity along a
countable designated meet is continuity from above (`Antitone.measure_iInter`) along the chain
`B n := D₀ ∩ ⋯ ∩ Dₙ`, cofinal among the finite sub-meets (v2's "upward" step).
Source: [[decision-problems-v2]] §1 ("countably additive … gives the condition") | dp-core-001
Kind: P
Fidelity: exact
Hyps: (a) -/
def Prob.ofMeasure (μ : Measure X) [IsProbabilityMeasure μ] : Prob (Jσ X) where
  P s := (μ s).toReal
  nonneg _ := ENNReal.toReal_nonneg
  top := by
    show (μ univ).toReal = 1
    rw [measure_univ, ENNReal.toReal_one]
  add s t h := by
    show (μ ((s : Set X) ∪ t)).toReal = (μ s).toReal + (μ t).toReal
    rw [measure_union ((MSet.disjoint_iff s t).1 h) t.2,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  cont D hD m hm := by
    have hDc : D.Countable := hD
    constructor
    · rintro _ ⟨F, hF, rfl⟩
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono
      show m ≤ F.inf id
      exact Finset.le_inf fun A hA => hm.1 (hF (Finset.mem_coe.2 hA))
    · intro b hb
      by_cases hDe : D = ∅
      · subst hDe
        have h1 : b ≤ (μ (((∅ : Finset (MSet X)).inf id : MSet X) : Set X)).toReal :=
          hb ⟨∅, by simp, rfl⟩
        have h2 : m = ⊤ := by
          apply le_antisymm le_top
          apply hm.2
          intro A hA
          exact hA.elim
        rw [Finset.inf_empty] at h1
        rw [h2]
        exact h1
      · obtain ⟨f, hf⟩ := hDc.exists_eq_range (Set.nonempty_iff_ne_empty.2 hDe)
        let B : ℕ → MSet X := fun n => (Finset.range (n + 1)).inf f
        have hBanti : Antitone (fun n => ((B n : MSet X) : Set X)) := by
          intro i j hij
          show ((B j) : Set X) ⊆ (B i)
          have : (Finset.range (j + 1)).inf f ≤ (Finset.range (i + 1)).inf f :=
            Finset.inf_mono (Finset.range_mono (Nat.succ_le_succ hij))
          exact this
        have hBmeas : ∀ n, NullMeasurableSet ((B n : MSet X) : Set X) μ :=
          fun n => (B n).2.nullMeasurableSet
        have hiInter : (⋂ n, ((B n : MSet X) : Set X)) = (m : Set X) := by
          have hm' := isGLB_sInter D hDc
          rw [hm.unique hm']
          show (⋂ n, ((B n : MSet X) : Set X)) = ⋂₀ (Subtype.val '' D)
          rw [hf, ← Set.range_comp, Set.sInter_range]
          ext x
          simp only [Set.mem_iInter, Function.comp]
          constructor
          · intro h i
            exact (Finset.inf_le (Finset.mem_range.2 (Nat.lt_succ_self i)) : B i ≤ f i) (h i)
          · intro h n
            have : (⟨⋂ i, ((f i : MSet X) : Set X), MeasurableSet.iInter fun i => (f i).2⟩ :
                MSet X) ≤ (Finset.range (n + 1)).inf f :=
              Finset.le_inf fun i _ => fun y hy => Set.mem_iInter.1 hy i
            exact this (Set.mem_iInter.2 h)
        have hmeasInter : μ (m : Set X) = ⨅ n, μ ((B n : MSet X) : Set X) := by
          rw [← hiInter]
          exact hBanti.measure_iInter hBmeas ⟨0, measure_ne_top _ _⟩
        have hbn : ∀ n, b ≤ (μ ((B n : MSet X) : Set X)).toReal := by
          intro n
          apply hb
          refine ⟨(Finset.range (n + 1)).image f, ?_, ?_⟩
          · rw [Finset.coe_image, hf]
            exact Set.image_subset_range _ _
          · rw [Finset.inf_image]
            rfl
        by_cases hb0 : b ≤ 0
        · exact hb0.trans ENNReal.toReal_nonneg
        · push Not at hb0
          have : ENNReal.ofReal b ≤ μ (m : Set X) := by
            rw [hmeasInter]
            exact le_iInf fun n => (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 (hbn n)
          have := ENNReal.toReal_mono (measure_ne_top _ _) this
          rwa [ENNReal.toReal_ofReal hb0.le] at this

theorem Prob.ofMeasure_apply (μ : Measure X) [IsProbabilityMeasure μ] (s : MSet X) :
    (Prob.ofMeasure μ).P s = (μ s).toReal := rfl

/-- Countable additivity from continuity along the complemented family (v2's "downward" step):
for pairwise disjoint measurable `f`, `P (⋃ f)` is the least upper bound of the finite partial
sums.
Source: [[decision-problems-v2]] §1 ("countable additivity in disguise", downward)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Prob.isLUB_sum_of_pairwise_disjoint (P : Prob (Jσ X)) (f : ℕ → Set X)
    (h : ∀ i, MeasurableSet (f i)) (hd : Pairwise (Function.onFun Disjoint f)) :
    IsLUB (Set.range fun s : Finset ℕ => ∑ i ∈ s, P.P ⟨f i, h i⟩)
      (P.P ⟨⋃ i, f i, MeasurableSet.iUnion h⟩) := by
  let g : ℕ → MSet X := fun i => ⟨f i, h i⟩
  let B : MSet X := ⟨⋃ i, f i, MeasurableSet.iUnion h⟩
  have hD : Set.range (fun i => (g i)ᶜ) ∈ (Jσ X).1 := Set.countable_range _
  have hglb : IsGLB (Set.range fun i => (g i)ᶜ) Bᶜ := by
    constructor
    · rintro _ ⟨i, rfl⟩
      exact compl_le_compl (show g i ≤ B from Set.subset_iUnion f i)
    · intro b hb
      show (b : Set X) ⊆ (⋃ i, f i)ᶜ
      rw [Set.compl_iUnion]
      exact Set.subset_iInter fun i => hb ⟨i, rfl⟩
  have := P.isLUB_range_finset_sup g hD Bᶜ hglb
  rw [compl_compl] at this
  convert this using 2
  funext s
  rw [P.finset_sum s g]
  intro i _ j _ hij
  show Disjoint (g i) (g j)
  exact (MSet.disjoint_iff _ _).2 (hd hij)

/-- A `Prob (Jσ X)` read as a measure, by Carathéodory (`Measure.ofMeasurable`) from
`s ↦ ENNReal.ofReal (P s)`, whose countable additivity is `isLUB_sum_of_pairwise_disjoint`
turned into a `HasSum`.
Source: [[decision-problems-v2]] §1 ("probabilities in the present sense are exactly the countably additive ones") | dp-core-001
Kind: P
Fidelity: exact
Hyps: (a) -/
def Prob.toMeasure (P : Prob (Jσ X)) : Measure X :=
  Measure.ofMeasurable (fun s hs => ENNReal.ofReal (P.P ⟨s, hs⟩))
    (by
      show ENNReal.ofReal (P.P ⊥) = 0
      rw [P.bot, ENNReal.ofReal_zero])
    (by
      intro f h hd
      have hlub := P.isLUB_sum_of_pairwise_disjoint f h hd
      have hnn : ∀ i, 0 ≤ P.P ⟨f i, h i⟩ := fun i => P.nonneg _
      have hsum := hasSum_of_isLUB_of_nonneg _ hnn hlub
      rw [← hsum.tsum_eq, ENNReal.ofReal_tsum_of_nonneg hnn hsum.summable])

theorem Prob.toMeasure_apply (P : Prob (Jσ X)) (s : Set X) (hs : MeasurableSet s) :
    P.toMeasure s = ENNReal.ofReal (P.P ⟨s, hs⟩) :=
  Measure.ofMeasurable_apply s hs

instance Prob.toMeasure_isProbabilityMeasure (P : Prob (Jσ X)) :
    IsProbabilityMeasure P.toMeasure :=
  ⟨by
    rw [P.toMeasure_apply univ MeasurableSet.univ]
    show ENNReal.ofReal (P.P ⊤) = 1
    rw [P.top, ENNReal.ofReal_one]⟩

/-- **T1(iv).** On a σ-algebra with its canonical (countable) designation, the probabilities of
§1 are exactly the probability measures: `P ↦ ofMeasurable (ofReal ∘ P)` and
`μ ↦ toReal ∘ μ` are mutually inverse. Neither side is defined as the other.
Source: [[decision-problems-v2]] §1 lines 24–26 | dp-core-001
Kind: P
Fidelity: exact (v2's `Δ_σ(X)` convention, made a theorem)
Hyps: (a) -/
def prob_sigma_equiv : Prob (Jσ X) ≃ {μ : Measure X // IsProbabilityMeasure μ} where
  toFun P := ⟨P.toMeasure, P.toMeasure_isProbabilityMeasure⟩
  invFun μ := @Prob.ofMeasure X _ μ.1 μ.2
  left_inv P := by
    apply Prob.ext
    funext s
    show (P.toMeasure s).toReal = P.P s
    rw [P.toMeasure_apply s s.2, ENNReal.toReal_ofReal (P.nonneg _)]
  right_inv μ := by
    apply Subtype.ext
    haveI := μ.2
    apply Measure.ext
    intro s hs
    show (Prob.ofMeasure μ.1).toMeasure s = μ.1 s
    rw [Prob.toMeasure_apply _ s hs, Prob.ofMeasure_apply, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- With `J = ∅`, a `Prob` is exactly a finitely additive probability (the continuity clause
is vacuous) — definitional.
Source: [[decision-problems-v2]] §1 ("with `J = ∅` they are exactly the finitely additive ones")
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem prob_empty_designation_iff {E : Type*} [BooleanAlgebra E] (P : E → ℝ) :
    (∃ Q : Prob (∅ : Designation E), Q.P = P) ↔
      (∀ X, 0 ≤ P X) ∧ P ⊤ = 1 ∧ ∀ X Y, Disjoint X Y → P (X ⊔ Y) = P X + P Y := by
  constructor
  · rintro ⟨Q, rfl⟩
    exact ⟨Q.nonneg, Q.top, Q.add⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨P, h1, h2, h3, fun _ hD => hD.elim⟩, rfl⟩

/-! ### T7: Dirac worlds -/

/-- The measure of a two-valued `Prob (Jσ X)` is a zero-one measure.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem Prob.toMeasure_isZeroOne (P : Prob (Jσ X)) (hP : TwoValued P.P) :
    IsZeroOneMeasure P.toMeasure :=
  ⟨fun s hs => by
    rw [P.toMeasure_apply s hs]
    rcases hP ⟨s, hs⟩ with h | h <;> simp [h]⟩

section StandardBorel

variable [StandardBorelSpace X]

/-- The measure of a `Jσ`-world is a Dirac measure (`MeasureTheory.exists_eq_dirac` applied to
the zero-one probability measure obtained through both T1 bridges).
Source: [[decision-problems-v2]] Appendix A "Annihilation" | dp-core-2-059
Kind: P
Fidelity: variant: standard Borel `X` (v2 says Polish; Polish + Borel gives the instance)
Hyps: (a) -/
theorem World.exists_eq_dirac (ω : World (Jσ X)) :
    ∃ x, ω.toProb.toMeasure = Measure.dirac x := by
  haveI := ω.toProb.toMeasure_isZeroOne ω.toProb_twoValued
  exact MeasureTheory.IsZeroOneMeasure.exists_eq_dirac

/-- The point of a `Jσ`-world.
Source: [[decision-problems-v2]] Appendix A "Annihilation"
Kind: D
Fidelity: exact
Hyps: n/a -/
def World.diracPoint (ω : World (Jσ X)) : X := Classical.choose ω.exists_eq_dirac

theorem World.toMeasure_eq_dirac (ω : World (Jσ X)) :
    ω.toProb.toMeasure = Measure.dirac ω.diracPoint :=
  Classical.choose_spec ω.exists_eq_dirac

/-- A `Jσ`-world holds exactly the events containing its point.
Source: [[decision-problems-v2]] Appendix A "Annihilation"
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem World.mem_iff_diracPoint_mem (ω : World (Jσ X)) (s : MSet X) :
    s ∈ ω ↔ ω.diracPoint ∈ (s : Set X) := by
  have h1 : (Measure.dirac ω.diracPoint) (s : Set X) = ENNReal.ofReal (ω.indicator s) := by
    rw [← ω.toMeasure_eq_dirac]
    exact Prob.toMeasure_apply _ _ s.2
  rw [Measure.dirac_apply' _ s.2] at h1
  by_cases hs : s ∈ ω
  · rw [ω.indicator_of_mem hs, ENNReal.ofReal_one] at h1
    refine ⟨fun _ => ?_, fun _ => hs⟩
    by_contra hx
    rw [Set.indicator_of_notMem hx] at h1
    exact zero_ne_one h1
  · rw [ω.indicator_of_notMem hs, ENNReal.ofReal_zero] at h1
    refine ⟨fun h => (hs h).elim, fun hx => ?_⟩
    rw [Set.indicator_of_mem hx] at h1
    exact (one_ne_zero h1).elim

/-- **T7.** On a standard Borel space with the countable designation, worlds are exactly the
points: `World (Jσ X) ≃ X`, `x ↦ {s | x ∈ s}` and `ω ↦` the point of its Dirac measure. The
equivalence round-trips through `world_equiv_twoValuedProb` and `prob_sigma_equiv`; the Dirac
world is not restated as `dirac`.
Source: [[decision-problems-v2]] Appendix A "Annihilation" ("designating countable joins yields exactly the Dirac worlds") | dp-core-2-059
Kind: P
Fidelity: variant: standard Borel `X`, which contains Polish
Hyps: (a) -/
def world_sigma_equiv_point : World (Jσ X) ≃ X where
  toFun := World.diracPoint
  invFun := diracWorld (Jσ X)
  left_inv ω := by
    ext s
    exact (ω.mem_iff_diracPoint_mem s).symm
  right_inv x := by
    have h := (diracWorld (Jσ X) x).mem_iff_diracPoint_mem ⟨{x}, measurableSet_singleton x⟩
    rw [mem_diracWorld] at h
    exact Set.mem_singleton_iff.1 (h.1 (Set.mem_singleton x))

/-- **T7, maximal designation.** Designating every existing meet changes nothing:
`World (Jmax X) ≃ X` as well.
Source: [[decision-problems-v2]] Appendix A "Annihilation"; "The world/probability mismatch" | dp-core-2-059
Kind: C
Fidelity: variant: standard Borel `X`
Hyps: (a) -/
def world_max_equiv_point : World (Jmax X) ≃ X where
  toFun ω := (ω.restrict Jσ_le_Jmax).diracPoint
  invFun := diracWorld (Jmax X)
  left_inv ω := by
    ext s
    have := (ω.restrict Jσ_le_Jmax).mem_iff_diracPoint_mem s
    rw [World.mem_restrict] at this
    exact this.symm
  right_inv x := by
    have h := ((diracWorld (Jmax X) x).restrict Jσ_le_Jmax).mem_iff_diracPoint_mem
      ⟨{x}, measurableSet_singleton x⟩
    rw [World.mem_restrict, mem_diracWorld] at h
    exact Set.mem_singleton_iff.1 (h.1 (Set.mem_singleton x))

/-- **T5(d).** No `Jσ`-world of `Borel ℝ` contains every co-countable set: such a world is
`δ_x`, which omits `{x}ᶜ`.
Source: drafting chat line 1463 (the co-countable filter) | dp-core-2-056(b)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem no_sigma_world_of_cocountable :
    ¬ ∃ ω : World (Jσ X), ∀ s : MSet X, (s : Set X)ᶜ.Countable → s ∈ ω := by
  rintro ⟨ω, hω⟩
  have h := hω ⟨{ω.diracPoint}ᶜ, (measurableSet_singleton _).compl⟩
    (by rw [compl_compl]; exact Set.countable_singleton _)
  rw [ω.mem_iff_diracPoint_mem] at h
  exact h (Set.mem_singleton _)

end StandardBorel

/-- N+ for T7: `ℝ` is standard Borel, and `World (Jσ ℝ)` is nontrivial (it is in bijection
with `ℝ`), so the equivalence is not empty-typed.
Source: [[decision-problems-v2]] Appendix A "Annihilation" (`Borel(X)` for Polish `X`) | dp-core-2-059
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem world_sigma_real_nontrivial : Nontrivial (World (Jσ ℝ)) :=
  (world_sigma_equiv_point (X := ℝ)).nontrivial

/-! ### T8(b): purely atomic probabilities under the singleton designation -/

section Atomic

variable [MeasurableSingletonClass X]

/-- The singleton `{x}` as a measurable event.
Source: [[decision-problems-v2]] Appendix A "The world/probability mismatch"
Kind: D
Fidelity: exact
Hyps: n/a -/
def singletonM (x : X) : MSet X := ⟨{x}, measurableSet_singleton x⟩

/-- `⊤ = ⋁ₓ {x}` in `MSet X`.
Source: [[decision-problems-v2]] Appendix A "The world/probability mismatch" (`[0,1] = ⋁ₓ {x}`)
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem isLUB_singletons_top : IsLUB (Set.range (singletonM (X := X))) (⊤ : MSet X) := by
  constructor
  · rintro _ ⟨x, rfl⟩
    exact le_top
  · intro b hb
    show (univ : Set X) ⊆ b
    intro x _
    exact hb ⟨x, rfl⟩ (Set.mem_singleton x)

/-- The complemented singleton family has infimum `⊥` (the singleton family in the official meet
language).
Source: [[decision-problems-v2]] Appendix A "Typing the designation"
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem isGLB_compl_singletons_bot :
    IsGLB (Set.range fun x : X => (singletonM x)ᶜ) (⊥ : MSet X) := by
  constructor
  · rintro _ ⟨x, rfl⟩
    exact bot_le
  · intro b hb x hx
    exact (hb ⟨x, rfl⟩ hx) (Set.mem_singleton x)

/-- **T8(b).** If the complemented singleton family is designated, every probability is purely
atomic: `1` is the least upper bound of the finite sums `∑_{x ∈ F} P {x}` — for every `ε > 0`
some finite set of points carries mass `> 1 - ε`.
Source: [[decision-problems-v2]] Appendix A "The world/probability mismatch" (line 331) | dp-core-2-060
Kind: P
Fidelity: exact (the sup statement, not "a countable sum of Diracs")
Hyps: (a) -/
theorem purely_atomic_of_singleton_designation (J : Designation (MSet X))
    (hJ : Set.range (fun x : X => (singletonM x)ᶜ) ∈ J.1) (P : Prob J) :
    IsLUB (Set.range fun F : Finset X => ∑ x ∈ F, P.P (singletonM x)) 1 := by
  have := P.isLUB_range_finset_sup singletonM hJ ⊥ isGLB_compl_singletons_bot
  rw [compl_bot, P.top] at this
  convert this using 2
  funext F
  rw [P.finset_sum F singletonM]
  intro x _ y _ hxy
  show Disjoint (singletonM x) (singletonM y)
  rw [MSet.disjoint_iff]
  exact Set.disjoint_singleton.2 hxy

/-- No diffuse probability (all singletons null) exists once the complemented singleton family is
designated.
Source: [[decision-problems-v2]] Appendix A "The world/probability mismatch" ("Lebesgue measure would need `1` to be a supremum of finite sums of `0`")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem no_diffuse_prob_of_singleton_designation (J : Designation (MSet X))
    (hJ : Set.range (fun x : X => (singletonM x)ᶜ) ∈ J.1) :
    ¬ ∃ P : Prob J, ∀ x, P.P (singletonM x) = 0 := by
  rintro ⟨P, hP⟩
  have h := purely_atomic_of_singleton_designation J hJ P
  have : (1 : ℝ) ≤ 0 := by
    apply h.2
    rintro _ ⟨F, rfl⟩
    simp [hP]
  linarith

/-- The complemented singleton family is designated by `Jmax`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem compl_singletons_mem_Jmax :
    Set.range (fun x : X => (singletonM x)ᶜ) ∈ (Jmax X).1 :=
  ⟨⊥, isGLB_compl_singletons_bot⟩

/-- The Dirac probability `δ_x` on `(MSet X, J)` for any designation `J`, obtained from the Dirac
world through T1 (not defined as `dirac`).
Source: [[decision-problems-v2]] Appendix A "The world/probability mismatch" (`δ_x`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def diracProb (J : Designation (MSet X)) (x : X) : Prob J :=
  (world_equiv_twoValuedProb J (diracWorld J x)).1

theorem diracProb_apply (J : Designation (MSet X)) (x : X) (s : MSet X) :
    (diracProb J x).P s = if x ∈ (s : Set X) then 1 else 0 := rfl

/-- **N+ for T8(b).** `δ_x` is a `Prob (Jmax X)`, so the hypothesis package of
`purely_atomic_of_singleton_designation` (a designation containing the complemented singleton
family, and a probability for it) is inhabited; its finite sums reach `1` at `F = {x}`.
Source: [[decision-problems-v2]] Appendix A "The world/probability mismatch" | dp-core-2-060
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem diracProb_purely_atomic (x : X) :
    IsLUB (Set.range fun F : Finset X => ∑ y ∈ F, (diracProb (Jmax X) x).P (singletonM y)) 1 ∧
      ∑ y ∈ ({x} : Finset X), (diracProb (Jmax X) x).P (singletonM y) = 1 := by
  refine ⟨purely_atomic_of_singleton_designation _ compl_singletons_mem_Jmax _, ?_⟩
  rw [Finset.sum_singleton, diracProb_apply]
  simp [singletonM]

end Atomic

/-! #### Lebesgue measure on `[0,1]` -/

/-- Lebesgue measure restricted to `[0,1]`, a probability measure on `ℝ`.
Source: [[decision-problems-v2]] Appendix A "The world/probability mismatch"
Kind: D
Fidelity: exact
Hyps: n/a -/
def lebesgueUnit : Measure ℝ := volume.restrict (Icc 0 1)

instance lebesgueUnit_isProbabilityMeasure : IsProbabilityMeasure lebesgueUnit := by
  refine ⟨?_⟩
  rw [lebesgueUnit, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
  simp

/-- Lebesgue measure restricted to `[0,1]` as a `Prob (Jσ ℝ)` (through T1(iv)).
Source: [[decision-problems-v2]] Appendix A "The world/probability mismatch" | dp-core-2-060
Kind: D
Fidelity: variant: carrier `Borel(ℝ)` with the measure restricted to `[0,1]`, in place of the
appendix's `Borel[0,1]` (sets outside `[0,1]` are null; the singleton family is all of `ℝ`'s)
Hyps: n/a -/
def lebesgueProb : Prob (Jσ ℝ) := Prob.ofMeasure lebesgueUnit

theorem lebesgueProb_singleton (x : ℝ) : lebesgueProb.P (singletonM x) = 0 := by
  show (lebesgueUnit {x}).toReal = 0
  rw [lebesgueUnit, Measure.restrict_apply (measurableSet_singleton x)]
  have : volume ({x} ∩ Icc (0 : ℝ) 1) = 0 :=
    measure_mono_null Set.inter_subset_left Real.volume_singleton
  rw [this, ENNReal.toReal_zero]

/-- **T8(c).** Lebesgue measure on `[0,1]` is a `Prob (Jσ ℝ)` but not a `Prob J` for any
designation `J` containing the complemented singleton family: no probability with the same
values exists for such `J`. (A non-membership of the definition, not a refutation of the note.)
Source: [[decision-problems-v2]] Appendix A "The world/probability mismatch" (line 331) | dp-core-2-060
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem lebesgue_not_prob_of_singleton_designation (J : Designation (MSet ℝ))
    (hJ : Set.range (fun x : ℝ => (singletonM x)ᶜ) ∈ J.1) :
    ¬ ∃ Q : Prob J, Q.P = lebesgueProb.P := by
  rintro ⟨Q, hQ⟩
  exact no_diffuse_prob_of_singleton_designation J hJ
    ⟨Q, fun x => by rw [hQ]; exact lebesgueProb_singleton x⟩

end

end Cleanroom.Decision.DpWorldsJb

import LogicalInduction.Properties.LimitCoherence
import Cleanroom.Bli.BliExtrapolation.Chain

/-!
# `bli-extrapolation` · Measure: the conditional-chaining measure is FAF's Gaifman measure of the
chained valuation (target 2b, load-bearing; route α of design decision 4)

`Chain.lean` built a rational valuation `chainVal e p` from a conditional rule and proved the four
finite clauses. Here they are packaged as FAF's `GaifmanCoherent` (`chainVal_gaifman`), and the
**conditional-chaining measure** is *defined* as FAF's `gaifmanMeasure` of that valuation:
`chainMeasure e p hp := gaifmanMeasure _ (chainVal_gaifman e hp)`. FAF's theorems then give
σ-additivity (a `Measure` on `BoolPCWorld`, a probability measure) and the sentence identity
`chainMeasure_sentence` for free; the cylinder identity `chainMeasure_conj` says the σ-additive
object *is* the chained one, and `chainMeasure_unique` (a π-system argument over Mathlib's
`measurableCylinders`) makes "the conditional-chaining measure" a definite description.
[[bli-soto-a-inventory]] 050's remark "the same object FAF obtains differently" is thereby
literally true.

This is the one heavy import of the package (`Properties.LimitCoherence` pulls
`Properties.Relationships` → `Framework.Criterion`); `Gaifman.lean`, `Soto.lean` and
`Conditioning.lean` inherit it.

Sources: [[bli-soto-a-inventory]] 050; PDF 06 p. 1; PDF 07 p. 2.
-/

namespace Cleanroom.Bli.BliExtrapolation

open LogicalInduction LO.Propositional BoolPCWorld MeasureTheory

/-! ## The chained valuation is Gaifman-coherent -/

/-- **The chained valuation is `GaifmanCoherent`** (FAF's finite coherence conditions): values in
`[0,1]`, `⊤ ↦ 1`, invariance under semantic equivalence, additivity on exclusive disjunctions —
from `Chain.lean`'s four rational lemmas, cast to `ℝ`. This is PDF 06's "if `Q_n` is
propositionally coherent and all newly defined `p` are in `[0,1]`, then `P_n` is propositionally
coherent" with coherence rendered as FAF's object.
Source: [[bli-soto-a-inventory]] 050; PDF 06 p. 1 ("Coherence")
Kind: P
Fidelity: exact
Hyps: (a) `p.InUnit` (the source's "all `p ∈ [0,1]`") -/
theorem chainVal_gaifman (e : ℕ ≃ ℕ) {p : CondRule} (hp : p.InUnit) :
    GaifmanCoherent (fun φ => (chainVal e p φ : ℝ)) where
  mem_Icc := fun φ =>
    ⟨by exact_mod_cast (chainVal_mem_Icc e hp φ).1, by exact_mod_cast (chainVal_mem_Icc e hp φ).2⟩
  top_eq_one := by simp [chainVal_top]
  congr := fun h => by simp only [chainVal_congr e p h]
  disjoint_add := fun h => by simp only [chainVal_disjoint_add e p h]; push_cast; rfl

/-! ## The conditional-chaining measure -/

/-- **The conditional-chaining measure** (design decision 4, route α): FAF's `gaifmanMeasure` of
the chained valuation. A probability measure on `BoolPCWorld = ℕ → Bool` (σ-additive, by FAF's
projective-limit construction), *not* the finitely additive content of the pmf family.
Source: [[bli-soto-a-inventory]] 050 ("a probability measure on the Cantor space of prime
valuations determined by its conditional probabilities along the enumeration")
Kind: D
Fidelity: exact -/
noncomputable def chainMeasure (e : ℕ ≃ ℕ) (p : CondRule) (hp : p.InUnit) :
    Measure BoolPCWorld :=
  gaifmanMeasure _ (chainVal_gaifman e hp)

/-- `chainMeasure` is a probability measure (FAF's instance, applied).
Source: [[bli-soto-a-inventory]] 050
Kind: L
Fidelity: exact -/
instance chainMeasure_isProbabilityMeasure (e : ℕ ≃ ℕ) (p : CondRule) (hp : p.InUnit) :
    IsProbabilityMeasure (chainMeasure e p hp) := by
  unfold chainMeasure
  infer_instance

/-- **The sentence identity** (load-bearing, target 2b): the measure of the event "`φ` holds" is
`ofReal (chainVal e p φ)`, in FAF's `ofReal` form (from `gaifmanMeasure_sentence`). Stated over an
enumeration `e` (decision 3); the measure is FAF's `gaifmanMeasure` of the chained valuation
(decision 4, route α).
Source: [[bli-soto-a-inventory]] 050; PDF 06 p. 1 (`P(φ) := Σ_{C ⊨ φ} P(C)`)
Kind: L (FAF's `gaifmanMeasure_sentence` applied; the content of 2b is `chainVal_gaifman` and
`chainMeasure_unique`)
Fidelity: exact
Hyps: (a) `p.InUnit` -/
theorem chainMeasure_sentence (e : ℕ ≃ ℕ) {p : CondRule} (hp : p.InUnit) (φ : Sentence) :
    chainMeasure e p hp {v : BoolPCWorld | v.toPCWorld.Holds φ} =
      ENNReal.ofReal (chainVal e p φ) :=
  gaifmanMeasure_sentence _ (chainVal_gaifman e hp) φ

/-- The level-`k` cylinder in enumerated coordinates: the worlds holding `conj e u`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def cyl (e : ℕ ≃ ℕ) {k : ℕ} (u : FiniteWorld k) : Set BoolPCWorld :=
  {v | v.toPCWorld.Holds (conj e u)}

/-- Membership in a cylinder: agreement with `u` on the first `k` enumerated atoms.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_cyl_iff (e : ℕ ≃ ℕ) {k : ℕ} (u : FiniteWorld k) (v : BoolPCWorld) :
    v ∈ cyl e u ↔ ∀ j : Fin k, v (e j) = u j := by
  unfold cyl
  rw [Set.mem_setOf_eq, conj_holds_iff]
  simp only [BoolPCWorld.toPCWorld]
  constructor
  · intro h j
    have := h j
    cases hv : v (e j) <;> cases hu : u j <;> simp_all
  · intro h j
    rw [h j]

/-- **The cylinder identity** (load-bearing, target 2b): the σ-additive object gives the level-`k`
cylinder `conj e u` exactly the chained mass `chainPMF p k u` — the statement that the measure *is*
the chained one. Stated over an enumeration `e` (decision 3); the measure is FAF's
`gaifmanMeasure` of the chained valuation (decision 4, route α).
Source: [[bli-soto-a-inventory]] 050; PDF 06 p. 1
Kind: L (`chainMeasure_sentence` plus `chainVal_conj`)
Fidelity: exact
Hyps: (a) `p.InUnit` -/
theorem chainMeasure_conj (e : ℕ ≃ ℕ) {p : CondRule} (hp : p.InUnit) {k : ℕ}
    (u : FiniteWorld k) :
    chainMeasure e p hp (cyl e u) = ENNReal.ofReal (chainPMF p k u) := by
  unfold cyl
  rw [chainMeasure_sentence, chainVal_conj]

/-- Sentence events are measurable (FAF's `measurable_pcWorld_holds` pulled back along
`toPCWorld`).
Source: FAF `measurable_pcWorld_holds`, `BoolPCWorld.measurable_toPCWorld`
Kind: L
Fidelity: n/a -/
lemma measurableSet_holds (φ : Sentence) :
    MeasurableSet {v : BoolPCWorld | v.toPCWorld.Holds φ} :=
  BoolPCWorld.measurable_toPCWorld (measurableSet_setOf.mpr (measurable_pcWorld_holds φ))

/-- Cylinders are measurable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma measurableSet_cyl (e : ℕ ≃ ℕ) {k : ℕ} (u : FiniteWorld k) : MeasurableSet (cyl e u) :=
  measurableSet_holds _

/-! ## Almost-everywhere consequences (target 2c) -/

/-- If `∼φ` has chained value zero then `φ` holds `chainMeasure`-a.e.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainMeasure_ae_of_neg_zero (e : ℕ ≃ ℕ) {p : CondRule} (hp : p.InUnit) {φ : Sentence}
    (h : chainVal e p (∼φ) = 0) :
    ∀ᵐ v ∂chainMeasure e p hp, v.toPCWorld.Holds φ := by
  rw [ae_iff]
  have hset : {v : BoolPCWorld | ¬ v.toPCWorld.Holds φ} = {v | v.toPCWorld.Holds (∼φ)} := by
    ext v; simp
  rw [hset, chainMeasure_sentence, h]
  simp

/-- `chainMeasure_ae_of_pmf_zero`: if every level-`n` world refuting `φ` carries zero chained
mass (`n ≥ level e φ`), then `φ` holds a.e.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainMeasure_ae_of_pmf_zero (e : ℕ ≃ ℕ) {p : CondRule} (hp : p.InUnit) {φ : Sentence}
    {n : ℕ} (hn : level e φ ≤ n)
    (h : ∀ u : FiniteWorld n, ¬ (enumWorld e u).toPCWorld.Holds φ → chainPMF p n u = 0) :
    ∀ᵐ v ∂chainMeasure e p hp, v.toPCWorld.Holds φ := by
  apply chainMeasure_ae_of_neg_zero e hp
  apply chainVal_eq_zero_of_le e p (by simpa using hn)
  intro u hu
  exact h u ((PCWorld.holds_neg _ _).mp hu)

/-- The countable form: a set of sentences each of whose negations has value zero holds a.e.
(every set of FAF sentences is countable).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainMeasure_ae_all (e : ℕ ≃ ℕ) {p : CondRule} (hp : p.InUnit) (A : Set Sentence)
    (h : ∀ φ ∈ A, chainVal e p (∼φ) = 0) :
    ∀ᵐ v ∂chainMeasure e p hp, ∀ φ ∈ A, v.toPCWorld.Holds φ := by
  rw [ae_ball_iff (Set.to_countable A)]
  intro φ hφ
  exact chainMeasure_ae_of_neg_zero e hp (h φ hφ)

/-! ## Uniqueness: the cylinder values determine the measure -/

/-- One above the largest enumeration index of a finite atom set.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def levelOf (e : ℕ ≃ ℕ) (I : Finset ℕ) : ℕ := I.sup (fun a => e.symm a + 1)

/-- Atoms of `I` have enumeration index below `levelOf e I`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lt_levelOf (e : ℕ ≃ ℕ) {I : Finset ℕ} {a : ℕ} (ha : a ∈ I) : e.symm a < levelOf e I :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Finset.le_sup (f := fun a => e.symm a + 1) ha)

/-- Read the coordinates `I` off a level-`levelOf e I` world.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def restrictTo (e : ℕ ≃ ℕ) (I : Finset ℕ) (u : FiniteWorld (levelOf e I)) : I → Bool :=
  fun i => u ⟨e.symm i, lt_levelOf e i.2⟩

/-- Distinct level-`k` cylinders are disjoint.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cyl_disjoint (e : ℕ ≃ ℕ) {k : ℕ} {u w : FiniteWorld k} (huw : u ≠ w) :
    Disjoint (cyl e u) (cyl e w) := by
  rw [Set.disjoint_left]
  intro v hu hw
  rw [mem_cyl_iff] at hu hw
  apply huw
  funext j
  rw [← hu j, ← hw j]

open Classical in
/-- Every Mathlib measurable cylinder is a finite disjoint union of enumerated cylinders at level
`levelOf e I`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cylinder_eq_biUnion (e : ℕ ≃ ℕ) (I : Finset ℕ) (S : Set (I → Bool)) :
    cylinder I S =
      ⋃ u ∈ (Finset.univ.filter fun u : FiniteWorld (levelOf e I) => restrictTo e I u ∈ S),
        cyl e u := by
  ext v
  simp only [mem_cylinder, Set.mem_iUnion, exists_prop]
  constructor
  · intro hv
    refine ⟨fun j => v (e j), ?_, ?_⟩
    · have : restrictTo e I (fun j => v (e j)) = I.restrict v := by
        funext i
        simp [restrictTo, Finset.restrict]
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rwa [this]⟩
    · rw [mem_cyl_iff]
      intro j
      rfl
  · rintro ⟨u, huS, hvu⟩
    rw [mem_cyl_iff] at hvu
    have : I.restrict v = restrictTo e I u := by
      funext i
      simp only [Finset.restrict, restrictTo]
      have := hvu ⟨e.symm i, lt_levelOf e i.2⟩
      simpa using this
    rw [this]
    exact (Finset.mem_filter.mp huS).2

open Classical in
/-- **Uniqueness** (load-bearing, target 2b): a probability measure on `BoolPCWorld` giving every
enumerated cylinder `conj e u` the mass `chainPMF p k u` is `chainMeasure e p hp`. Cylinders in
enumerated coordinates refine Mathlib's `measurableCylinders`, a π-system generating the product
σ-algebra. This is what makes "the conditional-chaining measure" a definite description.
Source: [[bli-soto-a-inventory]] 050 ("determined by its conditionals")
Kind: P
Fidelity: exact
Hyps: (a) `p.InUnit`; (a) `IsProbabilityMeasure μ` -/
theorem chainMeasure_unique (e : ℕ ≃ ℕ) {p : CondRule} (hp : p.InUnit) (μ : Measure BoolPCWorld)
    [IsProbabilityMeasure μ]
    (h : ∀ (k : ℕ) (u : FiniteWorld k), μ (cyl e u) = ENNReal.ofReal (chainPMF p k u)) :
    μ = chainMeasure e p hp := by
  refine Measure.ext_of_generateFrom_of_iUnion (measurableCylinders (fun _ : ℕ => Bool))
    (fun _ => Set.univ) generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
    (Set.iUnion_const _) (fun _ => univ_mem_measurableCylinders _) (fun _ => measure_ne_top _ _) ?_
  intro s hs
  obtain ⟨I, S, _, rfl⟩ := (mem_measurableCylinders s).mp hs
  have hdisj : ((Finset.univ.filter fun u : FiniteWorld (levelOf e I) => restrictTo e I u ∈ S) :
      Set (FiniteWorld (levelOf e I))).PairwiseDisjoint (cyl e) :=
    fun u _ w _ huw => cyl_disjoint e huw
  have hmeas : ∀ u ∈ (Finset.univ.filter fun u : FiniteWorld (levelOf e I) =>
      restrictTo e I u ∈ S), MeasurableSet (cyl e u) :=
    fun u _ => measurableSet_cyl e u
  rw [cylinder_eq_biUnion e I S, measure_biUnion_finset hdisj hmeas,
    measure_biUnion_finset hdisj hmeas]
  apply Finset.sum_congr rfl
  intro u _
  rw [h, chainMeasure_conj]

end Cleanroom.Bli.BliExtrapolation

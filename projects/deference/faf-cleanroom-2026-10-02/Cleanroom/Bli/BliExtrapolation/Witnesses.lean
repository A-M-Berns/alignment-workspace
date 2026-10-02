import Cleanroom.Bli.BliExtrapolation.Gaifman

/-!
# `bli-extrapolation` · Witnesses: the fresh-atom enumeration, the two-universal template, the
halving witness (4b, N+) and the enumeration-dependence witness (3e, N+)

Every hand-built witness of the package lives on **fresh atoms** of `bli-found`'s family `8`
(`freshAtom 8 _`; `Tags.lean`'s registry rows `8`–`15` are reserved, and this package claims `8` —
the registry line is `bli-found`'s file and is not edited here; see the report). Universal `u` is
the atom `univAtom u := freshAtomCode 8 (Nat.pair 0 u)`, instance atom `i` is
`instAtom i := freshAtomCode 8 (Nat.pair 1 i)`. `freshEnum : ℕ ≃ ℕ` is an enumeration with the
fresh codes at the even indices (`freshEnum (2k) = freshAtomCode 8 k`) and every other atom at an
odd index (a `Denumerable` interleaving; noncomputable, used only in witnesses). The template
`mkStructure inst0 inst1` is the quantifier structure with universals `univAtom u`, polarity
`true`, instances `inst0` for `u = 0`, `inst1` for `u = 1`, `⊤` for the rest, and no split triples.

* **`halving_witness`** (4b, N+): one universal `U = univAtom 0` whose instances are the fresh atoms
  `instAtom i` at the strictly increasing indices `2 · Nat.pair 1 i`, base `B = 1` with
  `q U = q (¬U) = ½`: `HalvingCondition` holds (through `halving_of_fresh_instances`),
  `BaseAxConsistent` holds, `μ U = ½`, `μ (I_0) = ¾ > μ U` (the identity is not trivial), and
  `μ (⋂ i, I_i) = ½ = μ U`.
* **`extrapolate_depends_on_enumeration`** (3e, N+): one universal with one instance atom `a`; with
  `U` enumerated before `a`, `P(a) = ¾`; with `a` before `U`, `P(a) = ½`.

The refutation witnesses (4d) are in `Refutations.lean`.

Sources: PDF 07 p. 2 / PIBBSS §4.3 (the halving argument, the enumeration remark);
[[bli-soto-a-inventory]] 055 ("off-base guesses depend on the enumeration order").
-/

namespace Cleanroom.Bli.BliExtrapolation

open LogicalInduction LO.Propositional BoolPCWorld MeasureTheory Finset Cleanroom.Bli.BliFound

/-! ## Fresh atoms of family 8 -/

/-- The fresh-atom family of this package's witnesses (`bli-found` registry: `8`, reserved).
Source: none: infrastructure ([[plan]] §0.4 rule 10)
Kind: D
Fidelity: n/a -/
def witnessFamily : ℕ := 8

/-- The atom of universal `u`: `freshAtomCode 8 (Nat.pair 0 u)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def univAtom (u : ℕ) : ℕ := freshAtomCode witnessFamily (Nat.pair 0 u)

/-- The `i`-th instance atom: `freshAtomCode 8 (Nat.pair 1 i)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def instAtom (i : ℕ) : ℕ := freshAtomCode witnessFamily (Nat.pair 1 i)

/-- `univAtom` is injective.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma univAtom_injective : Function.Injective univAtom := by
  intro u u' h
  have := (freshAtomCode_inj.mp h).2
  exact (Nat.pair_eq_pair.mp this).2

/-- `instAtom` is injective.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma instAtom_injective : Function.Injective instAtom := by
  intro i i' h
  have := (freshAtomCode_inj.mp h).2
  exact (Nat.pair_eq_pair.mp this).2

/-- Universal atoms and instance atoms are distinct.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma univAtom_ne_instAtom (u i : ℕ) : univAtom u ≠ instAtom i := by
  intro h
  have := (freshAtomCode_inj.mp h).2
  exact absurd (Nat.pair_eq_pair.mp this).1 (by norm_num)

/-- `univAtom 0 = freshAtomCode 8 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma univAtom_zero : univAtom 0 = freshAtomCode witnessFamily 0 := rfl

/-- `univAtom 1 = freshAtomCode 8 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma univAtom_one : univAtom 1 = freshAtomCode witnessFamily 1 := rfl

/-- `instAtom 0 = freshAtomCode 8 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma instAtom_zero : instAtom 0 = freshAtomCode witnessFamily 2 := rfl

/-! ## The fresh-atom enumeration -/

/-- The fresh codes of family `8` are injective in the payload.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freshCode_injective : Function.Injective (freshAtomCode witnessFamily) :=
  fun _ _ h => (freshAtomCode_inj.mp h).2

/-- Infinitely many atoms are not fresh codes of family `8` (all codes of family `9` are not).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma nonFresh_infinite : Set.Infinite {a : ℕ | a ∉ Set.range (freshAtomCode witnessFamily)} := by
  apply Set.Infinite.mono _ (Set.infinite_range_of_injective
    (f := freshAtomCode (witnessFamily + 1)) (fun _ _ h => (freshAtomCode_inj.mp h).2))
  rintro _ ⟨k, rfl⟩ ⟨k', hk'⟩
  have := (freshAtomCode_inj.mp hk').1
  omega

/-- `Infinite` instance for the non-fresh atoms.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
instance nonFresh_infinite_inst :
    Infinite ↥{a : ℕ | a ∉ Set.range (freshAtomCode witnessFamily)} :=
  nonFresh_infinite.to_subtype

open Classical in
/-- **The fresh-atom enumeration**: fresh codes of family `8` at the even indices, every other
atom at an odd index (`ℕ ≃ ℕ ⊕ ℕ`, then the fresh codes on the left and a `Denumerable`
enumeration of the complement on the right). Noncomputable; used only by the witnesses.
Source: none: infrastructure (mandate: "build `e` from `freshAtom`'s pairing")
Kind: D
Fidelity: n/a -/
noncomputable def freshEnum : ℕ ≃ ℕ :=
  Equiv.natSumNatEquivNat.symm.trans
    (((Equiv.ofInjective (freshAtomCode witnessFamily) freshCode_injective).sumCongr
      (@Denumerable.eqv _ (Nat.Subtype.denumerable
        {a : ℕ | a ∉ Set.range (freshAtomCode witnessFamily)})).symm).trans
      (Equiv.sumCompl (· ∈ Set.range (freshAtomCode witnessFamily))))

/-- `freshEnum (2k) = freshAtomCode 8 k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freshEnum_even (k : ℕ) : freshEnum (2 * k) = freshAtomCode witnessFamily k := by
  have h1 : Equiv.natSumNatEquivNat.symm (2 * k) = Sum.inl k := by
    rw [Equiv.symm_apply_eq, Equiv.natSumNatEquivNat_apply]
    rfl
  simp only [freshEnum, Equiv.trans_apply, h1, Equiv.sumCongr_apply, Sum.map_inl]
  rfl

/-- `freshEnum 0 = univAtom 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freshEnum_zero : freshEnum 0 = univAtom 0 := by
  rw [univAtom_zero]; simpa using freshEnum_even 0

/-- `freshEnum 2 = univAtom 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freshEnum_two : freshEnum 2 = univAtom 1 := by
  rw [univAtom_one]; simpa using freshEnum_even 1

/-- `freshEnum 4 = instAtom 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freshEnum_four : freshEnum 4 = instAtom 0 := by
  rw [instAtom_zero]; simpa using freshEnum_even 2

/-- The `i`-th instance atom sits at index `2 · Nat.pair 1 i`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freshEnum_instAtom (i : ℕ) : freshEnum (2 * Nat.pair 1 i) = instAtom i :=
  freshEnum_even _

/-! ## The two-universal template -/

/-- **The two-universal template**: universals `univAtom u` (polarity `true`), instances `inst0 i`
for `u = 0`, `inst1 i` for `u = 1`, `⊤` (a tautological axiom) for every other universal, and no
split triples.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def mkStructure (inst0 inst1 : ℕ → Sentence) : UnivStructure where
  univ := univAtom
  univ_inj := univAtom_injective
  pol := true
  inst := fun u i => if u = 0 then inst0 i else if u = 1 then inst1 i else ⊤
  split := ∅

/-- The universal sentence of the template is the universal atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma mk_univSentence (inst0 inst1 : ℕ → Sentence) (u : ℕ) :
    (mkStructure inst0 inst1).univSentence u = Formula.atom (univAtom u) := by
  simp [UnivStructure.univSentence, mkStructure]

/-- The instances of the template.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma mk_inst_zero (inst0 inst1 : ℕ → Sentence) (i : ℕ) :
    (mkStructure inst0 inst1).inst 0 i = inst0 i := by simp [mkStructure]

/-- The instances of the template's second universal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma mk_inst_one (inst0 inst1 : ℕ → Sentence) (i : ℕ) :
    (mkStructure inst0 inst1).inst 1 i = inst1 i := by simp [mkStructure]

/-- `AxHolds` for the template: the two schema-1 families.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mk_axHolds_iff (inst0 inst1 : ℕ → Sentence) (v : PCWorld) :
    AxHolds (mkStructure inst0 inst1) v ↔
      (∀ i, v (univAtom 0) → v.Holds (inst0 i)) ∧ (∀ i, v (univAtom 1) → v.Holds (inst1 i)) := by
  rw [axHolds_iff]
  simp only [mk_univSentence, PCWorld.holds_atom]
  have hsplit : (mkStructure inst0 inst1).split = ∅ := rfl
  simp only [hsplit, Set.mem_empty_iff_false, false_imp_iff, implies_true, and_true]
  constructor
  · intro h
    exact ⟨fun i => by simpa [mkStructure] using h 0 i,
      fun i => by simpa [mkStructure] using h 1 i⟩
  · rintro ⟨h0, h1⟩ u i hu
    by_cases hu0 : u = 0
    · subst hu0; simpa [mkStructure] using h0 i hu
    · by_cases hu1 : u = 1
      · subst hu1; simpa [mkStructure] using h1 i hu
      · simp [mkStructure, hu0, hu1, PCWorld.holds_top]

/-- The axioms of the template, listed.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mk_mem_Ax_iff (inst0 inst1 : ℕ → Sentence) (a : Sentence) :
    a ∈ Ax (mkStructure inst0 inst1) ↔
      ∃ u i, a = Formula.atom (univAtom u) 🡒 (mkStructure inst0 inst1).inst u i := by
  simp only [Ax, mkStructure, Set.mem_empty_iff_false, false_and, exists_false,
    Set.mem_union, Set.mem_setOf_eq, or_false]
  simp [UnivStructure.univSentence]

/-! ## Locality for the fresh-atomic template (3c: the first `Local` inhabitants)

`UnivStructure.Local` is a hypothesis structure; `axEntails_decidable` only transfers its finite
check to a `Decidable` instance. The content of claim (ii) is in *inhabiting* `Local`. This
section inhabits it for the template with atomic instances and tautological second family —
the atomic case of [[bli-soto-a-2-inventory]] 008's Lemma B — and hence for `halvingS` and
`enumS`. Everything here is computable (no `Classical`). -/

/-- Atoms of a member of `Γ` lie in `atomsOf Γ φ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_atomsOf_of_mem (Γ : Finset Sentence) (φ : Sentence) {ψ : Sentence} (hψ : ψ ∈ Γ)
    {a : ℕ} (ha : a ∈ sentenceAtomCodes ψ) : a ∈ atomsOf Γ φ :=
  Finset.mem_union_left _ (Finset.le_sup (f := sentenceAtomCodes) hψ ha)

/-- Atoms of `φ` lie in `atomsOf Γ φ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_atomsOf_of_mem_right (Γ : Finset Sentence) (φ : Sentence) {a : ℕ}
    (ha : a ∈ sentenceAtomCodes φ) : a ∈ atomsOf Γ φ :=
  Finset.mem_union_right _ ha

/-- `worldOn J w` reads `w` on `J`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma worldOn_toPCWorld_of_mem (J : Finset ℕ) (w : J → Bool) {a : ℕ} (ha : a ∈ J) :
    (worldOn J w).toPCWorld a ↔ w ⟨a, ha⟩ = true := by
  simp [worldOn, BoolPCWorld.toPCWorld, ha]

/-- **The extension world**: a valuation `w` of the finite atom set `J`, extended by `true` on
the instance atoms `g i` outside `J` and `false` elsewhere. The only axioms of the atomic
template mentioning an atom outside `J` are then satisfied.
Source: [[bli-soto-a-2-inventory]] 008 (Lemma B: conservative extension), atomic case
Kind: D
Fidelity: n/a -/
def extendWorld (J : Finset ℕ) (w : J → Bool) (g : ℕ → ℕ) : PCWorld :=
  fun a => if h : a ∈ J then w ⟨a, h⟩ = true else ∃ i, g i = a

/-- `extendWorld` agrees with `worldOn J w` on `J`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma extendWorld_of_mem (J : Finset ℕ) (w : J → Bool) (g : ℕ → ℕ) {a : ℕ} (ha : a ∈ J) :
    extendWorld J w g a ↔ (worldOn J w).toPCWorld a := by
  rw [worldOn_toPCWorld_of_mem J w ha]
  simp [extendWorld, ha]

/-- Off `J`, `extendWorld` is true exactly on the instance atoms.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma extendWorld_of_notMem (J : Finset ℕ) (w : J → Bool) (g : ℕ → ℕ) {a : ℕ} (ha : a ∉ J) :
    extendWorld J w g a ↔ ∃ i, g i = a := by
  simp [extendWorld, ha]

/-- **The local axioms** of the atomic template on a finite atom set `J`: the schema-1 axioms
`U 🡒 a_i` whose instance atom `g i` lies in `J`, listed through `idx J`, when the universal
atom `U = univAtom 0` lies in `J`; none otherwise (the second family's instances are `⊤`).
Source: [[bli-soto-a-2-inventory]] 008 (Lemma B), atomic case
Kind: D
Fidelity: n/a -/
def mkAtomicAxOn (g : ℕ → ℕ) (idx : Finset ℕ → Finset ℕ) (J : Finset ℕ) : Finset Sentence :=
  if univAtom 0 ∈ J then
    ((idx J).filter fun i => g i ∈ J).image
      fun i => Formula.atom (univAtom 0) 🡒 Formula.atom (g i)
  else ∅

/-- The local axioms are axioms.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mkAtomicAxOn_sub (g : ℕ → ℕ) (idx : Finset ℕ → Finset ℕ) (J : Finset ℕ) :
    ∀ a ∈ mkAtomicAxOn g idx J, a ∈ Ax (mkStructure (fun i => Formula.atom (g i)) (fun _ => ⊤)) := by
  intro a ha
  unfold mkAtomicAxOn at ha
  split_ifs at ha with hU
  · simp only [Finset.mem_image, Finset.mem_filter] at ha
    obtain ⟨i, -, rfl⟩ := ha
    rw [mk_mem_Ax_iff]
    exact ⟨0, i, by simp⟩
  · simp at ha

/-- Every schema-1 axiom with both atoms in `J` is a local axiom (given `idx` lists the
instances with atom in `J`, up to equal atoms).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_mkAtomicAxOn (g : ℕ → ℕ) (idx : Finset ℕ → Finset ℕ)
    (hidx : ∀ J i, g i ∈ J → ∃ i' ∈ idx J, g i' = g i) (J : Finset ℕ) (i : ℕ)
    (hU : univAtom 0 ∈ J) (hi : g i ∈ J) :
    (Formula.atom (univAtom 0) 🡒 Formula.atom (g i)) ∈ mkAtomicAxOn g idx J := by
  unfold mkAtomicAxOn
  rw [if_pos hU, Finset.mem_image]
  obtain ⟨i', hi', hgi'⟩ := hidx J i hi
  exact ⟨i', Finset.mem_filter.mpr ⟨hi', hgi' ▸ hi⟩, by rw [hgi']⟩

/-- **Locality of the atomic template** (3c; the atomic case of [[bli-soto-a-2-inventory]] 008's
Lemma B): for `mkStructure (fun i => atom (g i)) (fun _ => ⊤)` with instance atoms `g i`
distinct from every universal atom, `Ax`-entailment from `Γ` to `φ` is decided by the
valuations of `atomsOf Γ φ` satisfying the local axioms `mkAtomicAxOn g idx (atomsOf Γ φ)`.
Forward direction: a valuation of `J = atomsOf Γ φ` satisfying the local axioms extends to an
`Ax`-world (`extendWorld`: instance atoms off `J` read `true`, so every axiom mentioning them
holds; if `U ∉ J`, `U` reads `false` and every axiom holds), which agrees with it on `Γ`, `φ`.
Backward direction: an `Ax`-world restricted to `J` satisfies the local axioms (their atoms
are in `J`).
Source: PDF 07 p. 2 (decidability claim, with a wrong reason); [[bli-soto-a-2-inventory]] 008
(Lemma B, atomic case)
Kind: P
Fidelity: exact for the atomic template (the first-order instance is target 8, not attempted)
Hyps: (a) `g i ≠ univAtom u`; (a) `idx` lists the instances with atom in `J` -/
theorem mkAtomic_spec (g : ℕ → ℕ) (hg : ∀ u i, g i ≠ univAtom u) (idx : Finset ℕ → Finset ℕ)
    (hidx : ∀ J i, g i ∈ J → ∃ i' ∈ idx J, g i' = g i) (Γ : Finset Sentence) (φ : Sentence) :
    AxEntails (mkStructure (fun i => Formula.atom (g i)) (fun _ => ⊤)) Γ φ ↔
      ∀ w : atomsOf Γ φ → Bool,
        (∀ a ∈ mkAtomicAxOn g idx (atomsOf Γ φ), (worldOn _ w).toPCWorld.Holds a) →
        (worldOn _ w).toPCWorld.ConsistentWith Γ → (worldOn _ w).toPCWorld.Holds φ := by
  classical
  constructor
  · intro hent w hax hΓ
    have hagree : ∀ a ∈ atomsOf Γ φ,
        ((worldOn _ w).toPCWorld a ↔ extendWorld (atomsOf Γ φ) w g a) :=
      fun a ha => (extendWorld_of_mem _ w g ha).symm
    have hv : AxHolds (mkStructure (fun i => Formula.atom (g i)) (fun _ => ⊤))
        (extendWorld (atomsOf Γ φ) w g) := by
      rw [mk_axHolds_iff]
      refine ⟨fun i hU => ?_, fun i _ => PCWorld.holds_top _⟩
      rw [PCWorld.holds_atom]
      by_cases hgi : g i ∈ atomsOf Γ φ
      · by_cases hU0 : univAtom 0 ∈ atomsOf Γ φ
        · have h := hax _ (mem_mkAtomicAxOn g idx hidx _ i hU0 hgi)
          rw [holds_imp, PCWorld.holds_atom, PCWorld.holds_atom] at h
          exact (hagree _ hgi).mp (h ((hagree _ hU0).mpr hU))
        · exfalso
          obtain ⟨i', hi'⟩ := (extendWorld_of_notMem _ w g hU0).mp hU
          exact hg 0 i' hi'
      · exact (extendWorld_of_notMem _ w g hgi).mpr ⟨i, rfl⟩
    have hvΓ : (extendWorld (atomsOf Γ φ) w g).ConsistentWith Γ := fun ψ hψ =>
      (PCWorld.holds_congr_atomCodes ψ
        (fun a ha => hagree a (mem_atomsOf_of_mem Γ φ hψ ha))).mp (hΓ ψ hψ)
    exact (PCWorld.holds_congr_atomCodes φ
      (fun a ha => hagree a (mem_atomsOf_of_mem_right Γ φ ha))).mpr (hent _ hv hvΓ)
  · intro hfin v hv hΓ
    let w : atomsOf Γ φ → Bool := fun a => decide (v a)
    have hagree : ∀ a ∈ atomsOf Γ φ, ((worldOn _ w).toPCWorld a ↔ v a) := by
      intro a ha
      rw [worldOn_toPCWorld_of_mem _ w ha]
      simp [w]
    have hax : ∀ a ∈ mkAtomicAxOn g idx (atomsOf Γ φ), (worldOn _ w).toPCWorld.Holds a := by
      intro a ha
      unfold mkAtomicAxOn at ha
      split_ifs at ha with hU
      · simp only [Finset.mem_image, Finset.mem_filter] at ha
        obtain ⟨i, ⟨-, hgi⟩, rfl⟩ := ha
        rw [holds_imp, PCWorld.holds_atom, PCWorld.holds_atom, hagree _ hU, hagree _ hgi]
        rw [mk_axHolds_iff] at hv
        intro h
        have := hv.1 i h
        rwa [PCWorld.holds_atom] at this
      · simp at ha
    have hΓ' : (worldOn _ w).toPCWorld.ConsistentWith Γ := fun ψ hψ =>
      (PCWorld.holds_congr_atomCodes ψ
        (fun a ha => hagree a (mem_atomsOf_of_mem Γ φ hψ ha))).mpr (hΓ ψ hψ)
    exact (PCWorld.holds_congr_atomCodes φ
      (fun a ha => hagree a (mem_atomsOf_of_mem_right Γ φ ha))).mp (hfin w hax hΓ')

/-- **`Local` for the atomic template**: `reach I := I`, `axOn := mkAtomicAxOn g idx`, exactness
by `mkAtomic_spec`. Computable.
Source: [[bli-soto-a-2-inventory]] 008 (Lemma B, atomic case); mandate 3c
Kind: P
Fidelity: exact for the atomic template
Hyps: (a) `g i ≠ univAtom u`; (a) `idx` lists the instances with atom in `J` -/
def mkAtomicLocal (g : ℕ → ℕ) (hg : ∀ u i, g i ≠ univAtom u) (idx : Finset ℕ → Finset ℕ)
    (hidx : ∀ J i, g i ∈ J → ∃ i' ∈ idx J, g i' = g i) :
    (mkStructure (fun i => Formula.atom (g i)) (fun _ => ⊤)).Local :=
  ⟨id, mkAtomicAxOn g idx, mkAtomicAxOn_sub g idx, mkAtomic_spec g hg idx hidx⟩

/-- `i ≤ instAtom i` (the payload bounds the code, `Nat.right_le_pair` twice).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma le_instAtom (i : ℕ) : i ≤ instAtom i := by
  unfold instAtom freshAtomCode
  exact (Nat.right_le_pair 1 i).trans (Nat.right_le_pair _ _)

/-! ## Base rules

From here on the witnesses use classical decidability of `AxEntails` (they are noncomputable
anyway: `freshEnum` is). -/

open Classical


/-- The constant-`½` rule (the uniform base as a chain).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def halfRule : CondRule := fun _ _ => 1 / 2

/-- `halfRule` takes values in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma halfRule_inUnit : halfRule.InUnit := fun _ _ => by norm_num [halfRule]

/-- Under `halfRule` every atom has value `½`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainVal_half_atom (e : ℕ ≃ ℕ) (a : ℕ) : chainVal e halfRule (Formula.atom a) = 1 / 2 := by
  have h1 : chainVal e halfRule (Formula.atom a) =
      chainVal e halfRule (⊤ ⋏ Formula.atom (e (e.symm a))) := by
    apply chainVal_congr
    intro v
    simp [PCWorld.holds_and, PCWorld.holds_top]
  rw [h1, chainVal_and_atom e _ (by simp) (1 / 2) (fun _ _ => Or.inr rfl), chainVal_top]
  ring

/-- Under `halfRule` every negated atom has value `½`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainVal_half_neg_atom (e : ℕ ≃ ℕ) (a : ℕ) :
    chainVal e halfRule (∼Formula.atom a) = 1 / 2 := by
  have h1 : chainVal e halfRule (∼Formula.atom a) =
      chainVal e halfRule (⊤ ⋏ ∼Formula.atom (e (e.symm a))) := by
    apply chainVal_congr
    intro v
    simp [PCWorld.holds_and, PCWorld.holds_top]
  rw [h1, chainVal_and_neg_atom e _ (by simp) (1 / 2) (fun _ _ => Or.inr rfl), chainVal_top]
  ring

/-- Extending a `snoc` by a coordinate beyond `k` does not change `Extends`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma extends_snoc_of_le {B k : ℕ} (hk : k ≤ B) (w : FiniteWorld B) (b : Bool)
    (u : FiniteWorld k) :
    Extends (hk.trans (Nat.le_succ B)) (Fin.snoc w b) u ↔ Extends hk w u := by
  unfold Extends
  apply forall_congr'
  intro j
  rw [show Fin.castLE (hk.trans (Nat.le_succ B)) j = Fin.castSucc (Fin.castLE hk j) from
    Fin.ext rfl, Fin.snoc_castSucc]

/-- The marginals of a chained pmf are the chained pmf.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma baseMarginal_chainPMF (r : CondRule) :
    ∀ (B k : ℕ), k ≤ B → ∀ u : FiniteWorld k, baseMarginal (chainPMF r B) k u = chainPMF r k u := by
  intro B
  induction B with
  | zero =>
      intro k hk u
      obtain rfl : k = 0 := Nat.le_zero.mp hk
      rw [baseMarginal_zero, chainPMF_sum_one]
      rfl
  | succ B ih =>
      intro k hk u
      rcases Nat.lt_or_ge k (B + 1) with hlt | hge
      · have hkB : k ≤ B := Nat.lt_succ_iff.mp hlt
        rw [← ih k hkB u]
        unfold baseMarginal
        rw [dif_pos hk, dif_pos hkB, sum_finiteWorld_succ]
        apply Finset.sum_congr rfl
        intro w _
        rw [Fintype.sum_bool]
        have h1 := extends_snoc_of_le hkB w true u
        have h2 := extends_snoc_of_le hkB w false u
        simp only [h1, h2]
        split_ifs
        · rw [← chainPMF_marginal r w, Fintype.sum_bool]
        · simp
      · obtain rfl : k = B + 1 := le_antisymm hk hge
        rw [baseMarginal_self]

/-- **Small sentences under a chained base**: if the base is `chainPMF r B`, the extrapolation of a
sentence of level `≤ B` is `chainVal e r`.
Source: none: infrastructure (instance of `extrapolateVal_eq_base`)
Kind: L
Fidelity: n/a -/
lemma extrapolateVal_of_chainBase (S : UnivStructure) [∀ Γ φ, Decidable (AxEntails S Γ φ)]
    (e : ℕ ≃ ℕ) {r : CondRule} (hr : r.InUnit) (B : ℕ) {φ : Sentence} (hφ : level e φ ≤ B) :
    extrapolateVal S e (chainPMF r B) φ = chainVal e r φ := by
  rw [extrapolateVal_eq_base S e (chainPMF_nonneg hr B) (chainPMF_sum_one r B) hφ,
    ← chainValAt_eq_of_le e r hφ]
  rfl

/-! ## The halving witness (4b) -/

/-- **The halving structure**: one universal `U = univAtom 0` with instances the fresh atoms
`instAtom i`; the second universal has the tautological instance `⊤`. (The template has a
universal atom `univAtom u` for every `u`, all with instance `⊤` beyond the first two, so `Ax`
contains infinitely many tautologies `atom (univAtom u) 🡒 ⊤`; `mk_axHolds_iff` reduces
`AxHolds` to the two families.)
Source: mandate 4b (`halving_witness`)
Kind: D
Fidelity: n/a -/
def halvingS : UnivStructure := mkStructure (fun i => Formula.atom (instAtom i)) (fun _ => ⊤)

/-- **`halvingS` is local** (3c, N+): the first inhabitant of `UnivStructure.Local` on a
structure the package actually uses. `idx J := range (sup J + 1)` lists every instance with
atom in `J` since `i ≤ instAtom i`. Computable (built before any classical instance is used).
Source: mandate 3c; [[bli-soto-a-2-inventory]] 008
Kind: N+
Fidelity: n/a -/
def halvingS_local : halvingS.Local :=
  mkAtomicLocal instAtom (fun u i => (univAtom_ne_instAtom u i).symm)
    (fun J => Finset.range (J.sup id + 1))
    (fun _ i hi => ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le
      ((le_instAtom i).trans (Finset.le_sup (f := id) hi))), rfl⟩)

/-- `Ax`-entailment for `halvingS` is decidable by the finite check of `halvingS_local` — a named
(non-instance) decision procedure, Lean-computable (a `def`, not `noncomputable`); this is not a
`Primrec`/`Computable` statement. The witness statements below keep the classical instance.
Source: mandate 3c
Kind: L
Fidelity: n/a -/
def halvingS_decidable (Γ : Finset Sentence) (φ : Sentence) :
    Decidable (AxEntails halvingS Γ φ) :=
  axEntails_decidable halvingS_local Γ φ

/-- The halving base: `B = 1`, `q U = q (¬U) = ½` (the chain of `halfRule` at level `1`).
Source: mandate 4b
Kind: D
Fidelity: n/a -/
def halvingBase : FiniteWorld 1 → ℚ := chainPMF halfRule 1

/-- The halving base is `½` everywhere.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma halvingBase_apply (w : FiniteWorld 1) : halvingBase w = 1 / 2 := by
  unfold halvingBase
  simp only [chainPMF, halfRule]
  split_ifs <;> norm_num

/-- The index of the `n`-th instance atom under `freshEnum`: `2 · Nat.pair 1 n`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def halvingK (n : ℕ) : ℕ := 2 * Nat.pair 1 n

/-- `halvingK` is strictly increasing.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma halvingK_strictMono : StrictMono halvingK := by
  intro a b hab
  have := Nat.pair_lt_pair_right 1 hab
  unfold halvingK
  omega

/-- `halvingK 0 = 4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma halvingK_zero : halvingK 0 = 4 := by decide

/-- `U`'s level is `1 ≤ halvingK 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma halving_lev : level freshEnum (halvingS.univSentence 0) ≤ halvingK 0 := by
  rw [halvingK_zero]
  simp [halvingS, ← freshEnum_zero]

/-- The instance atoms are fresh: if `freshEnum m = instAtom n`, the only axiom mentioning
`freshEnum m` is `U 🡒 inst 0 n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma halving_fresh (n m : ℕ) (hm : freshEnum m = instAtom n) :
    ∀ a ∈ Ax halvingS, freshEnum m ∈ sentenceAtomCodes a →
      a = halvingS.univSentence 0 🡒 halvingS.inst 0 n := by
  intro a ha hmem
  rw [halvingS, mk_mem_Ax_iff] at ha
  obtain ⟨u, i, rfl⟩ := ha
  rw [hm] at hmem
  simp only [sentenceAtomCodes_imp, sentenceAtomCodes_atom, Finset.mem_union,
    Finset.mem_singleton] at hmem
  rcases hmem with h | h
  · exact absurd h.symm (univAtom_ne_instAtom u n)
  · simp only [mkStructure] at h
    by_cases hu0 : u = 0
    · subst hu0
      simp only [if_true, sentenceAtomCodes_atom, Finset.mem_singleton] at h
      have := instAtom_injective h
      subst this
      simp [halvingS, mkStructure, UnivStructure.univSentence]
    · by_cases hu1 : u = 1
      · subst hu1
        simp at h
      · simp [hu0, hu1] at h

/-- The halving structure has fresh instances at the indices `2 · Nat.pair 1 n`, beyond the base
`B = 1` and beyond `U`'s level `1`.
Source: mandate 4b
Kind: P
Fidelity: n/a -/
theorem halving_freshInstances : FreshInstances halvingS freshEnum 1 0 := by
  refine ⟨halvingK, halvingK_strictMono, by rw [halvingK_zero]; norm_num, halving_lev, ?_,
    fun n => halving_fresh n (halvingK n) (freshEnum_instAtom n)⟩
  intro n
  simp [halvingS, halvingK, freshEnum_instAtom]

/-- **`halving_witness`** (4b, N+): the halving condition holds for `halvingS`, `freshEnum`, `B = 1`.
Source: mandate 4b
Kind: N+
Fidelity: n/a -/
theorem halving_witness : HalvingCondition halvingS freshEnum 1 0 :=
  halving_of_fresh_instances _ _ 1 0 halving_freshInstances

/-- The halving base is `Ax`-consistent: for any `w : FiniteWorld 1`, the world reading `U` as `w`
and every other atom as true satisfies both schema families.
Source: mandate 4b
Kind: N+
Fidelity: n/a -/
theorem halving_baseAxConsistent : BaseAxConsistent halvingS freshEnum halvingBase := by
  intro w _
  refine ⟨fun a => if a = univAtom 0 then (w 0 = true) else True, ?_, ?_⟩
  · rw [halvingS, mk_axHolds_iff]
    refine ⟨fun i _ => ?_, fun i _ => PCWorld.holds_top _⟩
    rw [PCWorld.holds_atom]
    simp [(univAtom_ne_instAtom 0 i).symm]
  · intro φ hφ
    rw [Finset.mem_singleton] at hφ
    subst hφ
    rw [conj_holds_iff]
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp [freshEnum_zero]

/-- Under the halving witness, `P(U) = ½`.
Source: mandate 4b
Kind: N+
Fidelity: n/a -/
theorem halving_val_univ :
    extrapolateVal halvingS freshEnum halvingBase (halvingS.univSentence 0) = 1 / 2 := by
  unfold halvingBase
  rw [extrapolateVal_of_chainBase halvingS freshEnum halfRule_inUnit 1
    (by simp [halvingS, ← freshEnum_zero])]
  simp [halvingS, chainVal_half_atom]

/-- Under the halving witness, `P(¬U) = ½`.
Source: mandate 4b
Kind: N+
Fidelity: n/a -/
theorem halving_val_neg_univ :
    extrapolateVal halvingS freshEnum halvingBase (∼halvingS.univSentence 0) = 1 / 2 := by
  unfold halvingBase
  rw [extrapolateVal_of_chainBase halvingS freshEnum halfRule_inUnit 1
    (by simp [halvingS, ← freshEnum_zero])]
  simp [halvingS, chainVal_half_neg_atom]

/-- Under the halving witness, `P(φ(0)) = ¾ = P(U) · 1 + P(¬U) · ½`: the first instance is not
decided by `U` alone.
Source: mandate 4b ("check the identity fails to be trivial: `μ {U} < μ (I_0)`")
Kind: N+
Fidelity: n/a -/
theorem halving_val_inst0 :
    extrapolateVal halvingS freshEnum halvingBase (halvingS.inst 0 0) = 3 / 4 := by
  have hinst : halvingS.inst 0 0 = Formula.atom (freshEnum 4) := by
    simp [halvingS, freshEnum_four]
  have hU : halvingS.univSentence 0 = Formula.atom (freshEnum 0) := by
    simp [halvingS, freshEnum_zero]
  have hlevU : level freshEnum (halvingS.univSentence 0) ≤ 4 := by rw [hU]; simp
  rw [hinst]
  unfold extrapolateVal
  rw [chainVal_split freshEnum _ (halvingS.univSentence 0)]
  have hpos : chainVal freshEnum (sotoRule halvingS freshEnum halvingBase)
      (halvingS.univSentence 0 ⋏ Formula.atom (freshEnum 4)) =
      1 * chainVal freshEnum (sotoRule halvingS freshEnum halvingBase) (halvingS.univSentence 0) := by
    apply chainVal_and_atom freshEnum _ hlevU 1
    intro w hw
    right
    rw [sotoRule_of_le halvingS freshEnum halvingBase (by norm_num) w]
    have hent : AxEntails halvingS {conj freshEnum w} (Formula.atom (freshEnum 4)) := by
      intro v hv hΓ
      have hconj : v.Holds (conj freshEnum w) := hΓ _ (Finset.mem_singleton_self _)
      have hvU : v.Holds (halvingS.univSentence 0) :=
        (holds_congr_of_holds_conj_pc freshEnum hlevU hconj).mpr hw
      rw [halvingS, mk_axHolds_iff] at hv
      rw [hU, PCWorld.holds_atom, freshEnum_zero] at hvU
      have := hv.1 0 hvU
      simpa [freshEnum_four] using this
    simp [axClause, hent]
  have hneg : chainVal freshEnum (sotoRule halvingS freshEnum halvingBase)
      (∼halvingS.univSentence 0 ⋏ Formula.atom (freshEnum 4)) =
      (1 / 2) * chainVal freshEnum (sotoRule halvingS freshEnum halvingBase)
        (∼halvingS.univSentence 0) := by
    apply chainVal_and_atom freshEnum _ (by simpa using hlevU) (1 / 2)
    intro w hw
    by_cases hc : AxConsistent halvingS {conj freshEnum w}
    · right
      rw [sotoRule_of_le halvingS freshEnum halvingBase (by norm_num) w]
      have hnU : ¬ (enumWorld freshEnum w).toPCWorld.Holds (halvingS.univSentence 0) :=
        (PCWorld.holds_neg _ _).mp hw
      obtain ⟨h1, h2⟩ := fresh_undecided halvingS freshEnum 0 4 0 hlevU
        (halving_fresh 0 4 freshEnum_four) w hc hnU
      simp [axClause, h1, h2]
    · left
      exact sotoPMF_zero_of_inconsistent halvingS freshEnum (chainPMF_nonneg halfRule_inUnit 1)
        (chainPMF_sum_one halfRule 1) halving_baseAxConsistent _ w hc
  rw [hpos, hneg]
  have h1 := halving_val_univ
  have h2 := halving_val_neg_univ
  unfold extrapolateVal at h1 h2
  rw [h1, h2]
  norm_num

/-- The halving witness's extrapolation.
Source: mandate 4b
Kind: D
Fidelity: n/a -/
noncomputable def halvingMeasure : Measure BoolPCWorld :=
  extrapolate halvingS freshEnum halvingBase (chainPMF_nonneg halfRule_inUnit 1)

/-- **The halving witness, measure form** (4b, N+): `μ U = ½`, `μ (I_0) = ¾`, `μ (⋂ i, I_i) = ½`;
in particular `μ U < μ (I_0)` (the identity is not trivial) and `μ U = μ (⋂ i, I_i)` (the identity
holds). Positive masses named: `q U = q (¬U) = ½`; base not a point mass; infinitely many
instances, each undecided on `¬U`-worlds.
Source: mandate 4b
Kind: N+
Fidelity: n/a
Hyps: (a) none (all discharged) -/
theorem halving_measures :
    halvingMeasure (univEvent halvingS 0) = ENNReal.ofReal (1 / 2) ∧
    halvingMeasure (instEvent halvingS 0 0) = ENNReal.ofReal (3 / 4) ∧
    halvingMeasure (⋂ i, instEvent halvingS 0 i) = ENNReal.ofReal (1 / 2) ∧
    halvingMeasure (univEvent halvingS 0) < halvingMeasure (instEvent halvingS 0 0) := by
  have hU : halvingMeasure (univEvent halvingS 0) = ENNReal.ofReal (1 / 2) := by
    unfold halvingMeasure univEvent
    rw [extrapolate_sentence, halving_val_univ]
    norm_num
  have hI : halvingMeasure (instEvent halvingS 0 0) = ENNReal.ofReal (3 / 4) := by
    unfold halvingMeasure instEvent
    rw [extrapolate_sentence, halving_val_inst0]
    norm_num
  refine ⟨hU, hI, ?_, ?_⟩
  · unfold halvingMeasure at hU ⊢
    rw [← gaifman_eq_of_halving halvingS freshEnum halvingBase 0 _ (chainPMF_sum_one halfRule 1)
      halving_baseAxConsistent halving_witness]
    exact hU
  · rw [hU, hI]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-! ## The enumeration-dependence witness (3e) -/

/-- **The enumeration structure**: one universal `U = univAtom 0` with the single instance atom
`a = instAtom 0` (every `inst 0 i` is that atom); the second universal has instance `⊤`, as do
the template's infinitely many further universals (tautological axioms, see `halvingS`).
Source: mandate 3e
Kind: D
Fidelity: n/a -/
def enumS : UnivStructure := mkStructure (fun _ => Formula.atom (instAtom 0)) (fun _ => ⊤)

/-- **`enumS` is local** (3c, N+): every instance is the one atom `instAtom 0`, so `idx J := {0}`.
Source: mandate 3c; [[bli-soto-a-2-inventory]] 008
Kind: N+
Fidelity: n/a -/
def enumS_local : enumS.Local :=
  mkAtomicLocal (fun _ => instAtom 0) (fun u _ => (univAtom_ne_instAtom u 0).symm) (fun _ => {0})
    (fun _ _ _ => ⟨0, Finset.mem_singleton_self 0, rfl⟩)

/-- The enumeration putting `a` first: index `0 ↦ instAtom 0`, index `4 ↦ univAtom 0`.
Source: mandate 3e
Kind: D
Fidelity: n/a -/
noncomputable def enumSwap : ℕ ≃ ℕ := (Equiv.swap 0 4).trans freshEnum

/-- `enumSwap 0 = instAtom 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma enumSwap_zero : enumSwap 0 = instAtom 0 := by
  simp [enumSwap, Equiv.swap_apply_left, freshEnum_four]

/-- The empty base (`B = 0`, total mass one).
Source: mandate 3e
Kind: D
Fidelity: n/a -/
def emptyBase : FiniteWorld 0 → ℚ := fun _ => 1

/-- The empty base is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma emptyBase_nonneg : ∀ w, 0 ≤ emptyBase w := fun _ => by norm_num [emptyBase]

/-- The empty base has mass one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma emptyBase_sum : ∑ w, emptyBase w = 1 := by
  rw [sum_finiteWorld_zero]; rfl

/-- With `U` enumerated before `a` (`freshEnum`: `U` at `0`, `a` at `4`), `P(a) = ¾`.
Source: mandate 3e (`P(a) = P(U)·1 + P(¬U)·½ = ¾`)
Kind: N+
Fidelity: n/a -/
theorem enum_val_first :
    extrapolateVal enumS freshEnum emptyBase (Formula.atom (instAtom 0)) = 3 / 4 := by
  have hU : enumS.univSentence 0 = Formula.atom (freshEnum 0) := by
    simp [enumS, freshEnum_zero]
  have hlevU : level freshEnum (enumS.univSentence 0) ≤ 4 := by rw [hU]; simp
  have hval_U : extrapolateVal enumS freshEnum emptyBase (enumS.univSentence 0) = 1 / 2 := by
    rw [hU]
    unfold extrapolateVal
    have h1 : chainVal freshEnum (sotoRule enumS freshEnum emptyBase) (Formula.atom (freshEnum 0)) =
        chainVal freshEnum (sotoRule enumS freshEnum emptyBase) (⊤ ⋏ Formula.atom (freshEnum 0)) := by
      apply chainVal_congr; intro v; simp [PCWorld.holds_and, PCWorld.holds_top]
    rw [h1, chainVal_and_atom freshEnum _ (by simp) (1 / 2), chainVal_top, mul_one]
    intro w _
    right
    rw [sotoRule_of_le enumS freshEnum emptyBase (Nat.zero_le 0) w]
    have hn1 : ¬ AxEntails enumS {conj freshEnum w} (Formula.atom (freshEnum 0)) := by
      intro h
      have := h (fun _ => False) (by rw [enumS, mk_axHolds_iff]; simp) (by
        intro φ hφ; rw [Finset.mem_singleton] at hφ; subst hφ
        rw [conj_holds_iff]; intro j; exact j.elim0)
      exact this
    have hn2 : ¬ AxEntails enumS {conj freshEnum w} (∼Formula.atom (freshEnum 0)) := by
      intro h
      have := h (fun _ => True) (by rw [enumS, mk_axHolds_iff]; simp [PCWorld.holds_top]) (by
        intro φ hφ; rw [Finset.mem_singleton] at hφ; subst hφ
        rw [conj_holds_iff]; intro j; exact j.elim0)
      exact (PCWorld.holds_neg _ _).mp this trivial
    simp [axClause, hn1, hn2]
  have hval_nU : extrapolateVal enumS freshEnum emptyBase (∼enumS.univSentence 0) = 1 / 2 := by
    have := chainVal_split freshEnum (sotoRule enumS freshEnum emptyBase) (enumS.univSentence 0) ⊤
    rw [chainVal_top] at this
    have hc1 : chainVal freshEnum (sotoRule enumS freshEnum emptyBase) (enumS.univSentence 0 ⋏ ⊤) =
        chainVal freshEnum (sotoRule enumS freshEnum emptyBase) (enumS.univSentence 0) := by
      apply chainVal_congr; intro v; simp [PCWorld.holds_and, PCWorld.holds_top]
    have hc2 : chainVal freshEnum (sotoRule enumS freshEnum emptyBase) (∼enumS.univSentence 0 ⋏ ⊤) =
        chainVal freshEnum (sotoRule enumS freshEnum emptyBase) (∼enumS.univSentence 0) := by
      apply chainVal_congr; intro v; simp [PCWorld.holds_and, PCWorld.holds_top]
    rw [hc1, hc2] at this
    unfold extrapolateVal at hval_U ⊢
    linarith
  rw [← freshEnum_four]
  unfold extrapolateVal
  rw [chainVal_split freshEnum _ (enumS.univSentence 0)]
  have hpos : chainVal freshEnum (sotoRule enumS freshEnum emptyBase)
      (enumS.univSentence 0 ⋏ Formula.atom (freshEnum 4)) =
      1 * chainVal freshEnum (sotoRule enumS freshEnum emptyBase) (enumS.univSentence 0) := by
    apply chainVal_and_atom freshEnum _ hlevU 1
    intro w hw
    right
    rw [sotoRule_of_le enumS freshEnum emptyBase (Nat.zero_le 4) w]
    have hent : AxEntails enumS {conj freshEnum w} (Formula.atom (freshEnum 4)) := by
      intro v hv hΓ
      have hconj : v.Holds (conj freshEnum w) := hΓ _ (Finset.mem_singleton_self _)
      have hvU : v.Holds (enumS.univSentence 0) :=
        (holds_congr_of_holds_conj_pc freshEnum hlevU hconj).mpr hw
      rw [enumS, mk_axHolds_iff] at hv
      rw [hU, PCWorld.holds_atom, freshEnum_zero] at hvU
      have := hv.1 0 hvU
      simpa [freshEnum_four] using this
    simp [axClause, hent]
  have hneg : chainVal freshEnum (sotoRule enumS freshEnum emptyBase)
      (∼enumS.univSentence 0 ⋏ Formula.atom (freshEnum 4)) =
      (1 / 2) * chainVal freshEnum (sotoRule enumS freshEnum emptyBase)
        (∼enumS.univSentence 0) := by
    apply chainVal_and_atom freshEnum _ (by simpa using hlevU) (1 / 2)
    intro w hw
    right
    rw [sotoRule_of_le enumS freshEnum emptyBase (Nat.zero_le 4) w]
    have hnU : ¬ (enumWorld freshEnum w).toPCWorld.Holds (enumS.univSentence 0) :=
      (PCWorld.holds_neg _ _).mp hw
    rw [hU, PCWorld.holds_atom] at hnU
    simp only [BoolPCWorld.toPCWorld, freshEnum_zero] at hnU
    -- the flipped worlds: `instAtom 0` set to `b`, every other atom as `enumWorld w`
    have key : ∀ b : Bool, ∃ v : PCWorld, AxHolds enumS v ∧ v.ConsistentWith {conj freshEnum w} ∧
        (v (freshEnum 4) ↔ b = true) := by
      intro b
      refine ⟨fun a => if a = instAtom 0 then (b = true) else (enumWorld freshEnum w a = true),
        ?_, ?_, ?_⟩
      · rw [enumS, mk_axHolds_iff]
        refine ⟨fun i hvU => ?_, fun i _ => PCWorld.holds_top _⟩
        exfalso
        simp only [(univAtom_ne_instAtom 0 0), if_false] at hvU
        exact hnU hvU
      · intro φ hφ
        rw [Finset.mem_singleton] at hφ
        subst hφ
        rw [conj_holds_iff]
        intro j
        have hne : freshEnum j ≠ instAtom 0 := by
          rw [← freshEnum_four]
          intro h
          have := freshEnum.injective h
          have hj := j.2
          omega
        simp [hne]
      · simp [freshEnum_four]
    have hn1 : ¬ AxEntails enumS {conj freshEnum w} (Formula.atom (freshEnum 4)) := by
      intro hent
      obtain ⟨v, hv, hΓ, hvb⟩ := key false
      have := hent v hv hΓ
      rw [PCWorld.holds_atom] at this
      simp only [Bool.false_eq_true, iff_false] at hvb
      exact hvb this
    have hn2 : ¬ AxEntails enumS {conj freshEnum w} (∼Formula.atom (freshEnum 4)) := by
      intro hent
      obtain ⟨v, hv, hΓ, hvb⟩ := key true
      have := hent v hv hΓ
      rw [PCWorld.holds_neg, PCWorld.holds_atom] at this
      exact this (hvb.mpr rfl)
    simp [axClause, hn1, hn2]
  rw [hpos, hneg]
  unfold extrapolateVal at hval_U hval_nU
  rw [hval_U, hval_nU]
  norm_num

/-- With `a` enumerated before `U` (`enumSwap`: `a` at `0`), `P(a) = ½`.
Source: mandate 3e (`P(a) = ½`)
Kind: N+
Fidelity: n/a -/
theorem enum_val_second :
    extrapolateVal enumS enumSwap emptyBase (Formula.atom (instAtom 0)) = 1 / 2 := by
  rw [← enumSwap_zero]
  unfold extrapolateVal
  have h1 : chainVal enumSwap (sotoRule enumS enumSwap emptyBase) (Formula.atom (enumSwap 0)) =
      chainVal enumSwap (sotoRule enumS enumSwap emptyBase) (⊤ ⋏ Formula.atom (enumSwap 0)) := by
    apply chainVal_congr; intro v; simp [PCWorld.holds_and, PCWorld.holds_top]
  rw [h1, chainVal_and_atom enumSwap _ (by simp) (1 / 2), chainVal_top, mul_one]
  intro w _
  right
  rw [sotoRule_of_le enumS enumSwap emptyBase (Nat.zero_le 0) w]
  have hn1 : ¬ AxEntails enumS {conj enumSwap w} (Formula.atom (enumSwap 0)) := by
    intro h
    have := h (fun _ => False) (by rw [enumS, mk_axHolds_iff]; simp) (by
      intro φ hφ; rw [Finset.mem_singleton] at hφ; subst hφ
      rw [conj_holds_iff]; intro j; exact j.elim0)
    exact this
  have hn2 : ¬ AxEntails enumS {conj enumSwap w} (∼Formula.atom (enumSwap 0)) := by
    intro h
    have := h (fun _ => True) (by rw [enumS, mk_axHolds_iff]; simp [PCWorld.holds_top]) (by
      intro φ hφ; rw [Finset.mem_singleton] at hφ; subst hφ
      rw [conj_holds_iff]; intro j; exact j.elim0)
    exact (PCWorld.holds_neg _ _).mp this trivial
  simp [axClause, hn1, hn2]

/-- **3e, `extrapolate_depends_on_enumeration`** (N+): the same structure, base (`B = 0`) and
sentence `a` receive different values under two enumerations — `¾` with `U` before `a`, `½` with
`a` before `U`. PDF 07 p. 3's "off-base guesses depend on enumeration order", witnessed; the reason
`e` is a parameter of every definition here.
Source: PDF 07 p. 3; PIBBSS §4.3 p. 18; [[bli-soto-a-inventory]] 055
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem extrapolate_depends_on_enumeration :
    extrapolateVal enumS freshEnum emptyBase (Formula.atom (instAtom 0)) ≠
      extrapolateVal enumS enumSwap emptyBase (Formula.atom (instAtom 0)) := by
  rw [enum_val_first, enum_val_second]
  norm_num

end Cleanroom.Bli.BliExtrapolation

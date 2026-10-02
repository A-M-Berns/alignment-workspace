import LogicalInduction.Framework.BooleanWorlds
import Cleanroom.Bli.BliFound.Tags

/-!
# `bli-extrapolation` · Syntax: quantifier structures, `Ax`, semantic entailment, enumerated
conjunctions and levels (target 1; design decisions 1–3)

Soto's extrapolation (PDF 07 "Step 2", PIBBSS §4.3) needs only *which atoms are universals, which
sentences are their instances, and how they interact propositionally*. FAF's language is
propositional with `ℕ` atoms and first-order primes are atoms (`paperPrimeSentence`), so the
definition of record is an abstract **quantifier structure** `UnivStructure` (design decision 1):
`univ u` is the atom of the `u`-th universal prime, `pol` its polarity (`false` for FAF's
`∀ = ∼∃¬`), `inst u i` its `i`-th instance (any sentence), `split` the schema-2 triples. `Ax S`
is the set of instances of PDF 07's two schemas. Entailment is **semantic** (design decision 2):
`AxEntails S Γ φ` quantifies over FAF's `PCWorld`s, which is `Ax ∪ Γ ⊢_Prop φ` by propositional
completeness; no proof system is built. The enumeration is a parameter `e : ℕ ≃ ℕ` (design
decision 3): the `k`-th prime is the atom `e k`, level-`k` conjunctions are FAF's `FiniteWorld k`
read in enumerated coordinates (`conj e u`), and `level e φ` is one above the largest enumeration
index of an atom of `φ`.

The first-order instance of `UnivStructure` is target 8 (`PaperInstance.lean`, stretch); nothing
here is about arithmetic. This file imports only `Framework.BooleanWorlds` and `bli-found`'s
`Tags` (for the fresh atoms of the witnesses).

Sources: [[bli-soto-a-inventory]] 050, 055; [[bli-soto-a-2-inventory]] 008; [[bli-soto-b-inventory]]
032, 033; PDF 07 p. 2; PIBBSS §4.3 p. 17.
-/

namespace Cleanroom.Bli.BliExtrapolation

open LogicalInduction LO.Propositional BoolPCWorld

/-! ## Literals -/

/-- The literal on atom `a` with sign `b`: `atom a` when `b = true`, `∼atom a` when `b = false`.
Source: none: infrastructure (PDF 07's `(¬)φ_j`)
Kind: D
Fidelity: exact -/
def lit (a : ℕ) (b : Bool) : Sentence :=
  if b then Formula.atom a else ∼(Formula.atom a)

/-- A world holds `lit a b` iff its value on `a` matches `b`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_lit (v : PCWorld) (a : ℕ) (b : Bool) : v.Holds (lit a b) ↔ (v a ↔ b = true) := by
  cases b <;> simp [lit]

/-- A world holds an implication iff truth of the antecedent gives truth of the consequent
(FAF has `holds_and`/`holds_or`/`holds_neg` but no implication law).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_imp (v : PCWorld) (φ ψ : Sentence) : v.Holds (φ 🡒 ψ) ↔ (v.Holds φ → v.Holds ψ) :=
  Iff.rfl

/-- The atoms of a literal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma sentenceAtomCodes_lit (a : ℕ) (b : Bool) : sentenceAtomCodes (lit a b) = {a} := by
  cases b <;> simp [lit]

/-! ## Quantifier structures and `Ax` -/

/-- **Abstract quantifier structure** (design decision 1). `univ u` is the atom code of the
`u`-th universal prime (injective: two universals never share an atom, else schema 2 collapses),
`pol` the polarity of the universal sentence (`true`: the atom itself, as in the hand-built
witnesses; `false`: its negation, as FAF's `∀φ = ∼paperPrimeSentence true (.exs (∼φ))`),
`inst u i` the `i`-th instance of universal `u` (any sentence; it may mention other universals —
that is what the 2-006 refutation needs, so no freshness field), `split` the schema-2 triples
`(u₁₂, u₁, u₂)` with `∀m₁∀m₂(φ₁ ∧ φ₂) ↔ (∀m₁φ₁ ∧ ∀m₂φ₂)`.
Source: PDF 07 p. 2 (the two schemas); [[bli-soto-a-inventory]] 055; PIBBSS §4.3
Kind: D
Fidelity: variant: quantifier structure abstracted (design decision 1); the first-order instance
is target 8 -/
structure UnivStructure where
  /-- atom code of the `u`-th universal prime -/
  univ : ℕ → ℕ
  /-- distinct universals have distinct atoms -/
  univ_inj : Function.Injective univ
  /-- polarity of the universal sentence -/
  pol : Bool
  /-- the `i`-th instance of universal `u` -/
  inst : ℕ → ℕ → Sentence
  /-- schema-2 triples `(u₁₂, u₁, u₂)` -/
  split : Set (ℕ × ℕ × ℕ)

namespace UnivStructure

variable (S : UnivStructure)

/-- The sentence "universal `u`": `atom (univ u)` or its negation according to `pol`.
Source: design decision 1
Kind: D
Fidelity: exact -/
def univSentence (u : ℕ) : Sentence :=
  if S.pol then Formula.atom (S.univ u) else ∼(Formula.atom (S.univ u))

/-- A world holds `univSentence u` iff its value on `univ u` equals the polarity.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_univSentence (v : PCWorld) (u : ℕ) :
    v.Holds (S.univSentence u) ↔ (v (S.univ u) ↔ S.pol = true) := by
  unfold univSentence
  cases h : S.pol <;> simp

/-- The atoms of a universal sentence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma sentenceAtomCodes_univSentence (u : ℕ) :
    sentenceAtomCodes (S.univSentence u) = {S.univ u} := by
  unfold univSentence
  cases S.pol <;> simp

end UnivStructure

/-- **The schema `Ax`** of PDF 07 / PIBBSS §4.3 over an abstract quantifier structure: schema 1
`univSentence u 🡒 inst u i` for all `u`, `i`, and schema 2 as the two implications
`univSentence u₁₂ 🡒 (univSentence u₁ ⋏ univSentence u₂)` and its converse for each triple in
`split` (FAF has no biconditional constructor).
Source: PDF 07 p. 2; PIBBSS §4.3 p. 17; [[bli-soto-b-inventory]] 032
Kind: D
Fidelity: variant: quantifier structure abstracted (design decision 1) -/
def Ax (S : UnivStructure) : Set Sentence :=
  {a | ∃ u i, a = S.univSentence u 🡒 S.inst u i} ∪
  {a | ∃ t ∈ S.split, a = S.univSentence t.1 🡒 (S.univSentence t.2.1 ⋏ S.univSentence t.2.2)} ∪
  {a | ∃ t ∈ S.split, a = (S.univSentence t.2.1 ⋏ S.univSentence t.2.2) 🡒 S.univSentence t.1}

/-- A world satisfies every axiom of `Ax S`.
Source: design decision 2
Kind: D
Fidelity: exact -/
def AxHolds (S : UnivStructure) (v : PCWorld) : Prop := ∀ a ∈ Ax S, v.Holds a

/-- **Semantic `Ax`-entailment** (design decision 2): every world satisfying `Ax S` and the finite
set `Γ` satisfies `φ`. By propositional completeness this is `Ax ∪ Γ ⊢_Prop φ`; no proof system
is built.
Source: PDF 07 p. 2 (`Ax ∪ {C} ⊢_Prop φ`); [[bli-soto-a-inventory]] 055
Kind: D
Fidelity: exact (semantic form of the source's syntactic entailment) -/
def AxEntails (S : UnivStructure) (Γ : Finset Sentence) (φ : Sentence) : Prop :=
  ∀ v : PCWorld, AxHolds S v → v.ConsistentWith Γ → v.Holds φ

/-- `Γ` is `Ax`-consistent: some world satisfies `Ax S` and `Γ`.
Source: PDF 07 p. 2 ("`Ax`-consistent `C`")
Kind: D
Fidelity: exact -/
def AxConsistent (S : UnivStructure) (Γ : Finset Sentence) : Prop :=
  ∃ v : PCWorld, AxHolds S v ∧ v.ConsistentWith Γ

/-- `Ax S` is countable (every set of FAF sentences is: `Sentence` is `Encodable`). Needed for the
a.e. statements of target 3a.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Ax_countable (S : UnivStructure) : (Ax S).Countable := Set.to_countable _

/-- Unpacked form of `AxHolds`: every instance follows from its universal, and every split
triple's universal is equivalent to the conjunction of its parts.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma axHolds_iff (S : UnivStructure) (v : PCWorld) :
    AxHolds S v ↔
      (∀ u i, v.Holds (S.univSentence u) → v.Holds (S.inst u i)) ∧
      (∀ t ∈ S.split, v.Holds (S.univSentence t.1) ↔
        (v.Holds (S.univSentence t.2.1) ∧ v.Holds (S.univSentence t.2.2))) := by
  constructor
  · intro h
    refine ⟨fun u i => h _ (Or.inl (Or.inl ⟨u, i, rfl⟩)), fun t ht => ⟨?_, ?_⟩⟩
    · exact fun hu => h _ (Or.inl (Or.inr ⟨t, ht, rfl⟩)) hu
    · exact fun hu => h _ (Or.inr ⟨t, ht, rfl⟩) hu
  · rintro ⟨h1, h2⟩ a ha
    rcases ha with (⟨u, i, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩
    · exact h1 u i
    · exact fun hu => (h2 t ht).mp hu
    · exact fun hu => (h2 t ht).mpr hu

/-- The world that gives every atom the truth value `(pol = false)` falsifies every universal
sentence, hence satisfies both schemas.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def noUniversalWorld (S : UnivStructure) : PCWorld := fun _ => S.pol = false

/-- In `noUniversalWorld S` every universal sentence is false.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma noUniversalWorld_not_holds (S : UnivStructure) (u : ℕ) :
    ¬ (noUniversalWorld S).Holds (S.univSentence u) := by
  rw [UnivStructure.holds_univSentence]
  unfold noUniversalWorld
  cases S.pol <;> simp

/-- **`Ax` is satisfiable** (Soto's "propositionally consistent by being a fragment of First Order
Logic", PDF 07 p. 2 / PIBBSS §4.3): in the abstract layer this is a one-liner — the world
falsifying every universal satisfies both schemas. The first-order argument is only needed where
universals are not free literals (target 8).
Source: PDF 07 p. 2; PIBBSS §4.3 p. 17; [[bli-soto-b-inventory]] 032
Kind: L
Fidelity: exact
Hyps: (a) none -/
lemma Ax_satisfiable (S : UnivStructure) : AxConsistent S ∅ := by
  refine ⟨noUniversalWorld S, ?_, fun φ hφ => absurd hφ (Finset.notMem_empty φ)⟩
  rw [axHolds_iff]
  refine ⟨fun u i hu => absurd hu (noUniversalWorld_not_holds S u), fun t _ => ?_⟩
  constructor
  · intro hu; exact absurd hu (noUniversalWorld_not_holds S _)
  · rintro ⟨hu, _⟩; exact absurd hu (noUniversalWorld_not_holds S _)

/-- Monotonicity of entailment in the antecedent set.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma AxEntails.mono {S : UnivStructure} {Γ Δ : Finset Sentence} {φ : Sentence}
    (h : AxEntails S Γ φ) (hΓΔ : ∀ v : PCWorld, v.ConsistentWith Δ → v.ConsistentWith Γ) :
    AxEntails S Δ φ :=
  fun v hv hΔ => h v hv (hΓΔ v hΔ)

/-- A consistent set does not entail both a sentence and its negation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma not_axEntails_both {S : UnivStructure} {Γ : Finset Sentence} {φ : Sentence}
    (hc : AxConsistent S Γ) (h1 : AxEntails S Γ φ) (h2 : AxEntails S Γ (∼φ)) : False := by
  obtain ⟨v, hv, hΓ⟩ := hc
  exact (PCWorld.holds_neg v φ).mp (h2 v hv hΓ) (h1 v hv hΓ)

/-! ## Enumerated coordinates: `conj`, `enumWorld`, `level` -/

/-- The level-`k` conjunction in enumerated coordinates (design decision 3): `⋀_{j<k} lit (e j) (u j)`,
a `FiniteWorld k` read as Soto's `(¬)φ₁ ∧ … ∧ (¬)φ_k` with `φ_j := atom (e j)`.
Source: PDF 06 p. 1; PDF 07 p. 2; [[bli-soto-a-inventory]] 050
Kind: D
Fidelity: exact -/
def conj (e : ℕ ≃ ℕ) {k : ℕ} (u : FiniteWorld k) : Sentence :=
  sentenceConjunction ((List.finRange k).map fun j : Fin k => lit (e j) (u j))

/-- The Boolean world read off a level-`k` finite world in enumerated coordinates: atom `e j` reads
`u j` for `j < k`, every other atom reads `false`.
Source: design decision 3 (FAF's `FiniteWorld.toBoolPCWorld` transported along `e`)
Kind: D
Fidelity: exact -/
def enumWorld (e : ℕ ≃ ℕ) {k : ℕ} (u : FiniteWorld k) : BoolPCWorld :=
  fun a => if h : e.symm a < k then u ⟨e.symm a, h⟩ else false

/-- One above the largest enumeration index of an atom of `φ` (`0` for atom-free sentences).
Source: design decision 3
Kind: D
Fidelity: exact -/
def level (e : ℕ ≃ ℕ) (φ : Sentence) : ℕ :=
  (sentenceAtomCodes φ).sup (fun a => e.symm a + 1)

/-- A world holds `conj e u` iff it agrees with `u` on the first `k` enumerated atoms.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma conj_holds_iff (e : ℕ ≃ ℕ) {k : ℕ} (u : FiniteWorld k) (v : PCWorld) :
    v.Holds (conj e u) ↔ ∀ j : Fin k, (v (e j) ↔ u j = true) := by
  unfold conj
  rw [holds_sentenceConjunction]
  constructor
  · intro h j
    have := h (lit (e j) (u j)) (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    exact (holds_lit v _ _).mp this
  · intro h φ hφ
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hφ
    exact (holds_lit v _ _).mpr (h j)

/-- `level e φ ≤ k` iff every atom of `φ` has enumeration index below `k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma level_le_iff (e : ℕ ≃ ℕ) (φ : Sentence) (k : ℕ) :
    level e φ ≤ k ↔ ∀ a ∈ sentenceAtomCodes φ, e.symm a < k := by
  unfold level
  rw [Finset.sup_le_iff]
  simp only [Nat.add_one_le_iff]

/-- The atoms of `φ` are among the first `level e φ` enumerated atoms.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sentenceAtoms_subset_of_level (e : ℕ ≃ ℕ) (φ : Sentence) :
    ∀ a ∈ sentenceAtomCodes φ, e.symm a < level e φ :=
  (level_le_iff e φ _).mp le_rfl

/-- `level` of an atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma level_atom (e : ℕ ≃ ℕ) (a : ℕ) : level e (Formula.atom a) = e.symm a + 1 := by
  simp [level]

/-- `level` of a negation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma level_neg (e : ℕ ≃ ℕ) (φ : Sentence) : level e (∼φ) = level e φ := by
  simp [level]

/-- `level` of a conjunction is the max.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma level_and (e : ℕ ≃ ℕ) (φ ψ : Sentence) :
    level e (φ ⋏ ψ) = max (level e φ) (level e ψ) := by
  simp [level, Finset.sup_union]

/-- `level` of a disjunction is the max.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma level_or (e : ℕ ≃ ℕ) (φ ψ : Sentence) :
    level e (φ ⋎ ψ) = max (level e φ) (level e ψ) := by
  simp [level, Finset.sup_union]

/-- `level` of an implication is the max.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma level_imp (e : ℕ ≃ ℕ) (φ ψ : Sentence) :
    level e (φ 🡒 ψ) = max (level e φ) (level e ψ) := by
  simp [level, Finset.sup_union]

/-- `level` of `⊤` and `⊥` is `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma level_top (e : ℕ ≃ ℕ) : level e (⊤ : Sentence) = 0 := by simp [level]

/-- `level` of `⊥` is `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma level_bot (e : ℕ ≃ ℕ) : level e (⊥ : Sentence) = 0 := by simp [level]

/-- The atoms of `conj e u` are `e j`, `j < k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_sentenceAtomCodes_conj (e : ℕ ≃ ℕ) {k : ℕ} (u : FiniteWorld k) {a : ℕ}
    (ha : a ∈ sentenceAtomCodes (conj e u)) : ∃ j : Fin k, a = e j := by
  unfold conj at ha
  generalize List.finRange k = l at ha
  induction l with
  | nil => simp [sentenceConjunction] at ha
  | cons j l ih =>
      simp only [List.map_cons, sentenceConjunction, sentenceAtomCodes_and, Finset.mem_union,
        sentenceAtomCodes_lit, Finset.mem_singleton] at ha
      rcases ha with rfl | ha
      · exact ⟨j, rfl⟩
      · exact ih ha

/-- `level e (conj e u) ≤ k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma level_conj_le (e : ℕ ≃ ℕ) {k : ℕ} (u : FiniteWorld k) : level e (conj e u) ≤ k := by
  rw [level_le_iff]
  intro a ha
  obtain ⟨j, rfl⟩ := mem_sentenceAtomCodes_conj e u ha
  simp

/-- **Agreement below a level determines truth**: two Boolean worlds agreeing on every atom of
enumeration index `< k` agree on every sentence of level `≤ k`. The workhorse behind
`chainVal_level_mono`, the cylinder identities and the Gaifman arguments.
Source: FAF `PCWorld.holds_congr_atomCodes`
Kind: L
Fidelity: n/a -/
lemma holds_congr_of_agree_below (e : ℕ ≃ ℕ) {φ : Sentence} {k : ℕ} (h : level e φ ≤ k)
    {v v' : BoolPCWorld} (hvv' : ∀ a, e.symm a < k → v a = v' a) :
    v.toPCWorld.Holds φ ↔ v'.toPCWorld.Holds φ := by
  apply PCWorld.holds_congr_atomCodes
  intro a ha
  have := hvv' a ((level_le_iff e φ k).mp h a ha)
  simp only [BoolPCWorld.toPCWorld, this]

/-- `enumWorld e u` reads `u j` at atom `e j`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma enumWorld_apply_e (e : ℕ ≃ ℕ) {k : ℕ} (u : FiniteWorld k) (j : Fin k) :
    enumWorld e u (e j) = u j := by
  simp [enumWorld]

/-- `enumWorld e u` reads `false` beyond level `k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma enumWorld_of_le (e : ℕ ≃ ℕ) {k : ℕ} (u : FiniteWorld k) {a : ℕ} (ha : k ≤ e.symm a) :
    enumWorld e u a = false := by
  simp [enumWorld, not_lt.mpr ha]

/-- `enumWorld e u` holds `conj e w` iff `u = w`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma enumWorld_holds_conj_iff (e : ℕ ≃ ℕ) {k : ℕ} (u w : FiniteWorld k) :
    (enumWorld e u).toPCWorld.Holds (conj e w) ↔ u = w := by
  rw [conj_holds_iff]
  simp only [BoolPCWorld.toPCWorld, enumWorld_apply_e]
  constructor
  · intro h; funext j
    have := h j
    cases hu : u j <;> cases hw : w j <;> simp_all
  · rintro rfl j; exact Iff.rfl

/-- A world holding `conj e u` agrees with `enumWorld e u` on every sentence of level `≤ k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_congr_of_holds_conj (e : ℕ ≃ ℕ) {k : ℕ} {u : FiniteWorld k} {φ : Sentence}
    (h : level e φ ≤ k) {v : BoolPCWorld} (hv : v.toPCWorld.Holds (conj e u)) :
    v.toPCWorld.Holds φ ↔ (enumWorld e u).toPCWorld.Holds φ := by
  apply holds_congr_of_agree_below e h
  intro a ha
  rw [conj_holds_iff] at hv
  have := hv ⟨e.symm a, ha⟩
  simp only [Equiv.apply_symm_apply, BoolPCWorld.toPCWorld] at this
  rw [enumWorld]
  simp only [ha, dite_true]
  cases hva : v a <;> cases hu : u ⟨e.symm a, ha⟩ <;> simp_all

/-- The `PCWorld` form of `holds_congr_of_holds_conj`: a proposition-valued world holding
`conj e u` agrees with `enumWorld e u` on every sentence of level `≤ k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_congr_of_holds_conj_pc (e : ℕ ≃ ℕ) {k : ℕ} {u : FiniteWorld k} {φ : Sentence}
    (h : level e φ ≤ k) {v : PCWorld} (hv : v.Holds (conj e u)) :
    v.Holds φ ↔ (enumWorld e u).toPCWorld.Holds φ := by
  apply PCWorld.holds_congr_atomCodes
  intro a ha
  have hlt : e.symm a < k := (level_le_iff e φ k).mp h a ha
  rw [conj_holds_iff] at hv
  have := hv ⟨e.symm a, hlt⟩
  simp only [Equiv.apply_symm_apply] at this
  rw [this]
  simp only [BoolPCWorld.toPCWorld, enumWorld, hlt, dite_true]

/-- `enumWorld e (Fin.snoc u b)` agrees with `enumWorld e u` below level `k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma enumWorld_snoc_agree (e : ℕ ≃ ℕ) {k : ℕ} (u : FiniteWorld k) (b : Bool) {a : ℕ}
    (ha : e.symm a < k) : enumWorld e (Fin.snoc u b) a = enumWorld e u a := by
  simp only [enumWorld, ha, dite_true, Nat.lt_succ_of_lt ha]
  exact Fin.snoc_castSucc (α := fun _ => Bool) (p := u) (x := b) (i := ⟨e.symm a, ha⟩)

/-- `enumWorld e (Fin.snoc u b)` reads `b` at atom `e k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma enumWorld_snoc_last (e : ℕ ≃ ℕ) {k : ℕ} (u : FiniteWorld k) (b : Bool) :
    enumWorld e (Fin.snoc u b) (e k) = b := by
  have := enumWorld_apply_e e (Fin.snoc u b) (Fin.last k)
  simpa [Fin.snoc_last] using this

/-- `Fin.snoc u b` holds a sentence of level `≤ k` iff `u` does.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_enumWorld_snoc_iff (e : ℕ ≃ ℕ) {k : ℕ} (u : FiniteWorld k) (b : Bool) {φ : Sentence}
    (h : level e φ ≤ k) :
    (enumWorld e (Fin.snoc u b)).toPCWorld.Holds φ ↔ (enumWorld e u).toPCWorld.Holds φ :=
  holds_congr_of_agree_below e h (fun _ ha => enumWorld_snoc_agree e u b ha)

/-- A world holds `conj e (Fin.snoc u b)` iff it holds `conj e u` and the literal on `e k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_conj_snoc_iff (e : ℕ ≃ ℕ) {k : ℕ} (u : FiniteWorld k) (b : Bool) (v : PCWorld) :
    v.Holds (conj e (Fin.snoc u b)) ↔ v.Holds (conj e u) ∧ v.Holds (lit (e k) b) := by
  rw [conj_holds_iff, conj_holds_iff, holds_lit, Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]

/-! ## Locality: the hypothesis under which entailment is decidable (design decision 2) -/

/-- The atoms of a finite set of sentences together with one more sentence.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def atomsOf (Γ : Finset Sentence) (φ : Sentence) : Finset ℕ :=
  Γ.sup sentenceAtomCodes ∪ sentenceAtomCodes φ

/-- The Boolean world reading a valuation of the finite atom set `J`, `false` elsewhere.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def worldOn (J : Finset ℕ) (w : J → Bool) : BoolPCWorld :=
  fun a => if h : a ∈ J then w ⟨a, h⟩ else false

/-- **Locality** (the shape of [[bli-soto-a-2-inventory]] 008's Lemma B), a *hypothesis structure*,
not a field of `UnivStructure`: a finite "reach" `reach I` of every finite atom set (no
containment `I ⊆ reach I` is required; only `spec` is used) and a finite subset `axOn J ⊆ Ax S`
such that `Ax`-entailment from `Γ` to `φ` is decided by the finitely many valuations of
`reach (atomsOf Γ φ)` satisfying `axOn (reach (atomsOf Γ φ))`. From it, `AxEntails` is decidable
(`axEntails_decidable`, a transfer lemma). The content is in inhabiting `Local`: done for the
fresh-atomic template (`mkAtomicLocal`, `halvingS_local`, `enumS_local` in `Witnesses.lean`);
the first-order instance is target 8 (not attempted).
Source: PDF 07 p. 2 (decidability claim); [[bli-soto-a-2-inventory]] 008 (Lemmas A/B)
Kind: D
Fidelity: weaker: decidability relative to a `Local` instance -/
structure UnivStructure.Local (S : UnivStructure) where
  /-- the finite set of atoms a finite check must look at -/
  reach : Finset ℕ → Finset ℕ
  /-- the finitely many axioms relevant on a finite atom set -/
  axOn : Finset ℕ → Finset Sentence
  /-- `axOn J` consists of axioms -/
  axOn_sub : ∀ J, ∀ a ∈ axOn J, a ∈ Ax S
  /-- the finite check is exact -/
  spec : ∀ (Γ : Finset Sentence) (φ : Sentence),
    AxEntails S Γ φ ↔
      ∀ w : (reach (atomsOf Γ φ)) → Bool,
        (∀ a ∈ axOn (reach (atomsOf Γ φ)), (worldOn _ w).toPCWorld.Holds a) →
        (worldOn _ w).toPCWorld.ConsistentWith Γ → (worldOn _ w).toPCWorld.Holds φ

/-- Truth of a sentence in a Boolean world is decidable (through FAF's `eval`).
Source: FAF `eval_eq_true_iff_holds`
Kind: L
Fidelity: n/a -/
instance decidableHoldsToPCWorld (v : BoolPCWorld) (φ : Sentence) :
    Decidable (v.toPCWorld.Holds φ) :=
  decidable_of_iff (BoolPCWorld.eval v φ = true) (eval_eq_true_iff_holds v φ)

/-- Consistency of a Boolean world with a finite set is decidable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
instance decidableConsistentWithToPCWorld (v : BoolPCWorld) (Γ : Finset Sentence) :
    Decidable (v.toPCWorld.ConsistentWith Γ) :=
  decidable_of_iff (∀ ψ ∈ Γ, v.toPCWorld.Holds ψ) Iff.rfl

/-- **Claim (ii), the transfer step**: under a `Local` instance, `Ax`-entailment is decidable by
the finite check over the valuations of `reach (atomsOf Γ φ)`. This is one step
(`decidable_of_iff` on `L.spec`): a proposition equivalent to a decidable finite check is
decidable. Decidability is *relative to locality*; the content is in inhabiting `Local`, which
`mkAtomicLocal` does for the fresh-atomic template (`halvingS_local`, `enumS_local`) and which
is not done for the first-order instance (target 8). A `Decidable` instance (a terminating
finite check), not a `Primrec`/`Computable` statement about a coded function.
Source: PDF 07 p. 2 ("deciding whether `Ax ∪ {C} ⊢_Prop φ` for finite `C` is decidable", with a
wrong reason); [[bli-soto-a-2-inventory]] 008
Kind: L
Fidelity: weaker: relative to a `Local` instance; the first-order discharge is target 8, not attempted
Hyps: (c) `L : S.Local` — a locality assumption (the shape of 2-008's Lemma B, this run's
survey, not a published theorem); discharged for the atomic template, open for the first-order
instance -/
def axEntails_decidable {S : UnivStructure} (L : S.Local) (Γ : Finset Sentence) (φ : Sentence) :
    Decidable (AxEntails S Γ φ) :=
  decidable_of_iff _ (L.spec Γ φ).symm

end Cleanroom.Bli.BliExtrapolation

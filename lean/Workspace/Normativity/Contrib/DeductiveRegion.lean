/-
# The deductive coherence region on a finite fragment

Fix a stage `D` of a deductive process and a finite fragment `coords` of sentences.
The day-`n` coherence region is

```
K = conv { W|_coords : W ∈ PC(D) }
```

the convex hull of the restrictions to `coords` of the propositionally consistent
worlds satisfying `D`.  This file computes `K` as an explicit finite list of rational
vertices and proves that list sound, complete, cube-valued, and nonempty under exactly
the hypothesis that nonemptiness needs.

The enumeration is a decision procedure, not an assumption.  A world is
`LO.Propositional.Boolean.Valuation ℕ`, an assignment to countably many atoms, and
`ConsistentWith D` reads it through finitely many sentences.  Only the atoms occurring
in `D ∪ coords` can matter, so the search is over the `2^k` assignments to those `k`
atoms.  Brute force, and exact.

Soundness and completeness are stated about **worlds**, not about atom assignments.
That is what makes the extension step come out right: a member of `coords` is a
formula, not an atom, so two sentences of the fragment can constrain the same atom and
a `{0,1}` pattern can be unrealisable for that reason alone.  `region_fragment_shares_atom`
below exhibits it — `[p, ∼p]` admits two of its four patterns.

`deductiveRegion` lifts the vertex list to price vectors.  `payout_mem_deductiveRegion`
is the load-bearing direction: every deductively plausible world's payout lies in the
region, which is what gives an enforcement trader zero liability at every such world.

Names are provisional (`AGENTS.md` standard 6).  Logical Induction's own results are
used as the pinned dependency's theorems, not restated as axioms.
-/

import Workspace.Normativity.Contrib.AssessmentProcess
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination

namespace Workspace.Normativity.Contrib.DeductiveRegion

open LogicalInduction
open Workspace.Normativity.Contrib.AssessmentProcess

/-! ## The finite search space

Every atom that either the stage or the fragment can read.  A world's behaviour outside
this set is invisible to both, which is what makes the enumeration below exhaustive. -/

/-- The atoms occurring in a fragment. -/
def fragmentAtoms : List Sentence → Finset ℕ
  | [] => ∅
  | φ :: rest => Sentence.atoms φ ∪ fragmentAtoms rest

lemma atoms_subset_fragmentAtoms {coords : List Sentence} {φ : Sentence} (hφ : φ ∈ coords) :
    Sentence.atoms φ ⊆ fragmentAtoms coords := by
  induction coords with
  | nil => exact absurd hφ (List.not_mem_nil)
  | cons ψ rest ih =>
      rcases List.mem_cons.mp hφ with rfl | hrest
      · exact fun _ ha => Finset.mem_union_left _ ha
      · exact fun _ ha => Finset.mem_union_right _ (ih hrest ha)

/-- The atoms occurring in the stage `D` or in the fragment `coords`. -/
def regionContext (D : Finset Sentence) (coords : List Sentence) : Finset ℕ :=
  D.biUnion Sentence.atoms ∪ fragmentAtoms coords

lemma atoms_subset_regionContext_of_mem_stage {D : Finset Sentence} {coords : List Sentence}
    {φ : Sentence} (hφ : φ ∈ D) : φ.atoms ⊆ regionContext D coords := fun _ ha =>
  Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨φ, hφ, ha⟩)

lemma atoms_subset_regionContext_of_mem_coords {D : Finset Sentence} {coords : List Sentence}
    {φ : Sentence} (hφ : φ ∈ coords) : φ.atoms ⊆ regionContext D coords := fun _ ha =>
  Finset.mem_union_right _ (atoms_subset_fragmentAtoms hφ ha)

/-- The context atoms in increasing order.

Built by filtering a range rather than by `Finset.sort`.  The two agree as sets, but
`Finset.sort` is `List.mergeSort`, whose well-founded recursion does not reduce in the
kernel; the `decide +kernel` instances at the end of this file depend on every step of
the search reducing. -/
def contextList (D : Finset Sentence) (coords : List Sentence) : List ℕ :=
  (List.range ((regionContext D coords).sup id + 1)).filter
    fun a => decide (a ∈ regionContext D coords)

lemma mem_contextList (D : Finset Sentence) (coords : List Sentence) {a : ℕ} :
    a ∈ contextList D coords ↔ a ∈ regionContext D coords := by
  simp only [contextList, List.mem_filter, List.mem_range, decide_eq_true_eq]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  exact Nat.lt_succ_of_le (Finset.le_sup (f := id) h)

/-- A bit vector read as an atom table against a list of atoms, `false` off the list. -/
def tableOf (atoms : List ℕ) (xs : List Bool) : ℕ → Bool :=
  fun a => xs.getD (atoms.idxOf a) false

lemma tableOf_map (atoms : List ℕ) (f : ℕ → Bool) {a : ℕ} (ha : a ∈ atoms) :
    tableOf atoms (atoms.map f) a = f a := by
  have hlt : atoms.idxOf a < atoms.length := List.idxOf_lt_length_of_mem ha
  have hlt' : atoms.idxOf a < (atoms.map f).length := by simpa using hlt
  rw [tableOf, List.getD_eq_getElem _ _ hlt', List.getElem_map, List.getElem_idxOf hlt]

/-! ## The vertex list

One entry per assignment to the context atoms that satisfies the whole stage, read off
on the fragment.  `dedup` keeps the list a set of vertices rather than a multiset; every
statement below is about membership, so the deduplication is free. -/

/-- The `{0,1}` patterns on `coords` realised by a propositionally consistent world
satisfying `D`, as an explicit finite list of rational vectors. -/
def admissiblePatterns (D : Finset Sentence) (coords : List Sentence) : List (List ℚ) :=
  let atoms := contextList D coords
  (((allBoolLists atoms.length).filter fun xs =>
      tableConsistent (tableOf atoms xs) D).map fun xs =>
        coords.map (boolPayoutRat (tableOf atoms xs))).dedup

/-- **Soundness.**  Every listed pattern is the payout table of an actual
propositionally consistent world satisfying `D`, read on `coords`. -/
theorem admissiblePatterns_sound (D : Finset Sentence) (coords : List Sentence)
    {w : List ℚ} (hw : w ∈ admissiblePatterns D coords) :
    ∃ v : PCWorld, v.ConsistentWith D ∧ w = coords.map (ratPayout v) := by
  rw [admissiblePatterns, List.mem_dedup, List.mem_map] at hw
  obtain ⟨xs, hxs, rfl⟩ := hw
  rw [List.mem_filter] at hxs
  refine ⟨boolPCWorld (tableOf (contextList D coords) xs), ?_, ?_⟩
  · exact (tableConsistent_eq_true_iff _ D).mp hxs.2
  · exact List.map_congr_left fun φ _ => boolPayoutRat_eq_ratPayout _ φ

open Classical in
/-- The world's own atom table agrees with the enumerated one on every sentence the
context covers.  This is where "only the context atoms matter" is discharged.

`open Classical` is scoped to this lemma and to completeness below rather than taken for
the file: a world is `ℕ → Prop`, so reading it as bits is classical, while the enumerator
itself must keep computable instances to reduce in the kernel. -/
lemma sentenceBool_tableOf_iff (D : Finset Sentence) (coords : List Sentence) (v : PCWorld)
    {φ : Sentence} (hsub : φ.atoms ⊆ regionContext D coords) :
    sentenceBool (tableOf (contextList D coords)
      ((contextList D coords).map fun a => decide (v a))) φ = true ↔ v.Holds φ := by
  rw [sentenceBool_congr_of_atoms (v := fun a => decide (v a)) fun a ha =>
    tableOf_map _ _ ((mem_contextList D coords).mpr (hsub ha))]
  exact sentenceBool_decide_world v φ

open Classical in
/-- **Completeness.**  Every propositionally consistent world satisfying `D` has its
restriction to `coords` in the list. -/
theorem admissiblePatterns_complete (D : Finset Sentence) (coords : List Sentence)
    (v : PCWorld) (hv : v.ConsistentWith D) :
    coords.map (ratPayout v) ∈ admissiblePatterns D coords := by
  have hmemxs : (contextList D coords).map (fun a => decide (v a))
      ∈ allBoolLists (contextList D coords).length :=
    mem_allBoolLists_iff.mpr (by simp)
  have hcons : tableConsistent
      (tableOf (contextList D coords)
        ((contextList D coords).map fun a => decide (v a))) D = true :=
    (tableConsistent_eq_true_iff _ D).mpr fun φ hφ =>
      (sentenceBool_eq_true_iff _ φ).mp
        ((sentenceBool_tableOf_iff D coords v
          (atoms_subset_regionContext_of_mem_stage hφ)).mpr (hv φ hφ))
  have hmap : coords.map (boolPayoutRat (tableOf (contextList D coords)
      ((contextList D coords).map fun a => decide (v a))))
      = coords.map (ratPayout v) := by
    refine List.map_congr_left fun φ hφ => ?_
    have hiff := sentenceBool_tableOf_iff D coords v
      (atoms_subset_regionContext_of_mem_coords (coords := coords) hφ)
    unfold boolPayoutRat ratPayout
    by_cases hh : v.Holds φ
    · simp [hiff.mpr hh, hh]
    · have hne : sentenceBool (tableOf (contextList D coords)
          ((contextList D coords).map fun a => decide (v a))) φ ≠ true := fun h => hh (hiff.mp h)
      simp [hne, hh]
  rw [admissiblePatterns, List.mem_dedup, List.mem_map]
  exact ⟨_, List.mem_filter.mpr ⟨hmemxs, hcons⟩, hmap⟩

/-- Every listed pattern has one entry per fragment coordinate. -/
theorem admissiblePatterns_length (D : Finset Sentence) (coords : List Sentence)
    {w : List ℚ} (hw : w ∈ admissiblePatterns D coords) : w.length = coords.length := by
  obtain ⟨v, _, rfl⟩ := admissiblePatterns_sound D coords hw
  simp

lemma ratPayout_eq_zero_or_one (v : PCWorld) (φ : Sentence) :
    ratPayout v φ = 0 ∨ ratPayout v φ = 1 := by
  unfold ratPayout
  by_cases hh : v.Holds φ
  · exact Or.inr (if_pos hh)
  · exact Or.inl (if_neg hh)

/-- **Cube-valued.**  Every entry of every listed pattern is `0` or `1`. -/
theorem admissiblePatterns_mem_cube (D : Finset Sentence) (coords : List Sentence)
    {w : List ℚ} (hw : w ∈ admissiblePatterns D coords) {x : ℚ} (hx : x ∈ w) :
    x = 0 ∨ x = 1 := by
  obtain ⟨v, _, rfl⟩ := admissiblePatterns_sound D coords hw
  rw [List.mem_map] at hx
  obtain ⟨φ, _, rfl⟩ := hx
  exact ratPayout_eq_zero_or_one v φ

/-- **Exactly what nonemptiness needs.**  The vertex list is nonempty precisely when the
stage is propositionally satisfiable.  Nothing about the fragment enters. -/
theorem admissiblePatterns_ne_nil_iff (D : Finset Sentence) (coords : List Sentence) :
    admissiblePatterns D coords ≠ [] ↔ ∃ v : PCWorld, v.ConsistentWith D := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ h
    obtain ⟨v, hv, _⟩ := admissiblePatterns_sound D coords hw
    exact ⟨v, hv⟩
  · rintro ⟨v, hv⟩ hnil
    have := admissiblePatterns_complete D coords v hv
    rw [hnil] at this
    exact absurd this (by simp)

/-- **Nonemptiness**, under the exact consistency hypothesis on `D`: some propositionally
consistent world satisfies `D`. -/
theorem admissiblePatterns_nonempty (D : Finset Sentence) (coords : List Sentence)
    (hD : ∃ v : PCWorld, v.ConsistentWith D) : admissiblePatterns D coords ≠ [] :=
  (admissiblePatterns_ne_nil_iff D coords).mpr hD

/-! ## The region on price vectors

The fragment is a list, so the ambient coordinate space is `Fin coords.length → ℝ`.  A
price vector is a whole `Sentence → ℝ`; it enters the region through its restriction,
which is what makes membership fragment-local. -/

/-- A price vector read on the fragment. -/
def restrictTo (coords : List Sentence) (p : Sentence → ℝ) : Fin coords.length → ℝ :=
  fun i => p coords[i]

/-- A rational pattern read as a real coordinate vector. -/
def vertex (coords : List Sentence) (w : List ℚ) : Fin coords.length → ℝ :=
  fun i => ((w.getD i.val 0 : ℚ) : ℝ)

lemma vertex_map (coords : List Sentence) (f : Sentence → ℚ) (i : Fin coords.length) :
    vertex coords (coords.map f) i = ((f coords[i] : ℚ) : ℝ) := by
  simp [vertex, List.getD_eq_getElem?_getD]

lemma restrictTo_payout (coords : List Sentence) (v : PCWorld) :
    restrictTo coords v.payout = vertex coords (coords.map (ratPayout v)) := by
  funext i
  rw [vertex_map, restrictTo, payout_eq_ratPayout]

/-- The listed vertices as a set of coordinate vectors. -/
def deductiveVertices (D : Finset Sentence) (coords : List Sentence) :
    Set (Fin coords.length → ℝ) :=
  {x | ∃ w ∈ admissiblePatterns D coords, x = vertex coords w}

/-- **The deductive coherence region.**  A price vector lies in it when its restriction to
the fragment is a convex combination of the admissible patterns. -/
def deductiveRegion (D : Finset Sentence) (coords : List Sentence) :
    (Sentence → ℝ) → Prop :=
  fun p => restrictTo coords p ∈ convexHull ℝ (deductiveVertices D coords)

/-- **The load-bearing direction.**  Every deductively plausible world's payout vector is
in the region.  Downstream this is what gives an enforcement trader zero liability at
every such world. -/
theorem payout_mem_deductiveRegion (D : Finset Sentence) (coords : List Sentence)
    (v : PCWorld) (hv : v.ConsistentWith D) : deductiveRegion D coords v.payout := by
  refine subset_convexHull ℝ _ ?_
  exact ⟨coords.map (ratPayout v), admissiblePatterns_complete D coords v hv,
    restrictTo_payout coords v⟩

/-- **Fragment-locality.**  Membership reads the price vector only at the fragment's
coordinates. -/
theorem deductiveRegion_fragmentLocal (D : Finset Sentence) (coords : List Sentence)
    {p q : Sentence → ℝ} (h : ∀ φ ∈ coords, p φ = q φ) :
    deductiveRegion D coords p ↔ deductiveRegion D coords q := by
  have : restrictTo coords p = restrictTo coords q := by
    funext i
    exact h coords[i] (List.getElem_mem i.isLt)
  rw [deductiveRegion, deductiveRegion, this]

/-- **The region sits in the unit cube.** -/
theorem deductiveRegion_subset_cube (D : Finset Sentence) (coords : List Sentence)
    {p : Sentence → ℝ} (hp : deductiveRegion D coords p) (i : Fin coords.length) :
    restrictTo coords p i ∈ Set.Icc (0 : ℝ) 1 := by
  have hcube : Convex ℝ (Set.pi Set.univ fun _ : Fin coords.length => Set.Icc (0 : ℝ) 1) :=
    convex_pi fun _ _ => convex_Icc _ _
  have hsub : deductiveVertices D coords ⊆
      Set.pi Set.univ fun _ : Fin coords.length => Set.Icc (0 : ℝ) 1 := by
    rintro x ⟨w, hw, rfl⟩ j _
    obtain ⟨v, _, rfl⟩ := admissiblePatterns_sound D coords hw
    rw [vertex_map]
    rcases ratPayout_eq_zero_or_one v coords[j] with h | h <;> rw [h] <;> norm_num
  exact convexHull_min hsub hcube hp i (Set.mem_univ i)

/-! ## The region is the convex hull of the listed patterns

Membership was defined through `restrictTo`, so the statement with content is that the
region's *image* on the fragment is exactly the hull: every hull point is realised by
some price vector, which needs the fragment to be duplicate-free — a repeated coordinate
would force the two copies to agree. -/

/-- Extend a coordinate vector to a price vector by zero off the fragment. -/
noncomputable def extend (coords : List Sentence) (x : Fin coords.length → ℝ) :
    Sentence → ℝ :=
  fun φ => if h : ∃ i : Fin coords.length, coords[i] = φ then x h.choose else 0

lemma restrictTo_extend (coords : List Sentence) (hnd : coords.Nodup)
    (x : Fin coords.length → ℝ) : restrictTo coords (extend coords x) = x := by
  funext i
  have hex : ∃ j : Fin coords.length, coords[j] = coords[i] := ⟨i, rfl⟩
  have hchoose : coords[hex.choose] = coords[i] := hex.choose_spec
  have : hex.choose = i := Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp hchoose)
  simp [restrictTo, extend, this]

/-- **The region is the convex hull of the listed patterns.**  Read on the fragment, the
set of price vectors in the region is exactly `conv` of the admissible patterns. -/
theorem deductiveRegion_eq_convexHull (D : Finset Sentence) (coords : List Sentence)
    (hnd : coords.Nodup) :
    restrictTo coords '' {p | deductiveRegion D coords p}
      = convexHull ℝ (deductiveVertices D coords) := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hx
    refine ⟨extend coords x, ?_, restrictTo_extend coords hnd x⟩
    have h : restrictTo coords (extend coords x)
        ∈ convexHull ℝ (deductiveVertices D coords) := by
      rw [restrictTo_extend coords hnd x]; exact hx
    exact h

/-! ## Kernel-checked instances

The enumerator is a computable `def`, so the vertex list of a concrete fragment is a
closed term and its value is a kernel-checkable equation.  `decide +kernel` runs the
whole search — atom context, `2^k` assignments, stage filter, fragment read-off — inside
the kernel.  No `native_decide`, no floats.

The stages below are singletons because a `Finset Sentence` literal with two or more
elements goes through `insert`, hence through `DecidableEq Sentence`, which Foundation
builds with `simp`-generated proof terms that do not reduce in the kernel.  An
unsatisfiable single sentence `p ⋏ ∼p` exhibits the empty region just as well. -/

/-- One atom of the fragment. -/
def atomP : Sentence := .atom 0

/-- A second atom, unconstrained by the stages below. -/
def atomQ : Sentence := .atom 1

/-- **A worked finite instance.**  The stage asserts `p`; the fragment is `[p, q]`.  The
region has two vertices: `p` is pinned to `1`, `q` is free. -/
theorem region_worked_instance :
    admissiblePatterns {atomP} [atomP, atomQ] = [[1, 0], [1, 1]] := by
  decide +kernel

/-- **An inconsistent stage gives an empty region.**  No propositionally consistent world
satisfies `p ⋏ ∼p`, so the vertex list is empty. -/
theorem region_inconsistent_stage :
    admissiblePatterns {atomP ⋏ ∼atomP} [atomP, atomQ] = [] := by
  decide +kernel

/-- **A fragment whose sentences constrain the same atom.**  `[p, ∼p]` has four `{0,1}`
patterns and only two are realised by a world.  This is why soundness and completeness
are stated about worlds rather than about atom assignments: a pattern can be
unrealisable because the fragment's own sentences disagree, with no help from the
stage. -/
theorem region_fragment_shares_atom :
    admissiblePatterns (∅ : Finset Sentence) [atomP, ∼atomP] = [[0, 1], [1, 0]] := by
  decide +kernel

/-- The same effect through an entailment rather than a negation: `[p, p ⋏ q, q]` admits
four of its eight patterns. -/
theorem region_fragment_entailment :
    admissiblePatterns (∅ : Finset Sentence) [atomP, atomP ⋏ atomQ, atomQ]
      = [[0, 0, 0], [0, 0, 1], [1, 0, 0], [1, 1, 1]] := by
  decide +kernel

/-- With an unconstrained stage and an independent fragment all `2^{|Φ|}` patterns are
admissible, so the trimming above is the fragment's doing rather than an artefact of the
enumeration. -/
theorem region_independent_fragment :
    admissiblePatterns (∅ : Finset Sentence) [atomP, atomQ]
      = [[0, 0], [0, 1], [1, 0], [1, 1]] := by
  decide +kernel

/-! ## Inhabitation of the hypothesis packages

`AGENTS.md`'s Lean regime asks each theorem of record for a term inhabiting its full
hypothesis package.  The packages here are a stage with a world satisfying it, and a
duplicate-free fragment. -/

/-- The world affirming every atom. -/
def witnessWorld : PCWorld := boolPCWorld fun _ => true

lemma witnessWorld_consistent : witnessWorld.ConsistentWith {atomP} := by
  intro φ hφ
  rw [Finset.mem_singleton] at hφ
  subst hφ
  exact rfl

/-- The stage `{p}` is propositionally satisfiable — the exact hypothesis
`admissiblePatterns_nonempty` needs, discharged rather than assumed. -/
theorem witness_stage_satisfiable : ∃ v : PCWorld, v.ConsistentWith {atomP} :=
  ⟨witnessWorld, witnessWorld_consistent⟩

theorem witness_nonempty : admissiblePatterns {atomP} [atomP, atomQ] ≠ [] :=
  admissiblePatterns_nonempty _ _ witness_stage_satisfiable

/-- The load-bearing conclusion at an instance: a deductively plausible world's payout
vector lies in the region. -/
theorem witness_payout_mem_region :
    deductiveRegion {atomP} [atomP, atomQ] witnessWorld.payout :=
  payout_mem_deductiveRegion _ _ witnessWorld witnessWorld_consistent

/-- The fragment is duplicate-free, inhabiting `deductiveRegion_eq_convexHull`'s
hypothesis. -/
theorem witness_coords_nodup : ([atomP, atomQ] : List Sentence).Nodup := by
  simp [atomP, atomQ]

end Workspace.Normativity.Contrib.DeductiveRegion

#print axioms Workspace.Normativity.Contrib.DeductiveRegion.admissiblePatterns
#print axioms Workspace.Normativity.Contrib.DeductiveRegion.admissiblePatterns_sound
#print axioms Workspace.Normativity.Contrib.DeductiveRegion.admissiblePatterns_complete
#print axioms Workspace.Normativity.Contrib.DeductiveRegion.admissiblePatterns_length
#print axioms Workspace.Normativity.Contrib.DeductiveRegion.admissiblePatterns_mem_cube
#print axioms Workspace.Normativity.Contrib.DeductiveRegion.admissiblePatterns_ne_nil_iff
#print axioms Workspace.Normativity.Contrib.DeductiveRegion.admissiblePatterns_nonempty
#print axioms Workspace.Normativity.Contrib.DeductiveRegion.deductiveRegion
#print axioms Workspace.Normativity.Contrib.DeductiveRegion.payout_mem_deductiveRegion
#print axioms Workspace.Normativity.Contrib.DeductiveRegion.deductiveRegion_fragmentLocal
#print axioms Workspace.Normativity.Contrib.DeductiveRegion.deductiveRegion_subset_cube
#print axioms Workspace.Normativity.Contrib.DeductiveRegion.deductiveRegion_eq_convexHull
#print axioms Workspace.Normativity.Contrib.DeductiveRegion.region_worked_instance
#print axioms Workspace.Normativity.Contrib.DeductiveRegion.region_inconsistent_stage
#print axioms Workspace.Normativity.Contrib.DeductiveRegion.region_fragment_shares_atom
#print axioms Workspace.Normativity.Contrib.DeductiveRegion.region_fragment_entailment
#print axioms Workspace.Normativity.Contrib.DeductiveRegion.region_independent_fragment
#print axioms Workspace.Normativity.Contrib.DeductiveRegion.witness_stage_satisfiable
#print axioms Workspace.Normativity.Contrib.DeductiveRegion.witness_nonempty
#print axioms Workspace.Normativity.Contrib.DeductiveRegion.witness_payout_mem_region
#print axioms Workspace.Normativity.Contrib.DeductiveRegion.witness_coords_nodup

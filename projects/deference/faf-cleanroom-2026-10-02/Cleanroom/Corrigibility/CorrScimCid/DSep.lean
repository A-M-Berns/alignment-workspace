import Cleanroom.Corrigibility.CorrScimCid.Fig1
import FactoredSpaces.DSeparation
import FactoredSpaces.ActiveTrails
import FactoredSpaces.ConditionalHistory

/-!
# Fully updated deference as a d-separation fact (T8 a)

Over FAF's `Digraph.DSeparated` (no active trail), on Carey–Everitt's Fig. 1 graph:

* **with the information link `L → O`** (the agent has learned the human's latent values by another
  channel), the request `H` is d-separated from the utility `U` given `{L, O}` = `(Pa_O ∪ {O}) ∖ {H}`
  — Everitt 2021 Def. 7: `H → O` is a *nonrequisite* information link (`dsep_with_link`);
* **without the link**, `H` is not d-separated from `U` given `{O}`: the fork `H ← L → U` is open
  (`not_dsep_without_link`); and even with the link, conditioning on `O` alone does not separate
  (`not_dsep_with_link_given_O`) — it is the observation of `L` that makes the button irrelevant.

Method: FAF's characterisation `dSeparated_iff_disjoint_zClosureSet` reduces d-separation to the
disjointness of two `Z`-closures; a `Z`-closure is bounded by any `Z`-closed superset of the
unblocked ancestors, and both "`Z`-closed" and "superset of the unblocked ancestors" follow from
finite, `decide`-able closure conditions on explicit bounding sets (`dSeparated_of_bounds`).

Source: critique/carey-everitt.md Claim 2.3a (l. 113); corr-wf13-2-056; everitt-2021 Def. 7, Def. 11,
Thm 12.
-/

namespace Cleanroom.Corrigibility.CorrScimCid

open FactoredSpaces

/-! ### Generic: bounding `Z`-closures by finite closure checks -/

section Generic

variable {V : Type} [DecidableEq V] {G : Digraph V}

/-- The unblocked ancestors of `v` lie in any set containing `v` and closed under unblocked
predecessors.
Source: none: infrastructure
Kind: L -/
lemma unblockedAnc_subset_of_closed {Z T : Finset V}
    (hT : ∀ a b, G.Adj a b → a ∉ Z → b ∈ T → a ∈ T) {v : V} (hv : v ∈ T) :
    G.unblockedAnc Z v ⊆ (T : Set V) := by
  intro u hu
  rw [Digraph.mem_unblockedAnc_iff] at hu
  induction hu using Relation.ReflTransGen.head_induction_on with
  | refl => exact Finset.mem_coe.mpr hv
  | head hab _ ih => exact Finset.mem_coe.mpr (hT _ _ hab.1 hab.2 (Finset.mem_coe.mp ih))

/-- `T` is `Z`-closed as soon as, for each `w ∈ Z`, some predecessor-closed set `A w ∋ w` is either
inside `T` or disjoint from it.
Source: none: infrastructure
Kind: L -/
lemma isZClosed_of_bounds (Z T : Finset V) (A : V → Finset V)
    (hA : ∀ w ∈ Z, (∀ a b, G.Adj a b → a ∉ Z → b ∈ A w → a ∈ A w) ∧ w ∈ A w ∧
      (A w ⊆ T ∨ Disjoint (A w) T)) :
    G.IsZClosed Z (T : Set V) := by
  intro w hw hne
  obtain ⟨m, hm, hmT⟩ := hne
  obtain ⟨hcl, hwA, hAT⟩ := hA w hw
  have hsub : G.unblockedAnc Z w ⊆ (A w : Set V) := unblockedAnc_subset_of_closed hcl hwA
  rcases hAT with hAT | hdisj
  · exact hsub.trans (Finset.coe_subset.mpr hAT)
  · exact absurd (Finset.mem_coe.mp hmT)
      (Finset.disjoint_left.mp hdisj (Finset.mem_coe.mp (hsub hm)))

/-- A `Z`-closure is bounded by a `Z`-closed, predecessor-closed set containing the source.
Source: none: infrastructure
Kind: L -/
lemma zClosure_subset_of_bounds (Z T : Finset V) (A : V → Finset V)
    (hA : ∀ w ∈ Z, (∀ a b, G.Adj a b → a ∉ Z → b ∈ A w → a ∈ A w) ∧ w ∈ A w ∧
      (A w ⊆ T ∨ Disjoint (A w) T))
    (hT : ∀ a b, G.Adj a b → a ∉ Z → b ∈ T → a ∈ T) {s : V} (hs : s ∈ T) :
    G.zClosure Z s ⊆ (T : Set V) :=
  Digraph.zClosure_subset (isZClosed_of_bounds Z T A hA) (unblockedAnc_subset_of_closed hT hs)

/-- **d-separation from bounds**: disjoint bounds on the two `Z`-closures give d-separation.
Source: none: infrastructure (FAF `dSeparated_iff_disjoint_zClosureSet`)
Kind: L -/
lemma dSeparated_of_bounds (hG : G.IsAcyclic) {V₁ V₂ Z T₁ T₂ : Finset V}
    (h₁ : ∀ s ∈ V₁, G.zClosure Z s ⊆ (T₁ : Set V)) (h₂ : ∀ t ∈ V₂, G.zClosure Z t ⊆ (T₂ : Set V))
    (hd : Disjoint T₁ T₂) : G.DSeparated V₁ V₂ Z := by
  rw [Digraph.dSeparated_iff_disjoint_zClosureSet hG]
  refine Set.disjoint_left.mpr fun x hx₁ hx₂ => ?_
  obtain ⟨s, hs, -, hxs⟩ := Digraph.exists_of_mem_zClosureSet hx₁
  obtain ⟨t, ht, -, hxt⟩ := Digraph.exists_of_mem_zClosureSet hx₂
  exact Finset.disjoint_left.mp hd (Finset.mem_coe.mp (h₁ s hs hxs)) (Finset.mem_coe.mp (h₂ t ht hxt))

/-- A vertex adjacent (unblocked) to two others witnesses non-d-separation.
Source: none: infrastructure (FAF `mem_zClosureSet_of_mem_unblockedAnc`)
Kind: L -/
lemma not_dSeparated_of_common_unblocked (hG : G.IsAcyclic) {V₁ V₂ Z : Finset V} {s t x : V}
    (hs : s ∈ V₁) (ht : t ∈ V₂) (hsZ : s ∉ Z) (htZ : t ∉ Z)
    (hxs : x ∈ G.unblockedAnc Z s) (hxt : x ∈ G.unblockedAnc Z t) : ¬ G.DSeparated V₁ V₂ Z := by
  rw [Digraph.dSeparated_iff_disjoint_zClosureSet hG]
  intro hd
  exact Set.disjoint_left.mp hd (Digraph.mem_zClosureSet_of_mem_unblockedAnc hs hsZ hxs)
    (Digraph.mem_zClosureSet_of_mem_unblockedAnc ht htZ hxt)

end Generic

/-! ### The Fig. 1 graphs -/

namespace DSep

open Fig1 Fig1.Node

/-- Adjacency of the paper's Fig. 1 graph, exactly: `L → H, M → H, H → O, O → S, S → U, L → U`.
Source: carey-everitt-2023 Fig. 1 (l. 60–69), decoded through critique Claim 2.3a
Kind: D
Fidelity: exact -/
def adj₁ : Node → Node → Bool
  | L, H => true
  | M, H => true
  | H, O => true
  | O, S => true
  | S, U => true
  | L, U => true
  | _, _ => false

/-- The paper's Fig. 1 digraph.
Source: carey-everitt-2023 Fig. 1
Kind: D -/
def G₁ : Digraph Node := ⟨fun u v => adj₁ u v = true⟩

instance : DecidableRel G₁.Adj := fun u v => inferInstanceAs (Decidable (adj₁ u v = true))

lemma G₁_acyclic : G₁.IsAcyclic := Digraph.isAcyclic_of_rank rank (by decide)

/-- Fig. 1 with the information link `L → O`: fully updated deference (the agent observes the
latent values before deciding whether to obey).
Source: critique/carey-everitt.md Claim 2.3a ("the addition of an information link `L → O`")
Kind: D -/
def adj₂ : Node → Node → Bool
  | L, O => true
  | u, v => adj₁ u v

/-- The Fig. 1 digraph with `L → O`.
Source: critique Claim 2.3a
Kind: D -/
def G₂ : Digraph Node := ⟨fun u v => adj₂ u v = true⟩

instance : DecidableRel G₂.Adj := fun u v => inferInstanceAs (Decidable (adj₂ u v = true))

lemma G₂_acyclic : G₂.IsAcyclic := Digraph.isAcyclic_of_rank rank (by decide)

/-- **Fully updated deference as d-separation (T8 a).** With `L → O`, `H ⊥ U ∣ {L, O}` over FAF's
`DSeparated`: the request is a nonrequisite observation for `O` (Everitt 2021 Def. 7 with
`(Pa_O ∪ {O}) ∖ {H} = {L, O}`). The `Z`-closure of `H` is inside `{H, M, O}`, that of `U` inside
`{U, S}`.
Source: critique/carey-everitt.md Claim 2.3a (l. 113); corr-wf13-2-056; everitt-2021 Def. 7
Kind: P
Fidelity: exact
Hyps: — -/
theorem dsep_with_link : G₂.DSeparated {H} {U} {L, O} :=
  dSeparated_of_bounds G₂_acyclic (T₁ := {H, M, O}) (T₂ := {U, S})
    (fun s hs => by
      rw [Finset.mem_singleton] at hs
      subst hs
      exact zClosure_subset_of_bounds {L, O} {H, M, O}
        (fun w => if w = L then {L} else {O, H, M}) (by decide) (by decide) (by decide))
    (fun t ht => by
      rw [Finset.mem_singleton] at ht
      subst ht
      exact zClosure_subset_of_bounds {L, O} {U, S}
        (fun w => if w = L then {L} else {O, H, M}) (by decide) (by decide) (by decide))
    (by decide)

/-- **The negative twin.** Without `L → O`, `H` and `U` are d-connected given `O`: the fork
`H ← L → U` is open (`L` is an unblocked ancestor of both).
Source: critique Claim 2.3a; mandate T8(a)
Kind: P
Fidelity: exact
Hyps: — -/
theorem not_dsep_without_link : ¬ G₁.DSeparated {H} {U} {O} :=
  not_dSeparated_of_common_unblocked G₁_acyclic (x := L) (Finset.mem_singleton_self H)
    (Finset.mem_singleton_self U) (by decide) (by decide)
    ((Digraph.mem_unblockedAnc_iff).mpr (Relation.ReflTransGen.single ⟨by decide, by decide⟩))
    ((Digraph.mem_unblockedAnc_iff).mpr (Relation.ReflTransGen.single ⟨by decide, by decide⟩))

/-- Even with the link, conditioning on `O` alone does not separate: it is the observation of `L`
that makes `H` nonrequisite.
Source: mandate T8(a)
Kind: P
Fidelity: exact
Hyps: — -/
theorem not_dsep_with_link_given_O : ¬ G₂.DSeparated {H} {U} {O} :=
  not_dSeparated_of_common_unblocked G₂_acyclic (x := L) (Finset.mem_singleton_self H)
    (Finset.mem_singleton_self U) (by decide) (by decide)
    ((Digraph.mem_unblockedAnc_iff).mpr (Relation.ReflTransGen.single ⟨by decide, by decide⟩))
    ((Digraph.mem_unblockedAnc_iff).mpr (Relation.ReflTransGen.single ⟨by decide, by decide⟩))

end DSep

end Cleanroom.Corrigibility.CorrScimCid

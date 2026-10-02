import Cleanroom.Found.DpCoreTree.Occurrence

/-!
# Definition 7: the plumbing lemmas and Remark 3.4

T5 of [[dp-core-tree-mandate]] (theorem half; the witnesses that separate the quantifier
forms are in `Witnesses.lean`).

* `RecordsFor.covers`: recording implies coverage.
* `RecordsForAll.deviations`, `RecordsForDeviations.self`: the implication chain
  "for every procedure ⟹ for every point-deviation of `C` ⟹ for `C`" (both converses are
  refuted in `Witnesses.lean`: tree J and the gate tree).
* Remark 3.4: coverage together with a.s. subtree-veridicality at **every** `d`-node is
  equivalent to "`occ(d)` and the `O_d`-runs coincide a.s." (`covers_and_veridical_iff`).
* `exists_dNode_of_count_pos` / `count_pos_of_edge`: `#_d(ℓ) > 0` iff some `d`-node lies on
  the path to `ℓ`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Found.DpCoreTree

open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] [DecidableEq ι]

namespace Tree

/-! ### `#_d > 0` iff a `d`-node is on the path -/

/-- A path meeting `d` passes some `d`-node.
Source: none: infrastructure
Kind: L -/
theorem exists_dNode_of_count_pos (d : ι) :
    (B : Tree Ω ι acts K) → ∀ ℓ, 0 < count d B ℓ →
      ∃ q : B.DecNode, pt B q = d ∧ (edgeOf B q ℓ).isSome
  | leaf _ _, _, h => by simp at h
  | chance _ β child, ⟨i, ℓ⟩, h => by
      obtain ⟨q, hq, he⟩ := exists_dNode_of_count_pos d (child i) ℓ (by simpa using h)
      exact ⟨⟨i, q⟩, hq, by rw [edgeOf_chance, dif_pos rfl]; exact he⟩
  | decision d' child, ⟨a, ℓ⟩, h => by
      by_cases hd : d' = d
      · subst hd
        exact ⟨none, rfl, by simp⟩
      · simp only [count_decision, hd, if_false, zero_add] at h
        obtain ⟨q, hq, he⟩ := exists_dNode_of_count_pos d (child a) ℓ h
        exact ⟨some ⟨a, q⟩, hq, by rw [edgeOf_decision_some, dif_pos rfl]; exact he⟩

/-- A path through a `d`-node meets `d`.
Source: none: infrastructure
Kind: L -/
theorem count_pos_of_edge :
    (B : Tree Ω ι acts K) → ∀ (q : B.DecNode) (ℓ : B.Leaves),
      (edgeOf B q ℓ).isSome → 0 < count (pt B q) B ℓ
  | leaf _ _, q, _, _ => q.elim
  | chance _ β child, ⟨i, q⟩, ⟨j, ℓ⟩, h => by
      by_cases hji : j = i
      · subst hji
        rw [edgeOf_chance, dif_pos rfl] at h
        simpa using count_pos_of_edge (child j) q ℓ h
      · simp [edgeOf_chance, hji] at h
  | decision d' child, none, ⟨a, ℓ⟩, _ => by simp
  | decision d' child, some ⟨a, q⟩, ⟨b, ℓ⟩, h => by
      by_cases hba : b = a
      · subst hba
        rw [edgeOf_decision_some, dif_pos rfl] at h
        have := count_pos_of_edge (child b) q ℓ h
        simp only [pt_decision_some, count_decision]
        omega
      · simp [edgeOf_decision_some, hba] at h

/-! ### The implication chain -/

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)

/-- Recording implies coverage.
Source: [[decision-problems-v2]] Remark 3.4 ("Recording implies coverage")
Kind: L -/
theorem RecordsFor.covers {C : Proc ι acts K} {B : Tree Ω ι acts K} {d : ι}
    (h : RecordsFor obs actEv C B d) : Covers obs C B d := by
  intro ℓ hpos hobs
  have := (h ℓ hpos hobs).1
  omega

/-- Recording for every procedure gives recording for every point-deviation of any `C`.
Source: `sl-synthesis.md` line 20
Kind: L -/
theorem RecordsForAll.deviations {B : Tree Ω ι acts K} {d : ι}
    (h : RecordsForAll obs actEv B d) (C : Proc ι acts K) :
    RecordsForDeviations obs actEv C B d :=
  fun m => h (C.deviate d m)

/-- Recording for every point-deviation of `C` gives recording for `C`.
Source: `sl-synthesis.md` line 20
Kind: L -/
theorem RecordsForDeviations.self {C : Proc ι acts K} {B : Tree Ω ι acts K} {d : ι}
    (h : RecordsForDeviations obs actEv C B d) : RecordsFor obs actEv C B d := by
  have := h (C d)
  rwa [show C.deviate d (C d) = C from Function.update_eq_self d C] at this

/-! ### Remark 3.4 -/

/-- A.s. subtree-veridicality of a node (for `C`): every positive-mass leaf below `q` has its
world in `O_{d_q}`.
Source: [[decision-problems-v2]] Remark 3.4 ("Subtree-veridicality *at every* `d`-node")
Kind: D -/
def SubtreeVeridicalAS (C : Proc ι acts K) (B : Tree Ω ι acts K) (q : B.DecNode) : Prop :=
  ∀ ℓ ∈ leavesBelow B q, 0 < leafLaw C B ℓ → world B ℓ ∈ obs (pt B q)

/-- **Remark 3.4**: coverage together with a.s. subtree-veridicality at every `d`-node holds iff
`occ(d)` coincides a.s. with the `O_d`-runs.
Source: [[decision-problems-v2]] Remark 3.4 ("Only together do they identify being consulted
with the observation coming true")
Kind: L
Fidelity: variant: a.s. on both sides (both inclusions on positive-mass leaves; Remark 3.4's
second inclusion is stated plainly) -/
theorem covers_and_veridical_iff (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) :
    (Covers obs C B d ∧ ∀ q, pt B q = d → SubtreeVeridicalAS obs C B q) ↔
      ∀ ℓ, 0 < leafLaw C B ℓ → (ℓ ∈ occ d B ↔ world B ℓ ∈ obs d) := by
  constructor
  · rintro ⟨hcov, hver⟩ ℓ hpos
    constructor
    · intro hocc
      rw [mem_occ] at hocc
      obtain ⟨q, hq, he⟩ := exists_dNode_of_count_pos d B ℓ hocc
      have := hver q hq ℓ ((mem_leavesBelow B q ℓ).mpr he) hpos
      rwa [hq] at this
    · intro hobs
      rw [mem_occ]
      exact hcov ℓ hpos hobs
  · intro h
    refine ⟨fun ℓ hpos hobs => ?_, fun q hq ℓ hℓ hpos => ?_⟩
    · rw [← mem_occ]; exact (h ℓ hpos).mpr hobs
    · rw [hq]
      apply (h ℓ hpos).mp
      rw [mem_occ]
      have := count_pos_of_edge B q ℓ ((mem_leavesBelow B q ℓ).mp hℓ)
      rwa [hq] at this

end Tree

end Cleanroom.Found.DpCoreTree

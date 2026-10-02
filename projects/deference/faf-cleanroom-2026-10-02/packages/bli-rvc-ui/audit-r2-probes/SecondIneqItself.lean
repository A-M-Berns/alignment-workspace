import Cleanroom.Bli.BliRvcUi.Ui.Free

/-!
# Audit round 2 (fidelity) probe: Soto's second limit inequality itself fails, not only its lemma

`secondLimit_fails_free` refutes the *lemma* Soto uses (`lim_m P(¬∀mφ ∧ ⋀_{i≤m} φ(i)) = 0`) by
`P∞(∼u ⋏ ⋀_{i≤m} inst i) ≥ ε > 0`. The inequality he derives from it is
`P(∀mφ) ≥ lim_m P(⋀_{i≤m} φ(i))`. This probe checks that the package's bound yields the failure of
the inequality itself, uniformly in `m`: `P∞(u) + ε ≤ P∞(⋀_{i≤m} inst i)`. Route: Gaifman split
`P∞(⋀) = P∞(u ⋏ ⋀) + P∞(∼u ⋏ ⋀)` and `P∞(u) ≤ P∞(u ⋏ ⋀)` (the schema makes `u` entail every
instance in every completed world). Not imported by the library.
-/

namespace Cleanroom.Bli.BliRvcUi

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

theorem secondIneq_itself {DP : DeductiveProcess}
    (hfree : ∀ n, ∀ φ ∈ DP.D n, ∀ p, freshAtomCode 9 p ∉ sentenceAtomCodes φ)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {P : History} [IsLogicalInductor P (freeDP2 DP)] :
    ∃ ε : ℝ, 0 < ε ∧ ∀ m,
      limitingBelief P freeUI.u + ε ≤ limitingBelief P (instConj freeUI.inst m) := by
  obtain ⟨ε, hε, hm⟩ := secondLimit_fails_free hfree hworld (P := P)
  refine ⟨ε, hε, fun m => ?_⟩
  have hw := freeDP2_hworld hfree hworld
  have hG := lic_limitingBelief_gaifman P _ hw
  have h1 : limitingBelief P freeUI.u ≤
      limitingBelief P (freeUI.u ⋏ instConj freeUI.inst m) :=
    limitingBelief_le_of_theory_imp hw fun v hv hu => by
      rw [PCWorld.holds_and]
      refine ⟨hu, ?_⟩
      rw [holds_instConj]
      intro i _
      exact holds_imp_of_consistentWithTheory_ax
        (PCWorld.consistentWithTheory_union_right (consistentWithTheory_base_of_union hv)) i hu
  have hsplit : limitingBelief P
      ((freeUI.u ⋏ instConj freeUI.inst m) ⋎ (∼freeUI.u ⋏ instConj freeUI.inst m)) =
      limitingBelief P (freeUI.u ⋏ instConj freeUI.inst m) +
        limitingBelief P (∼freeUI.u ⋏ instConj freeUI.inst m) :=
    hG.disjoint_add fun v hv => ((PCWorld.holds_neg v _).mp hv.2.1) hv.1.1
  have hcongr : limitingBelief P
      ((freeUI.u ⋏ instConj freeUI.inst m) ⋎ (∼freeUI.u ⋏ instConj freeUI.inst m)) =
      limitingBelief P (instConj freeUI.inst m) :=
    hG.congr fun v => by
      rw [PCWorld.holds_or, PCWorld.holds_and, PCWorld.holds_and, PCWorld.holds_neg]
      constructor
      · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact h
      · intro h
        by_cases hu : v.Holds freeUI.u
        · exact Or.inl ⟨hu, h⟩
        · exact Or.inr ⟨hu, h⟩
  have := hm m
  linarith

end Cleanroom.Bli.BliRvcUi

#print axioms Cleanroom.Bli.BliRvcUi.secondIneq_itself

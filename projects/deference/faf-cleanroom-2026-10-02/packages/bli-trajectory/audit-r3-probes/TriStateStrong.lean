import Cleanroom.Bli.BliTrajectory.TriState

/-!
# Audit r3 (adversarial) probe — `bli-trajectory`: the `TriState` witness carries faith on the
**Boolean-closed** day family, not only on `Sminus m m`

Not imported by the library. `TriState.faithMarginal_coherent_distinct_not_imp_e2x` states
`FaithMarginal` (scope `Sminus m m`, size-bounded, not `⋏`-closed). Since a two-state witness
refutes that weaker antecedent too (`TwoStateGap.lean`), the statement as written is not what
separates three states from two. Its *proof* never uses the size bound — only the day condition
`∀ a ∈ sentenceAtomCodes φ, atomDay a < m` — so the witness satisfies faith on the family of
**all** sentences whose atoms refer to days `< m`, which is closed under `⋏`, `⋎`, `🡒` and `∼`
(`dayFamily_and`, `dayFamily_neg`): the Notion-strength antecedent, and the one
`Pinning.two_state_pinning_scope` needs. `triHistory_faith_dayFamily` is the strengthened
conjunct the headline could carry at no cost; `triTableVal_ne_in_scope` says the tables differ
*in scope* (at `cohAtom`/`atom 1 ∈ Sminus m m`), not merely as functions.
-/

namespace Cleanroom.Bli.BliTrajectory.AuditR3

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory

open Classical

noncomputable section

/-- The family of sentences whose atoms refer to days `< m`. -/
def dayFamily (m : ℕ) : Set Sentence := {φ | ∀ a ∈ sentenceAtomCodes φ, atomDay a < m}

lemma dayFamily_and {m : ℕ} {φ χ : Sentence} (hφ : φ ∈ dayFamily m) (hχ : χ ∈ dayFamily m) :
    φ ⋏ χ ∈ dayFamily m := by
  intro a ha
  rw [sentenceAtomCodes_and, Finset.mem_union] at ha
  rcases ha with ha | ha
  · exact hφ a ha
  · exact hχ a ha

lemma dayFamily_neg {m : ℕ} {φ : Sentence} (hφ : φ ∈ dayFamily m) : ∼φ ∈ dayFamily m := by
  intro a ha
  rw [sentenceAtomCodes_neg] at ha
  exact hφ a ha

lemma Sminus_subset_dayFamily (m : ℕ) : ↑(Sminus m m) ⊆ dayFamily m := by
  intro φ hφ
  exact (mem_Sminus.mp hφ).2

/-- **Faith on the whole day family** for the `TriState` witness — the proof of
`triHistory_faithMarginal` with the size bound dropped. -/
theorem triHistory_faith_dayFamily (ε : ℝ) :
    ∀ n m, n < m → ∀ φ ∈ dayFamily m, ∀ x : ℝ,
      marginalJoint (triSystem ε) (triHistory ε) n m φ x =
        x * marginalMass (triSystem ε) (triHistory ε) n m φ x := by
  intro n m hnm φ hφ x
  unfold marginalJoint marginalMass
  by_cases hm : m = n + 1
  · subst hm
    rw [sum_filter_triStates, sum_filter_triStates]
    have hday : ∀ a ∈ sentenceAtomCodes φ, atomDay a < n + 1 := hφ
    simp only [triSystem_val, triTableVal_eq_cells hday, triHistory_and_state_cells hday,
      triHistory_stateAtom]
    refine faith_of_levelsets (fun i => ∑ j : Fin 3, triTable i j * (triWorld n 0 j).payout φ)
      (fun i => ∑ j : Fin 3, (triCond ε i j - triTable i j) * (triWorld n 0 j).payout φ)
      (fun i => ∑ j : Fin 3, (1 / 3 : ℝ) * triCond ε i j * (triWorld n 0 j).payout φ) x ?_ ?_
    · intro i
      simp only [← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    · exact triLevel (fun j => (triWorld n 0 j).payout φ)
        (fun j => payout_eq_zero_or_one (triWorld n 0 j) φ) x
  · rw [Finset.sum_eq_zero fun q _ => triHistory_and_stateAtom_ne hm q φ,
      Finset.sum_eq_zero fun q _ => triHistory_stateAtom_ne hm q, mul_zero]

lemma pair_zero_one' : Nat.pair 0 1 = 1 := by decide

lemma atomDay_one' : atomDay 1 = 0 := by
  rw [← pair_zero_one']
  simp [atomDay, atomDayBase, cleanroomBaseTag, Nat.unpair_pair]

lemma triAtom'_mem_Sminus {m : ℕ} (hm : 1 ≤ m) : triAtom' ∈ Sminus m m := by
  rw [mem_Sminus]
  refine ⟨?_, fun a ha => ?_⟩
  · unfold SmallOn triAtom'
    rw [tokenSize_atom]
    have h := length_natDigits4_le_of_lt_pow (n := 1 + 5) (L := 2) (by norm_num)
    have := four_le_sizeBound hm
    omega
  · simp only [triAtom', sentenceAtomCodes_atom, Finset.mem_singleton] at ha
    subst ha
    rw [atomDay_one']
    omega

/-- **The three tables differ in scope**: for every `m ≥ 1` and `i ≠ i'` there is a
`φ ∈ Sminus m m` (namely `cohAtom` or `triAtom'`) at which the tables differ. -/
theorem triTableVal_ne_in_scope (ε : ℝ) {m : ℕ} (hm : 1 ≤ m) {i i' : Fin 3} (h : i ≠ i') :
    ∃ φ ∈ Sminus m m, triTableVal ε m i φ ≠ triTableVal ε m i' φ := by
  have hc := fun k => triTableVal_cohAtom (ε := ε) m k
  have ht := fun k => triTableVal_triAtom' (ε := ε) m k
  fin_cases i <;> fin_cases i'
  · exact absurd rfl h
  · exact ⟨triAtom', triAtom'_mem_Sminus hm, by rw [ht, ht]; norm_num [triTable]⟩
  · exact ⟨cohAtom, cohAtom_mem_Sminus hm, by rw [hc, hc]; norm_num [triTable]⟩
  · exact ⟨triAtom', triAtom'_mem_Sminus hm, by rw [ht, ht]; norm_num [triTable]⟩
  · exact absurd rfl h
  · exact ⟨cohAtom, cohAtom_mem_Sminus hm, by rw [hc, hc]; norm_num [triTable]⟩
  · exact ⟨cohAtom, cohAtom_mem_Sminus hm, by rw [hc, hc]; norm_num [triTable]⟩
  · exact ⟨cohAtom, cohAtom_mem_Sminus hm, by rw [hc, hc]; norm_num [triTable]⟩
  · exact absurd rfl h

end

end Cleanroom.Bli.BliTrajectory.AuditR3

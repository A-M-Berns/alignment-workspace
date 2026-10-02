import Cleanroom.Li.LiSpliceCondition.Candidate
import LogicalInduction.Properties.AffineCoherence

/-!
# Audit round 3 (fidelity) probe: the candidate reading's floor presupposes exploration

`conditioned_candidate_not_gatedExploits` (`Candidate.lean`) takes an inductor `P` over `DP`, an
e.c. family `ψ` and a uniform floor `ε ≤ P n (ψ n)`. Its docstring says the conditions "may be
mutually exclusive across days and refuted by later stages". This probe shows the limit of that
sentence: if *every* `ψ n` is refuted by the completed theory (the regime of an always-unchosen
candidate), the floor is uninhabitable by any inductor — FAF's provability induction
(`lic_provind_false`) drives `P n (ψ n)` to `0`. So the hypothesis package of the candidate
theorem itself forces some candidate to be realizable in the completed theory: the floor is not
a free parameter but a statement that exploration actually realizes the candidate. Not imported
by the library.
-/

namespace Cleanroom.Li.LiSpliceCondition

open LogicalInduction LO.Propositional Filter Topology

/-- If every member of an e.c. family is refuted by the completed theory, no inductor keeps a
uniform floor on the day's price of the day's own member. -/
theorem candidate_floor_impossible_of_all_refuted (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (ψ : ℕ → Sentence) (hcode : MachineSentenceCodes ψ)
    (hdis : ∀ n, ∀ v : PCWorld, v.ConsistentWithTheory DP → ¬ v.Holds (ψ n))
    (ε : ℚ) (hε : 0 < (ε : ℝ)) (hfloor : ∀ n, (ε : ℝ) ≤ P n (ψ n)) : False := by
  have h : AsympEq (fun n => P n (ψ n)) (fun _ => 0) :=
    lic_provind_false P DP ψ hcode
      (fun n v hv => (PCWorld.holds_neg v (ψ n)).mpr (hdis n v hv)) hworld
  have h' : Tendsto (fun n => P n (ψ n)) atTop (𝓝 0) := by
    simpa [AsympEq, sub_zero] using h
  have he : ∀ᶠ n in atTop, P n (ψ n) < ε := h'.eventually (eventually_lt_nhds hε)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp he
  exact absurd (hfloor N) (not_le.mpr (hN N le_rfl))

/-- Contrapositive, in the shape of the candidate theorem's hypotheses: the floor forces some
day's candidate to hold in some world consistent with the completed theory. -/
theorem candidate_floor_realizable (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (ψ : ℕ → Sentence) (hcode : MachineSentenceCodes ψ)
    (ε : ℚ) (hε : 0 < (ε : ℝ)) (hfloor : ∀ n, (ε : ℝ) ≤ P n (ψ n)) :
    ∃ n, ∃ v : PCWorld, v.ConsistentWithTheory DP ∧ v.Holds (ψ n) := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  exact candidate_floor_impossible_of_all_refuted P DP hworld ψ hcode hcon ε hε hfloor

end Cleanroom.Li.LiSpliceCondition

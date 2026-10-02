import Cleanroom.Bli.BliLinkage.LiaPackage

/-!
# bli-linkage audit r4 (fidelity) — probe: the uniform `o(1)` variant of `E1x` is dead too

Findings FR-11 says in prose that "the uniform `o(1)` variant of `E1x` on the whole small
algebra is ruled out by the same counting: on day `n ≥ 4` most small tautologies are unlisted
and priced exactly `0`, so the sup-distance between the LIA and any stage mixture over
`smallSet n` is `1`". That sentence is not in Lean. This probe machine-checks it on day `4`,
for every deductive process and every stage mixture (any `atoms`): some day-`4` small sentence
is priced `0` by FAF's LIA and `1` by `P 4`. Nothing here is a package object beyond
`LiaPackage`'s own lemmas; the probe is not imported by the library.
-/

namespace Cleanroom.Bli.BliLinkage.AuditR4

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

/-- Some member of the day-`4` tautology chain is not a listed key of the LIA's day-`4`
belief state (`16384` candidates, at most `2945` keys), for every deductive process. -/
theorem exists_tautChain_not_listed_day4 (DP : DeductiveProcess) :
    ∃ k < 2 ^ (2 ^ 4 - 2), tautChain k ∉ (liaStates DP 4).support := by
  by_contra h
  push Not at h
  have hsub : (Finset.range (2 ^ (2 ^ 4 - 2))).image tautChain ⊆ (liaStates DP 4).support := by
    intro φ hφ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hφ
    exact h k (Finset.mem_range.1 hk)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ tautChain_injective, Finset.card_range] at h1
  have h2 := liaStates_support_card_le_day4 DP
  norm_num at h1
  omega

/-- **Day-`4` sup-distance `1`**: for every deductive process, every atom set and every `P`
with `PCPσ atoms DP P`, there is a day-`4` small sentence that FAF's LIA prices at exactly `0`
and `P 4` prices at exactly `1`. So no `o(1)`-uniform agreement over `smallSet n` between
the LIA and a stage mixture is possible either (the distance is `1` on day `4`; the same
argument runs on every later day, not checked here). -/
theorem lia_stage_mixture_sup_distance_one_day4 (DP : DeductiveProcess)
    {atoms : ℕ → Finset ℕ} {P : History} (hcoh : PCPσ atoms DP P) :
    ∃ φ ∈ smallSet 4, liaHistory DP 4 φ = 0 ∧ P 4 φ = 1 := by
  obtain ⟨k, hk, hnot⟩ := exists_tautChain_not_listed_day4 DP
  have hsmall : tautChain k ∈ smallSet 4 := by
    refine tautChain_mem_smallSet ?_
    rw [sizeBound_eq_four_mul 4 (by norm_num)]
    generalize 2 ^ (2 ^ 4 - 2) = K at hk ⊢
    omega
  refine ⟨tautChain k, hsmall, ?_, ?_⟩
  · rw [liaHistory_eq_quote_cast]
    change (((liaStates DP 4).quote (tautChain k) : ℚ) : ℝ) = 0
    rw [RationalBeliefState.quote_eq_zero_of_not_mem _ hnot]
    norm_num
  · exact coherentOn_valid_one (hcoh 4)
      ((Cleanroom.Bli.BliLinkageB.atoms_subset_smallAtoms hsmall).trans Finset.subset_union_left)
      (fun v => holds_tautChain v k)

end Cleanroom.Bli.BliLinkage.AuditR4

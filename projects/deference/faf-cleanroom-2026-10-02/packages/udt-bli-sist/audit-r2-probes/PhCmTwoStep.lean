import Cleanroom.Bli.UdtBliSist.PhCm

/-!
# Audit round 2 (adversarial) probe: on `PhCm.crux` the two-step conditional genuinely changes
the values

`PhCm.crux` states that the one-step and two-step maximizer sets coincide on the CM/PH prior with
`Σ = {p}` but does not export the values. The mandate's trap condition for T5 asks for a witness
"where the two-step conditional genuinely changes a value". Here: on the instance (`1/4` each,
`(100, 10)`, PH tables reading their own node) the `Σ`-class weight at `CM_A` is `1/2` under both
actions, so by `EU_sub_eq_twoStep` the two-step difference is twice the one-step one:
`twoStepEU {p} CM_A pay − twoStepEU {p} CM_A refuse = 45` against `EU CM_A pay − EU CM_A refuse
= 45/2`. The crux's content is exercised on this prior (not an artifact of equal values). Not
imported by the library.
-/

namespace Cleanroom.Bli.UdtBliSist.PhCm

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

/-- The instance's data. -/
abbrev D₀ : IndepData witIndex 1 fourTables Bool := phData wQ wQ_nonneg wQ_sum fOther 10 100 200 0

/-- The instance's prior. -/
abbrev P₀ : FiniteBLIPrior witIndex 1 fourTables Bool := phPrior wQ wQ_nonneg wQ_sum fOther 10 100 200 0

/-- The `Σ`-class weight at `CM_A` is `1/2` under every action (`Reflective`: it is
`μ(CM_A) + μ(CM_R) = 1/4 + 1/4`). -/
theorem classProb_cm (a : Bool) :
    classProb P₀ (sigmaClass ({pS} : Finset ↥(witIndex.S 1)) fAsk) fAsk a = 1 / 2 := by
  rw [sigmaClass_p]
  unfold classProb cmClass
  rw [Finset.sum_pair fAsk_ne_fBoth]
  have hpt : 0 < massOf D₀.ν (fun π => π fAsk = a) := by
    rw [massOf_point]; norm_num
  have h0 := stateMass_toPrior_of_injective D₀ fourState_injective (0 : Fin 4)
  have h1 := stateMass_toPrior_of_injective D₀ fourState_injective (1 : Fin 4)
  simp only [state₀_eq, fourState_zero, fourState_one] at h0 h1
  change P₀.branchProb fAsk fAsk a + P₀.branchProb fBoth fAsk a = 1 / 2
  change D₀.toPrior.branchProb fAsk fAsk a + D₀.toPrior.branchProb fBoth fAsk a = 1 / 2
  rw [branchProb_toPrior D₀ fAsk fAsk a hpt, branchProb_toPrior D₀ fBoth fAsk a hpt, h0, h1]
  show wQ 0 + wQ 1 = 1 / 2
  norm_num [wQ]

/-- **The two-step values differ from the one-step values**: the two-step difference is `45`, the
one-step difference `45/2` — the `Σ`-class conditional doubles the stakes, and the maximizer sets
still coincide (`PhCm.crux`). -/
theorem twoStep_vs_oneStep :
    twoStepEU P₀ ({pS} : Finset ↥(witIndex.S 1)) fAsk true -
        twoStepEU P₀ ({pS} : Finset ↥(witIndex.S 1)) fAsk false = 45 ∧
      P₀.EU fAsk true - P₀.EU fAsk false = 45 / 2 := by
  obtain ⟨hR, hI, _, _, _, _, _, _⟩ := crux wQ wQ_nonneg wQ_sum fOther 10 100 200 0
    fAsk_ne_fOther.symm (by norm_num [wQ]) (by norm_num) (by norm_num [wQ])
  have hd := (instance_pay).1
  have h := EU_sub_eq_twoStep P₀ ({pS} : Finset ↥(witIndex.S 1)) fAsk hR hI true false
  rw [classProb_cm, hd] at h
  exact ⟨by linarith, hd⟩

end Cleanroom.Bli.UdtBliSist.PhCm

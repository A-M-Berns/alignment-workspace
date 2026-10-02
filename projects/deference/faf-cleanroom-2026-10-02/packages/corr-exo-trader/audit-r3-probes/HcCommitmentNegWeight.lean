import Cleanroom.Corrigibility.CorrExoTrader.Reflect

/-!
# Audit r3 (adversarial) probe — `HcModel.w` has no sign constraint, so clause (f) is not a
correlation

`HcModel.w : Bool → Bool → ℝ` is glossed as "the prior weight of the cell"; `HcCommitment`'s clause
(e) bounds only the row sums (`∀ s, 0 < ∑ b, w s b`) and clause (f) is the cross-product inequality.
With a negative cell the inequality says nothing about association. `hcNeg` below puts weight
`−1/4` on (faithful, pressed), makes the press *independent* of the state in the corrupted row
(`1/2`, `1/2`), and satisfies `HcCommitment` — clause (f) holds only through the negative weight.
Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrExoTrader

open HcModel

/-- A negative "prior weight" on (faithful, pressed); press independent of state in the corrupted row. -/
noncomputable def hcNeg : HcModel where
  w s b := if s then 1 / 2 else (if b then -1 / 4 else 3 / 4)
  algoVal s a := if a then (if s then -1 else 1) else 0
  implVal s a := if a then (if s then 2 else 1) else 0

theorem hcNeg_negative_cell : hcNeg.w false true < 0 := by norm_num [hcNeg]

theorem hcNeg_press_independent_in_true : hcNeg.w true true = hcNeg.w true false := by
  simp [hcNeg]

theorem hcNeg_stopWhenPressed_optimal (π : Bool → Bool) :
    hcNeg.udtValue π ≤ hcNeg.udtValue stopWhenPressed := by
  cases hπt : π true <;> cases hπf : π false <;>
    simp [udtValue, stopWhenPressed, hcNeg, hπt, hπf] <;> norm_num

/-- `hcNeg` satisfies the definition of record. -/
theorem hcNeg_commitment : HcCommitment hcNeg := by
  refine ⟨hcNeg_stopWhenPressed_optimal, ?_, ?_, ⟨true, true, by norm_num [hcNeg]⟩,
    fun s => ?_, ?_⟩
  · simp [udtValue, alwaysContinue, stopWhenPressed, hcNeg]
    norm_num
  · simp [updatefulPressedValue, hcNeg]
    norm_num
  · cases s <;> simp [hcNeg] <;> norm_num
  · norm_num [hcNeg]

end Cleanroom.Corrigibility.CorrExoTrader

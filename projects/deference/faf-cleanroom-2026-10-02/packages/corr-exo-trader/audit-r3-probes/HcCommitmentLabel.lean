import Cleanroom.Corrigibility.CorrExoTrader.Reflect

/-!
# Audit r3 (adversarial) probe — `HcCommitment`'s correlation clause correlates the press with a
*label*, not with divergence

`HcModel.HcCommitment` (repair round 2) says, per its docstring and ledger row, that "(e) the press
correlates with corruption — positive association in the `2 × 2` prior table" (line 57's "if the
button correlates with divergence"). The Lean clause is
`w false true * w true false < w true true * w false false`: positive association between the press
and the state *labelled* `true`. Nothing in the definition says the state labelled `true` is where
the implemented table diverges from the algorithm's: clause (d) only asks for *some* cell with
`implVal ≠ algoVal`, and there is no clause `∀ a, implVal false a = algoVal false a`.

`hcSwap` below keeps `hcWitness`'s prior and algorithmic table, makes the implemented table agree
with the algorithm in state `true` (the pressed-correlated state has **no** divergence) and lie in
state `false` (the faithful state diverges). It satisfies `HcCommitment` — so in a model of the
definition of record the press is positively associated with the *non-divergent* state, the
opposite of line 57's mechanism. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrExoTrader

open HcModel

/-- `hcWitness`'s prior and algorithmic table; the implemented table agrees with the algorithm in
state `true` and diverges (`100` for continue) in state `false`. -/
noncomputable def hcSwap : HcModel where
  w s b := if s then (if b then 9 / 20 else 1 / 20) else (if b then 1 / 20 else 9 / 20)
  algoVal s a := if a then (if s then -1 else 1) else 0
  implVal s a := if a then (if s then -1 else 100) else 0

/-- In `hcSwap` the pressed-correlated state `true` is *faithful*: implemented = algorithmic. -/
theorem hcSwap_true_state_faithful : ∀ a, hcSwap.implVal true a = hcSwap.algoVal true a := by
  intro a; cases a <;> simp [hcSwap]

/-- In `hcSwap` the divergence sits in state `false`. -/
theorem hcSwap_false_state_diverges : hcSwap.implVal false true ≠ hcSwap.algoVal false true := by
  norm_num [hcSwap]

/-- The same prior as `hcWitness`: the press is positively associated with state `true`. -/
theorem hcSwap_press_correlated_with_true :
    hcSwap.w false true * hcSwap.w true false < hcSwap.w true true * hcSwap.w false false := by
  norm_num [hcSwap]

theorem hcSwap_stopWhenPressed_optimal (π : Bool → Bool) :
    hcSwap.udtValue π ≤ hcSwap.udtValue stopWhenPressed := by
  cases hπt : π true <;> cases hπf : π false <;>
    simp [udtValue, stopWhenPressed, hcSwap, hπt, hπf] <;> norm_num

/-- `hcSwap` satisfies the definition of record. -/
theorem hcSwap_commitment : HcCommitment hcSwap := by
  refine ⟨hcSwap_stopWhenPressed_optimal, ?_, ?_, ⟨false, true, by norm_num [hcSwap]⟩,
    fun s => ?_, hcSwap_press_correlated_with_true⟩
  · simp [udtValue, alwaysContinue, stopWhenPressed, hcSwap]
    norm_num
  · simp [updatefulPressedValue, hcSwap]
    norm_num
  · cases s <;> simp [hcSwap] <;> norm_num

end Cleanroom.Corrigibility.CorrExoTrader

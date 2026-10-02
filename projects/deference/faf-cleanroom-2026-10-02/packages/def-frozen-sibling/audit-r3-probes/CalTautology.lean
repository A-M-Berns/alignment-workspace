import Cleanroom.Deference.DefFrozenSibling.Tracking

/-!
# Audit round 3 (adversarial) probe — the calibration sentence at a wide tolerance

`metaTrust` is stated for every `ε₀ > 0`. At `ε₀ ≥ 2` the calibration sentence
`calSentence ε₀ n` holds in every completed-theory world of the advised reasoner's process for
range reasons alone (`a n, Y n ∈ [0,1]`, so `|a n − Y n| ≤ 1 ≤ ε₀/2`), and `metaTrust`'s
conclusion follows from provability induction with **no `hz` and no tracking**. So the content
of T2b sits at `ε₀ < 2`; the theorem is not wrong, but a reader instantiating it at a wide
tolerance gets a range tautology. Not imported by the library.
-/

namespace Cleanroom.Deference.DefFrozenSibling.AuditR3

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane Cleanroom.Deference.DefTrackingPin Cleanroom.Deference.DefFrozenSibling
open Filter Topology

/-- At `ε₀ ≥ 2` every calibration clause holds in every world, by the `[0,1]` ranges alone. -/
theorem calSentence_holds_of_two_le (S : FrozenSystem) {ε₀ : ℚ} (h2 : 2 ≤ ε₀) (n : ℕ)
    (w : PCWorld) (hw : w.ConsistentWithTheory S.processH) : w.Holds (calSentence ε₀ n) := by
  refine calSentence_holds_of_close S n ?_ w hw
  obtain ⟨hY0, hY1⟩ := S.Y_mem_Icc n
  obtain ⟨ha0, ha1⟩ := S.a_mem_Icc n
  rw [abs_le]
  constructor <;> linarith

/-- `metaTrust`'s conclusion at `ε₀ ≥ 2`, with no `hz` and no T1. -/
theorem metaTrust_of_two_le (S : FrozenSystem) {ε₀ : ℚ} (h2 : 2 ≤ ε₀) :
    (fun n => S.Hplus n (calSentence ε₀ n)) ≈ₙ fun _ => 1 := by
  haveI := S.Hplus_inductor
  exact provind_eventually_true S.Hplus S.processH (calSentence ε₀) (calSentence_codes ε₀)
    (Filter.Eventually.of_forall fun n w hw => calSentence_holds_of_two_le S h2 n w hw) S.hworldH

end Cleanroom.Deference.DefFrozenSibling.AuditR3

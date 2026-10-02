import Cleanroom.Corrigibility.CorrChannelVoi.Cells

/-!
# `corr-channel-voi` · audit r3 (adversarial) probe: pointwise trust ⟺ obedience is free

Not imported by the library.

Load-bearing 5 renders "desideratum 1 on every signal" as the product-form cell inequality on the
joint model (`pointwiseTrust_iff_cells`, an unfolding — audit r2 adversarial N5; report deviation
6). The package already holds the two bridges that make the phrase literal in Good's-theorem
terms, but does not compose them: `cellModel_pressExpectOn_eq_signalGain` (the cell number is the
press-cell gain of `⟨button, k⟩`) and `freeValue_eq_forcedValue_iff` (that gain is `≤ 0` on every
press-cell iff forcing the press costs nothing). Composed: **pointwise trust holds iff the free and
the forced channel are worth the same**, i.e. iff *stop is a best response on every press-signal
of the experiment the agent actually observes*. One `forall_congr'`; offered as the T9↔T10 bridge
the mandate's "desideratum 1 on every signal" deserves.
-/

namespace Cleanroom.Corrigibility.CorrChannelVoi.AuditR3Adversarial

open Finset hiding expect
open Cleanroom.Found.LitDdbFrames.Blackwell Cleanroom.Trust.TtFiniteFrames
  Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep FactoredSpaces
  Cleanroom.Corrigibility.CorrChannelVoi

noncomputable section

variable {S : Type} [Fintype S] [DecidableEq S]

theorem pointwiseTrust_iff_free_eq_forced (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (k : Experiment World S) :
    PointwiseTrust ε α β c h k ↔
      freeValue (twoPoint ε hε) (twoButton α β hα hβ) k (twoValue c h .cont) =
        forcedValue (twoPoint ε hε) (twoButton α β hα hβ) k (twoValue c h .cont) := by
  rw [freeValue_eq_forcedValue_iff, pointwiseTrust_iff_cells ε α β c h hε hα hβ k .press]
  refine forall_congr' fun s => ?_
  rw [cellModel_pressExpectOn_eq_signalGain]

end

end Cleanroom.Corrigibility.CorrChannelVoi.AuditR3Adversarial

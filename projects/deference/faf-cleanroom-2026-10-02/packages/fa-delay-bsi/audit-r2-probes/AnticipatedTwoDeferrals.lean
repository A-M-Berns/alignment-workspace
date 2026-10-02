import Cleanroom.Fa.FaDelayBsi.Anticipated

/-!
# Audit r2 (fidelity) probe: `anticipated_deference` with two deferrals

`anticipated_deference` (`Anticipated.lean`) states the quote package and the anticipated-quote
package over the *same* deferral `g`: `pkg : CrossQuotePackage H DPA g (fun _ => X) Y` and
`hQ : AnticipatedQuote H DPH Y A g Q`. The source (msg 43) has two independent horizons — the
quote's own lookahead `f` (`A` quotes `𝔼^H_{f m}(X)` at day `m`) and the day `g n` at which `H`
anticipates the quote. The proof uses only `quoteSeq Y A ∘ g → L`, so the identification is not
needed. This probe elaborates the statement with separate `f` and `g`, by the same proof.
Not imported by the library; evidence for a non-blocking item.
-/

namespace Cleanroom.Fa.FaDelayBsi.AuditR2

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Cleanroom.Fa.FaTheoremA
open Cleanroom.Fa.FaDelayBsi
open Filter Topology

theorem anticipated_deference_two_deferrals {H : History} {DPH : DeductiveProcess}
    [IsLogicalInductor H DPH]
    (X : LUV) (hcode : X.MachineThresholdCodes)
    (hworldH : ∀ n, ∃ w : PCWorld, w.ConsistentWith (DPH.D n))
    (hval : ∀ w : PCWorld, w.ConsistentWithTheory DPH → ∃ x : ℝ, w.ValuesAt X x)
    {A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    (hworldA : ∀ n, ∃ w : PCWorld, w.ConsistentWith (DPA.D n))
    {f : DeferralFunction} {Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f (fun _ => X) Y)
    {g : DeferralFunction} {Q : ℕ → LUV} (hQ : AnticipatedQuote H DPH Y A g Q) :
    (fun n => (Q n).expect H n) ≈ₙ fun n => X.expect H n := by
  obtain ⟨L, hL, ha⟩ := theoremA_common_limit (A := A) X hcode hworldH hval hworldA pkg
  have hfut : Tendsto (fun n => quoteSeq Y A (g.f n)) atTop (𝓝 L) := ha.comp g.tendsto_atTop
  have hQlim := expect_tendsto_of_determinedVia_tendsto H DPH Q hQ.quote_codes _ hQ.reflected L
    hfut hworldH
  exact asympEq_of_tendsto hQlim hL

end Cleanroom.Fa.FaDelayBsi.AuditR2

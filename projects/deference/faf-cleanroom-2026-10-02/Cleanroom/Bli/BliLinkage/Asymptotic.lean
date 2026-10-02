import Cleanroom.Bli.BliLinkage.Defs
import Cleanroom.Bli.BliLinkage.AttemptA.Asymptotic

/-!
# `bli-linkage` — K5c: the `o(1)` bracket balance over FAF's LIA, threshold form (of record)

Only **attempt A** reached K5c, and only in the form the mandate calls the first step: FAF's own
`lic_no_expected_net_update_closed T succDeferral φ hφ` (`thm:ceu`) with `LUV.expect` unfolded to
the `1/(n+1)`-mesh bracket over the threshold atoms `⌜Q_{n+1}(φ n) > i/(n+1)⌝`. That **is** the
program's `o(1)` no-net-expected-update in threshold form, along e.c. families only; it is
ledgered **L** (a citation; nothing composed), not the mandate's **C**. The B2 cell-literal form
(the `LUVCombination.DeterminedViaTheory` certificate for "cell literal `r` ↔ threshold
conjunction" and `lic_expect_combination_provind_eq_ofDetermined`) was attempted by neither
attempt and is not stated OPEN (no Lean statement was written). K5d (the ℓ¹ projection) and K6
likewise. Nothing says the LIA is linked at any finite day (mandate Known issue 7).
-/

namespace Cleanroom.Bli.BliLinkage

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [LO.Entailment.Consistent T]

/-- **K5c — the `o(1)` bracket balance over FAF's LIA, threshold form** (FAF's `thm:ceu` with the
expectation unfolded): for an e.c. family `φ`,
`liaHistory (paperDP T) n (φ n) ≈ₙ (n+1)⁻¹ · ∑_{i<n+1} liaHistory (paperDP T) n ⌜Q_{n+1}(φ n) > i/(n+1)⌝`.
Source: [[bli-program]] §3.6(v); bli-slides-031 (R2); mandate § K5c; FAF `lic_no_expected_net_update_closed`, `LUV.expect`; attempt A `Asymptotic.nnu_asymptotic_threshold`
Kind: L
Fidelity: variant: threshold atoms of the future-price LUV, mesh `1/(n+1)`, in place of the B2 cell literals; `o(1)` along e.c. families, not exact at finite days
Hyps: (a) (`hφ : MachineSentenceCodes φ` is the family's e.c. certificate, a hypothesis of the statement) -/
theorem nnu_asymptotic_threshold (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ) :
    (fun n => liaHistory (paperDP T) n (φ n)) ≈ₙ
      fun n => ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1),
        liaHistory (paperDP T) n
          (((paperFutureQuoteCode T succDeferral φ hφ).luv n).gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ))) :=
  AttemptA.Asymptotic.nnu_asymptotic_threshold T φ hφ

end Cleanroom.Bli.BliLinkage

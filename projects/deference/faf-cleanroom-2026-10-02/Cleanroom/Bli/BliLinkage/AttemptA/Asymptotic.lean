import Cleanroom.Bli.BliLinkage.AttemptA.Defs
import LogicalInduction.Construction.Paper.Market

/-!
# `bli-linkage`, attempt A — K5c: the `o(1)` bracket balance over FAF's LIA, threshold form

The only asymptotic statement of this attempt, and it is **FAF's own theorem cited verbatim**:
`lic_no_expected_net_update_closed T succDeferral φ hφ` says that along an e.c. family `φ` the
LIA's day-`n` price of `φ n` is asymptotically its day-`n` expectation of its own day-`(n+1)`
price of `φ n`, and `LUV.expect` unfolds to the bracket sum
`(n+1)⁻¹ · ∑_{i < n+1} Q n ⌜Q_{n+1}(φ n) > i/(n+1)⌝` over the threshold atoms at mesh
`1/(n+1)`. That **is** the program's `o(1)` no-net-expected-update in threshold form
(mandate § K5c); it is ledgered **L** here, not the mandate's **C**, because nothing is
composed — the statement is FAF's with the expectation unfolded. The further step the mandate
asks for — the B2 cell-literal form through a `LUVCombination.DeterminedViaTheory`
certificate and `lic_expect_combination_provind_eq_ofDetermined` — was **not attempted**.
Along e.c. families only; nothing says the LIA is linked at any finite day (mandate Known
issue 7).
-/

namespace Cleanroom.Bli.BliLinkage.AttemptA

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

namespace Asymptotic

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [LO.Entailment.Consistent T]

/-- **K5c — the `o(1)` bracket balance over FAF's LIA, threshold form** (FAF's `thm:ceu` with
the expectation unfolded): for an e.c. family `φ`,
`liaHistory (paperDP T) n (φ n) ≈ₙ (n+1)⁻¹ · ∑_{i<n+1} liaHistory (paperDP T) n ⌜Q_{n+1}(φ n) > i/(n+1)⌝`,
where the threshold atoms are those of the future-price LUV `paperFutureQuoteCode T succDeferral φ hφ`.
Source: [[bli-program]] §3.6(v); bli-slides-031 (R2); mandate § K5c; FAF
`lic_no_expected_net_update_closed` (`Construction/Paper/Market.lean:285`), `LUV.expect`
(`Framework/Expectations.lean:323`)
Kind: L
Fidelity: variant: threshold atoms of the future-price LUV, mesh `1/(n+1)`, in place of the B2 cell literals; `o(1)` along e.c. families, not exact at finite days
Hyps: (a) (`hφ : MachineSentenceCodes φ` is the family's e.c. certificate, a hypothesis of the statement) -/
theorem nnu_asymptotic_threshold (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ) :
    (fun n => liaHistory (paperDP T) n (φ n)) ≈ₙ
      fun n => ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1),
        liaHistory (paperDP T) n
          (((paperFutureQuoteCode T succDeferral φ hφ).luv n).gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ))) :=
  lic_no_expected_net_update_closed T succDeferral φ hφ

end Asymptotic

end Cleanroom.Bli.BliLinkage.AttemptA

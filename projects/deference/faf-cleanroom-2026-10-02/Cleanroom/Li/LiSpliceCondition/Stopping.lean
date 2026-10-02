import Cleanroom.Li.LiSpliceCondition.Defs
import LogicalInduction.Properties.SelfTrust

/-!
# `li-splice-condition` · Stopping: LI adapted stopping (T5)

Package `Cleanroom.Li.LiSpliceCondition` ([[li-splice-condition-mandate]]), file 10 of the layout.
R1.7's "LI adapted stopping": for finitely many candidate deferral days and a generable partition
of unity, `ccee` applied once per candidate and summed. Over FAF this is
`lic_no_expected_net_update_conditional` (`thm:ccee`, with its `1/(n+1)` mesh slack carried by the
`ConditionalExpectationQuote` certificate) applied to each candidate and `AsympEq.add` /
`AsympEq.finsetSum`. **Indexing (the inventory's flag):** FAF's quote structure reads the weight
at the deferral day, `w (f n)`, evaluated by the day-`f n` market; the source's "`w⁽ʲ⁾` depending
only on prices up to day `m_j`" is the rank condition of FAF's `GeneratedRatFeature` at
`f n ≥ m_j`, and its `m₁ < … < m_k` is the special case of constant deferral functions shifted to
satisfy `n < f n`. The source's left-hand side `𝔼_n(X_n)` would need linearity of expectation to
split as `Σ_j 𝔼_n(X_n · w⁽ʲ⁾)` (`loe`, FAF's `lic_linearity_of_expectation_seq` with its
representation hypotheses); that split is **not** done here — the statement of record is the
summed `ccee`, whose right-hand side "`𝔼_n(⌜𝔼_τ(X_n)⌝)`" is *by definition* the sum.
-/

namespace Cleanroom.Li.LiSpliceCondition

open LogicalInduction LO.Propositional

/-- **LI adapted stopping, two candidates.** For two deferral functions and a generable partition
of unity `w`, `1 − w` (each quote package carries `PGenerableRat` of its weight), the sum of the
two quoted products is asymptotically the sum of the two quoted future expectations:
`ccee` twice, added.
Source: [[corr-wf14-inventory]] 049 (`selection.md` R1.7, `k = 2`); mandate T5.1
Kind: C
Fidelity: variant: the summed `ccee` (the `loe` split of `𝔼_n(X_n)` is not performed); FAF's `w (f n)` indexing; the `1/(n+1)` mesh slack is inside the quote packages
Hyps: (a) the two `ConditionalExpectationQuote` packages are FAF's own certificates -/
theorem adapted_stopping_two (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (f₁ f₂ : DeferralFunction)
    (X Z₁ Z₁' Z₂ Z₂' : ℕ → LUV) (w : ℕ → ℚ)
    (hq₁ : ConditionalExpectationQuote P DP f₁ X Z₁ Z₁' w)
    (hq₂ : ConditionalExpectationQuote P DP f₂ X Z₂ Z₂' (fun n => 1 - w n)) :
    AsympEq (fun n => (Z₁ n).expect P n + (Z₂ n).expect P n)
      (fun n => (Z₁' n).expect P n + (Z₂' n).expect P n) :=
  AsympEq.add (lic_no_expected_net_update_conditional P DP f₁ X Z₁ Z₁' w hcons hq₁)
    (lic_no_expected_net_update_conditional P DP f₂ X Z₂ Z₂' _ hcons hq₂)

/-- **LI adapted stopping, finitely many candidates.** For a finite family of deferral functions
with quote packages, the sum of the quoted products is asymptotically the sum of the quoted future
expectations. The partition-of-unity condition `Σ_j w j n = 1` is what makes the left-hand side
"`𝔼_n(X_n)`" under linearity; the summed `ccee` holds without it.
Source: [[corr-wf14-inventory]] 049 (R1.7, general `k`); mandate T5.1
Kind: C
Fidelity: variant: as `adapted_stopping_two`
Hyps: (a) -/
theorem adapted_stopping_finite (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) {J : Type*} [Fintype J]
    (f : J → DeferralFunction) (X : ℕ → LUV) (Z Z' : J → ℕ → LUV) (w : J → ℕ → ℚ)
    (hq : ∀ j, ConditionalExpectationQuote P DP (f j) X (Z j) (Z' j) (w j)) :
    AsympEq (fun n => ∑ j, (Z j n).expect P n) (fun n => ∑ j, (Z' j n).expect P n) :=
  AsympEq.finsetSum fun j =>
    lic_no_expected_net_update_conditional P DP (f j) X (Z j) (Z' j) (w j) hcons (hq j)

end Cleanroom.Li.LiSpliceCondition

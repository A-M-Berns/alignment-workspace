import Cleanroom.Corrigibility.CorrLiShutdown.Legitimacy

/-!
# Audit round 4 (fidelity) probe — F19's stated obstacle versus FAF's actual quantifier

Findings F19, `corr-li-shutdown-open.txt` and `Legitimacy.lean` §(b′) say that the mandate's
`loe` route to `decidedWeight_factors_open` "resists for a structural reason": FAF's
`lic_linearity_of_expectation_seq` needs `DeterminedViaTheory`, which "asks the day-`n`
deductive state `D_n` to decide the value of the combination, i.e. the quote literals of the
day-`n` value of `a_n` — and no deductive process decides the literals of its own day-`n` prices
at day `n`, because the day-`n` prices are computed *from* `D_n`".

This probe checks that claim against FAF (not imported by the library):

* `DeterminedViaTheory` quantifies over `v.ConsistentWithTheory DP`, which FAF defines as
  `∀ n, v.ConsistentWith (DP.D n)` — worlds consistent with **every** stage (the completed
  theory, the paper's `cworlds(Θ)`), not the day-`n` stage (`probe_consistentWithTheory_unfold`).
* FAF's `RationalQuoteCode.reflected` values the quoted LUV of **any** `RationalQuoteCode` at the
  represented rational in every such world. The package's own current-day quote
  `paperCurrentWeightQuoteCode` is a `RationalQuoteCode`, so every completed-theory world of
  `paperDP T` values it at `w n` (`probe_currentWeight_reflected`) — by the same mechanism that
  serves the deferred quote in `thm:ccee`. No deferral is involved.
* FAF's mesh product law then places the mesh product of `X n` with the current-day quote within
  `1/(n+1)` of `x · w n` in every completed-theory world (`probe_meshProduct_current_near`).

So the loe-shaped combination `w_n·X_n − ⌜X_n·w_n⌝` is approximately determined (within the mesh
slack) in every completed-theory world; the exact `hdet0` of `lic_linearity_of_expectation_seq`
fails only by that slack, and FAF's own `lic_expect_combination_provind_le/ge` proofs reduce to an
eventual-`ε` bound (`hmesh`) before calling `affine_provind_theory_le_const`. The obstacle F19
names is not the obstacle.
-/

namespace Cleanroom.Corrigibility.CorrLiShutdown

open LogicalInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

/-- FAF's `ConsistentWithTheory` is consistency with every stage — the completed theory. -/
theorem probe_consistentWithTheory_unfold (v : PCWorld) (DP : DeductiveProcess) :
    v.ConsistentWithTheory DP ↔ ∀ n, v.ConsistentWith (DP.D n) :=
  Iff.rfl

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- Every completed-theory world of `paperDP T` values the package's current-day weight quote at
`w n` (FAF's `RationalQuoteCode.reflected`, which knows nothing about deferral). -/
theorem probe_currentWeight_reflected (w : ℕ → ℚ)
    (hw : PGenerableRat (liaHistory (paperDP T)) w) (hmem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (n : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt ((paperCurrentWeightQuoteCode T w hw hmem).luv n) (w n : ℝ) :=
  RationalQuoteCode.reflected (paperQuotationPresentation T) _ n v hv

/-- The mesh product of `X n` with the current-day weight quote is valued within `1/(n+1)` of
`x · w n` in every completed-theory world that values `X n` at `x` (FAF's
`meshProductLUV_valuesAt`). -/
theorem probe_meshProduct_current_near (w : ℕ → ℚ)
    (hw : PGenerableRat (liaHistory (paperDP T)) w) (hmem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (X : ℕ → LUV) (n : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T))
    {x : ℝ} (hx : v.ValuesAt (X n) x) :
    ∃ z, v.ValuesAt (meshProductLUV (paperCurrentWeightQuoteCode T w hw hmem) X n) z ∧
      |z - x * (w n : ℝ)| ≤ 1 / ((n : ℝ) + 1) :=
  meshProductLUV_valuesAt (paperQuotationPresentation T) _ X n v hv hx

end Cleanroom.Corrigibility.CorrLiShutdown

#print axioms Cleanroom.Corrigibility.CorrLiShutdown.probe_consistentWithTheory_unfold
#print axioms Cleanroom.Corrigibility.CorrLiShutdown.probe_currentWeight_reflected
#print axioms Cleanroom.Corrigibility.CorrLiShutdown.probe_meshProduct_current_near

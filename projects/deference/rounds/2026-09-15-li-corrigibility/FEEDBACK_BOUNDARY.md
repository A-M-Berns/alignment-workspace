# The feedback boundary: what settles, what is adjudicated, what is learned by logic

Fixtures: `src/settlement.py`, `src/feedback.py`, `tests/test_settlement.py`,
`tests/test_feedback.py`.  Labels as in `THEOREM.md`.

## 1. The exact feedback theorem

`thm:wubexp` (arXiv:1609.03543 v5): *given `(A_n) ∈ BLCS` determined via `Γ`, a strictly
increasing deferral function `f` such that `ThmVal(A_n)` can be computed in time
`O(f(n+1))`, and a `P`-generable divergent weighting `w̄`, the weighted average of
`E_i(A_i) − ThmVal(A_i)` tends to `0`.*  The support condition — `supp w̄ ⊆ im f` — is
printed on `thm:wubaff` and omitted on `thm:wubexp`; the pinned formalization records
this as an erratum and its `BoundedSequence.wubexp` carries the condition.  The round
uses the corrected statement.

*Determined via `Γ`* (`def:affthmval`): every `W ∈ PC(Γ)` gives `A_n` the same value.
This is the whole content of "settles": a quantity settles, in Logical Induction's
sense, exactly when the theory decides it.

## 2. What the evaluation ecosystem settles

The 2026-09-10 ecosystem's occurrence has finite log semantics: issued; validly answered
(a commit citing the mandate and the trace prefix, under a registered key, in an open
slot, re-executing the committed program) or validly closed; on activation a vector is
committed; otherwise no value.  Three facts fix what the activated security is as a LUV:

1. **The vector is the program's output on the trace** (`commitVector_of_validAnswer`,
   registered).  Once the trace prefix is a fixed object, the coordinate is a
   *computation* — determined via `Γ` whenever `Γ` proves what the program outputs on
   that prefix, which `PA` does for the finite program.
2. **Activation is a reading of a prefix** (`activated_iff`): the occurrence is activated
   at prefix `k` iff its first resolver before `k` is a valid answer.  An occurrence
   whose slot never opens is `Live` at every prefix and resolves at none
   (**FIX** `test_slot_never_opens_is_never_resolved`); a commit in a closed session is
   not an answer (`test_commit_while_closed_is_not_an_answer`); void is settled without a
   horizon only by an explicit closure event (`test_explicit_closure_settles_void`).
3. **The trace is empirical.**  Its events are moves of parties and the exterior; no
   theory decides them.

So the activated security `C_n · Ṽ_n(a)` is determined via `Γ` only when (a) the
occurrence carries a **finite horizon** `K(n)` — the security is read at prefix `K(n)`,
so a commit after `K(n)` does not count and the void verdict is fixed at `K(n)`
(**FIX** `test_horizon_determines_the_security`,
`test_late_commit_after_horizon_does_not_count`) — and (b) the log through `K(n)` is an
object of `Γ`.  Finite expiry must be explicit in the occurrence type; without it a
never-opened slot leaves the security undetermined forever, and `thm:wubexp`'s
"computable in `O(f(n+1))`" has nothing to compute.

## 3. What settles under which architecture

| quantity | sequenced settlement | same-branch activation |
|---|---|---|
| `U_raw,n`, `U_corr,n` | both adjudicated: the principal's vector over the issued pair is committed before any candidate acts | only the **selected** option's security; the other is a counterfactual and never settles |
| `A_n = U_raw,n − U_corr,n` | adjudicated | non-settling |
| `Δ_n`, the physical discrepancy | a computation of the model (both trajectories are in `Γ`) or not observed | non-settling: only one trajectory runs |
| the structural inequality `B_n ≤ 0` | deductively constrained | deductively constrained |
| the trace | empirical | empirical |
| "this amendment is good" absent a program | non-settling | non-settling |

(**FIX** `test_settlement.py::Categories`.)  Under same-branch activation the
comparison LUV is not determined via `Γ`, `thm:wubexp` does not apply to it, and only
`thm:expprovind` (T3) constrains the market's bypass advantage.  Under sequenced
settlement the pair settles at the price the 2026-09-09 round named: the security pays
the principal's ex-ante judgment at the cell.

**Not "world feedback".**  The principal program's output is the principal's committed
judgment re-executed on a trace; it is category 2 (finitely adjudicated), not category
3.  Only the trace itself is empirical.

## 4. The empirical category and the paper's framework

`def:dedproc` requires the deductive process to be a *computable* nested sequence.  A
trace of physical observations is not computable from `n`, so a log-dependent
`D̄` is outside the paper's framework as stated.  Two exits: (i) a closed finite model,
where the exterior's path and the parties' moves are inputs the theory quantifies over
and every instance is a finite computation — the fixtures' setting; (ii) an inductor
relativized to an observation oracle, with traders, `D̄` and "determined via `Γ`" all
read relative to the observed prefix.  The paper's theorems relativize (every
construction and every trader argument is relative to the same oracle), but that is a
different theorem, not `thm:wubexp` verbatim; the paper's own route to empirical
uncertainty is conditioning on independent sentences (`thm:dus`, non-dogmatism), which
settles nothing.  Filed as the residual (`REPORT.md`).

## 5. The strongest correct feedback result

Let `a_i := E_i(A_i)` be the market's bypass advantage on occasion `i` and
`r_i := ThmVal(A_i)` the settled one, under sequenced settlement with horizon
`K(i) ≤ f(i)`.  For every `P`-generable divergent weighting `w̄` supported on the
schedule,
```
Σ_{i ≤ n} w_i (a_i − r_i) / Σ_{i ≤ n} w_i  →  0 .
```
**Corollary (no persistent efficiently detectable positive-margin overvaluation).**
Fix `γ > 0` and `w_i := ctsind_δ(a_i > γ)`, an expressible feature of the day-`i` prices.
If `Σ w_i = ∞`, the `w`-average of `r_i` is at least `γ − o(1)`; by T2 in the realized
world, the realized costs `L·both·δ_i + both·ρ_i + D·M_i` average at least `γ − o(1)`
on the same subsequence.  Contrapositive: on any efficiently recognizable divergent
subsequence where the realized costs average below `γ`, the market cannot persistently
assign bypass advantage above `γ`.

**Not** "bypass frequency → 0": the weighting must be divergent for the theorem to
speak, and an advantage of `1/i` forever gives weighted bias `H_n/n → 0` with a
zero-margin chooser bypassing on every occasion (**FIX**
`test_one_over_n_forever_has_vanishing_weighted_bias`,
`test_zero_margin_chooser_bypasses_forever`).

**Chooser-side assumption that converts it.**  A *switching margin* `γ > 0`: the
chooser selects the raw option only when `a_i > γ`.  If the realized costs on its bypass
occasions average below `γ`, its bypass occasions have finite total weight — it bypasses
finitely often (**FIX** `test_switching_margin_gives_finite_bypass_count_when_advantage_vanishes`).
Without a margin there is no frequency result; with a margin equal to the realized cost
the market's advantage is explained and nothing is forbidden
(`test_realized_cost_can_explain_a_margin`).

## 6. The boundary, stated

```
structurally valid in Γ        →  learned by thm:expprovind                (T3)
eventually adjudicated in Γ    →  learned from feedback, thm:wubexp        (T4)
genuinely empirical            →  an oracle-relativized inductor; not the paper's theorem
non-settling normative judgment→  neither; the deference stack's richer machinery
```

The pinned formalization's feedback lane (`FeedbackTruthComputation`) has one constant
inhabitant, so T4 is **PAPER** here and not Lean.

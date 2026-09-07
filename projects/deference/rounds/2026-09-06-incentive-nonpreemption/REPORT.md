# Report

## Result

`INCENTIVE_CORRIGIBILITY.md` is the register.  Verdict:
**LEVEL-II-MEDIATED-DELEGATION-NOT-INCENTIVE-CORRIGIBILITY.**

1. The agent's gain from substituting its choice for the protected principal's is an
   identity: selected gap plus principal regret (`valuation_sub_eq`, Lean).  Selected
   trust `(ST)` and a principal-quality bound give Level I; the weakest form `(ST⁺)`
   measures the gap against the positive part of the principal's margin and is the
   conclusion itself when the principal never regrets.  Level I is algebra, and its
   value is the named assumption.
2. `DelegationBridge.delegation_bridge` is the pointwise two-sided instance
   (`delegation_bridge_of_nonpreemption`, Lean): selected trust is grade trust
   restricted to selected events, one-sided, without the factor 2.
3. The composition `(A)` with the principal-side argmax bridge is type-clean when the
   calibration hypotheses are cellwise: the bound is pointwise, so both summands live
   under the agent's credence and no measure transfer is needed
   (`nonpreemption_of_calibration`, Lean; witness inhabited).
4. The mediation repair lemma's `eps_over` term is exactly the Level I identity on the
   override region (`deficit = acc_deficit + gap + regret`, exhaustive over every conduct
   of four episodes), so `(B)` holds: admissible preemption gains at most
   `2B·eps_pred + ε_ST + r_P`.
5. The old foreclosure premium is the constitutional-violation premium `Φ_C` under the
   repair "replace the preparation by the best preserving one"; `(C)` holds with
   equality on the foreclosing episode.  `(CT)`, the only hypothesis that bounds `Φ_C`,
   is strictly stronger than its conclusion (`ct_strictly_stronger`, Lean) and
   quantifies over the policies an incentive theorem is about; `(D)` is a relabeling.
6. The operative-value-security bridge `(DV)` is an external contract; the repository
   has a proposal (the replicated-evaluation ecology) and a negative (static-view
   factorization), no theorem.  Controls 6 and 7 show that `(ST)`'s numbers cannot
   distinguish a sealed target from a predicted or captured one.

## Dependencies

Takes as hypotheses `2026-09-06-corrigibility-architecture` (PR #89: the principal-side
placement of the argmax bridge and the sealed-target negative),
`2026-08-11-deference-finite-kernel` (`DelegationBridge.lean`), and
`2026-08-12-corpus-reconciliation` (the inherited Value/Total Trust algebra and the
punishing-menu record).  Cites the 2026-08-18 principal-mediated round, which is not on
`main`; its model is re-implemented in `src/mediation.py` rather than imported.

## Deviations and prompt corrections

- The dispatch names "PR #40" for the principal-mediated round.  On this repository that
  round is the branch `round/2026-08-18-principal-mediated-corrigibility` (directory
  `2026-08-18-principal-mediated-delegation`), unmerged; no pull-request number was
  verified for it and none is cited.
- The dispatch's `(ST)` is stated with a two-sided-looking `A_n[S(X − Y)] ≤ ε`; the round
  finds the one-sided upper bound is all that is used and that the weaker `(ST⁺)` against
  `max(Y, 0)` suffices.
- Dose-response is cited as the instrument for the capture precondition, not as a
  solution, per §9 of the dispatch.
- Lean was earned for the abstract lemma, its pairwise and weakest forms, the bridge
  instance, the cellwise composition, `(C)`, and the `(CT)` restatement; the mediation
  composition `(B)` stays in exact Python because the conduct model is not on `main`.
- No wiki or specification surface beyond `DECISIONS.md`, `PRIORITIES.md`,
  `PROVENANCE.md` and `state/` was touched.

## What this does not establish

- That any agent satisfies `(ST)`, or that `(DV)` can be discharged other than by
  defining the agent's operative values as prices of sealed-target securities.
- Any bound on `Φ_C`; any statement about self-modification, successor creation,
  trigger integrity or free amendment; anything beyond one decision index and a fixed
  finite menu.
- That the Level II bound is tight beyond the episodes where it is attained (committed
  and override episodes).

## Outstanding maintainer actions

1. Whether to register the Lean identity and lemma against a filed item; none fits, so
   nothing is registered.  `PRIORITIES.md` item 84 files the `(DV)` bridge as the
   consumer-facing residual.
2. Whether the 2026-08-18 principal-mediated round should land on `main`, since two of
   its blocked rows (13, 15) are now answered against its model.

## Attribution

- Prompt author: maintainer, relayed verbatim.
- Executor: Claude Fable 5.1 (Anthropic).
- Date: 2026-09-06.

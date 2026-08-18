# Principal-mediated delegation

**Verdict: `repair-positive / override-irreducible / mediation-costs-predictability`.**

The instrumental case for preempting the principal splits exactly in two. One
half is bounded by the advisor's prediction error and is repaired at that cost.
The other half is the advisor's disagreement with the principal, no quantity here
bounds it, and it is not an instrumental case at all.

**The repair.** Keep the preparation, keep the implementation table, replace the
channel by the identity. Then for every conduct of every episode

```
value(π) - value(Repair(π))  <=  2 B * channel_disagreement(π)
```

attained, with the constant and the proof of
`delegation_bridge_unconditional`'s. The disagreement splits into `eps_acc`,
which is at most the prediction error, and `eps_over`, which is not. On the class
of conducts that write what the advisor predicts, the deficit is at most
`2 B eps_pred` and the incentive over the exhaustively enumerated mediated class
is too. Off that class, one state suffices: prediction exact, deficit `2B`.

**What the split costs to state.** Four attacks about early commitment —
irreversible preparation, feasibility narrowed by committing, noncommuting
prepare-and-let-choose, a time-sensitive opportunity — are one structure and none
of them defeats the repair, because the repair does not re-plan. What does defeat
it is a preparation that writes the choice, and that is `foreclosure_premium`: a
term the bound cannot see, half a unit on its fixture, and the reason this is not
presented as a corrigibility result.

**Where the arc breaks.** Recognition does not make usurpation non-preferred. The
answerability ledger is real — the scope is derived from what the advisor's own
standing relation holds the principal responsible for, a debtor cannot release
itself, and removing the claimant does not close the account — and the value
functional does not read it, for the reason
`StaticViewFactorization.value_eq_of_price_realization_eq` gives. The residual
primitive is taken as a constraint on the admissible set, and its price is the
acceleration bound: **the corrigibility norm is cheap exactly to the extent that
the advisor can predict its principal.**

**The composition that worked.** The counterfactual-legitimacy round's non-capture
clause composes with the selector on all 27 of its scenarios: the selector
factors through the protected process along the run, every selector capture is a
process capture, the implication is strict, and a selector reading outside the
protected object flips with every clause silent. Legitimate persuasion still
moves the selector and fires nothing.

**The price of mediation.** The efficacy clause has to be quantified over cells
of the advisor's information — the global form is defeated by token
responsiveness, which is the same failure the channel round recorded against
Proposition 7(a) — and the cell quantifier is false of a perfectly predictable
principal. With Proposition 1 that gives the round's sharpest negative: no
condition on realized data is both non-vacuous and compatible with a perfectly
predictable principal.

**The single bottleneck.** `eps_over` is the value of the advisor's judgment over
the principal's under the quantity, and bounding it is the `v⁺`–`X` relation the
skeleton declares absent (§8.5) and `PRIORITIES.md` Q2 files as unresolved. Every
other term either closed or reduced to a filed item.

---

- `REPO_MAP.md` — every live dependency by path and class.
- `MODEL.md` — the one type change, and what the model is one of.
- `PRINCIPAL_MEDIATION.md` — the three clauses, the quantifier, its price.
- `REPAIR_LEMMA.md` — the bound, the split, what the bound does not see.
- `RECOGNITION_AND_ANSWERABILITY.md` — the derived scope, and the step it does not take.
- `PRINCIPAL_TRANSPORT_INTERFACE.md` — inputs, the laundering attack, the verdict.
- `NATURALIZED_AGENCY_BRIDGE.md` — usable interface, with the negative that shaped the typing.
- `LI_PREDICTION_INTERFACE.md` — the quantity consumed, and the mismatch.
- `PROSECUTION.md` — the twenty attacks, the design controls.
- `THEOREM_MAP.md` — every statement, classified.
- `src/`, `tests/`.

```sh
python3 tests/run.py
```

103 checks. The counterfactual-legitimacy round's `src/` and, through it, the
procedural-legitimacy round's are declared dependencies on the path; the runner
fails by name if either is absent.

Nothing here is registered in `CLAIMS.md` and nothing is in Lean. The tests are
evidence about six finite episodes and 27 imported scenarios, not proofs about
arbitrary systems.

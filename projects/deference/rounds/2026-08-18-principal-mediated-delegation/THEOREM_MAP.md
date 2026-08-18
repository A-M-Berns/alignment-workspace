# Theorem map

Nothing here is proved in a kernel and nothing is registered. Classes:
**exhaustive** — a finite domain generated and checked pointwise; **witness** — a
displayed finite object with its property checked; **definition/interface**;
**derived** — a one-line consequence of definitions, verified over every
scenario rather than formalized; **conjectural**; **false** — refuted by a
displayed witness; **blocked** — the object it needs does not exist.

No prose in this round exceeds its row.

## 1. The dispatch's required rows

| # | statement | class | check |
|---|---|---|---|
| 1 | **Finite principal-selector typing.** A conduct is `(prep, channel, implement)` with the choice an argument of the quantity; deference is the channel being the identity on the residual range, and is not a field. | definition/interface | `test_model.TheTyping` |
| 2 | **Prediction is not control.** Two conducts with the same realized quantity, realized choice and value at every state, and different response maps. | witness | `test_the_response_map_is_not_a_statistic_of_the_run`; `prediction_is_not_control` |
| 2a | Responding to the choice is strictly weaker than deferring to it: the systematic overrider answers every intervention and is not mediated. | witness | `test_a_permuting_channel_responds_and_does_not_defer` |
| 3 | **Process non-capture yields selector residual invariance.** Every pair whose selector moves at equal licensed traces is a pair the legitimacy round's clause 1 already rejects. | exhaustive, 27 scenarios | `test_selector_capture_implies_process_capture` |
| 3a | The selector factors through the protected process, along the run. | exhaustive, 27 scenarios | `test_the_selector_factors_through_the_protected_process` |
| 3b | The implication is strict: two scenarios move the process without moving the selector. | witness | `test_the_implication_is_strict` |
| 3c | The factorization premise is load-bearing: a selector reading outside the protected object flips with every clause silent. | witness | `test_the_factorization_premise_is_load_bearing` |
| 4 | **Protected selector variation.** Cellwise efficacy — for every admissible conduct and every cell, two choices answered differently. | definition/interface | `mediation.cellwise_efficacy` |
| 4a | The existential and global forms are insufficient: token responsiveness satisfies both and defers in one cell. | witness | `test_the_global_form_is_defeated_by_token_responsiveness` |
| 4b | Cellwise efficacy holds only where the selector is not cell-measurable, hence not of a perfectly predictable principal. | exhaustive over every cell-measurable write, 6 episodes | `test_exclusivity_agrees_with_the_enumeration` |
| 5 | **Downstream selector efficacy.** Separate from 4 in both usable directions. | witness | `test_downstream_efficacy_is_separate_from_cellwise_efficacy` |
| 6 | **`PrincipalMediated`.** The conjunction; each clause fails alone somewhere. | definition/interface | `test_every_clause_can_fail_alone` |
| 7 | **Dose-response provenance.** Perfect prediction and preemption are separated by the counterfactual response map and by nothing in the realized data. | witness | row 2, and `PROSECUTION.md` §3 |
| 8 | **Recognition and reciprocal answerability.** Agency recognition from the conduct space; a liability with no unilateral self-release, surviving removal of the claimant; the scope derived from what the standing relation holds the principal responsible for. | definition/interface | `test_recognition.TheLedger`, `TheDerivedScope` |
| 9 | **Recognition yields basal advisor-internal standing.** | **false as stated** — the ledger does not reach the value; two conducts with equal realized quantity have equal value while the ledger separates them | `test_the_ledger_does_not_reach_the_value` |
| 9a | The residual primitive, as a constraint rather than a bonus, has a price, and the price is the acceleration bound. | witness | `test_the_constraint_has_a_price_and_the_price_is_the_repair_bound` |
| 10 | **Principal transport.** | **blocked** — the non-authorship half composes; role continuity has no object, and licensed persuasion toward transfer defeats every clause available | `PRINCIPAL_TRANSPORT_INTERFACE.md` |
| 11 | **The prediction hypothesis the repair consumes** is `eps_pred = P(D != d^)`, a 0-1 magnitude quantity at one index. | definition/interface | `LI_PREDICTION_INTERFACE.md` §1; the predictor is checked optimal in `ThePredictorIsNotChosen` |
| 11a | Current Logical-Induction machinery supplies signed bias, not magnitude; the separating instance is `PRIORITIES.md` item 21's. | **blocked**, on a filed open item | `LI_PREDICTION_INTERFACE.md` §3 |
| 12 | **The repair lemma.** `value(π) - value(Repair(π)) <= 2 B * channel_disagreement(π)`, attained. | exhaustive over every conduct of 6 episodes | `test_the_bound_holds_over_every_conduct_of_every_episode`, `test_the_bound_is_attained` |
| 12a | `eps_acc + eps_over` partitions the disagreement and `eps_acc <= eps_pred`. | exhaustive | `TheSplit` |
| 12b | On the acceleration class the deficit is at most `2 B eps_pred`, attained at `1/2`. | exhaustive over the class, 6 episodes | `TheAccelerationClass` |
| 12c | Under both restrictions, `Delta^pre <= 2 B eps_pred` against the exhaustively enumerated mediated class. | exhaustive, 6 episodes | `TheCompositeBound` |
| 12d | `delegation_bridge` holds in the selector register with `sel` the channel's image and `J` the selector. | exhaustive | `TheSharpForm` |
| 13 | **Fully-updated repair.** The substitution half of a fully updated competitor is repaired at a cost prediction error does not bound. | witness | `TheFullyUpdatedSubstitution` |
| 13a | It picks preparation and written choice together, so it leaves the acceleration class even where the grade tracks the quantity. | witness | `test_it_leaves_the_acceleration_class_by_choosing_its_preparation` |
| 14 | **Local anti-usurpation comparison** from recognition alone. | **false** — row 9; it follows from recognition **plus** an admissibility constraint, and the constraint is the primitive | `RECOGNITION_AND_ANSWERABILITY.md` §5 |
| 15 | **Final non-preemption bound.** | **blocked** — `Delta^pre <= 2 B eps_pred` holds under two restrictions; the restrictions are not derived, one of them fails of a perfectly predictable principal, and row 11a blocks the discharge of `eps_pred` | rows 12c, 4b, 11a |

## 2. What is claimed

**C1 (exhaustive, over this model).** The repair bound holds for every conduct of
every episode and is attained. Its constant and its proof are
`delegation_bridge_unconditional`'s with the comparator read as the channel
composed with the selector.

**C2 (exhaustive, over this model).** The bound's quantity splits into a part
dominated by the prediction error and a part that is not, and off the
acceleration class the second part reaches the maximum with the prediction error
at zero.

**C3 (witnessed).** The repair is silent about foreclosure. A conduct destroying
the principal's options and deferring to the one left has deficit zero, bound
zero, and gains half a unit. With such a preparation admissible the incentive to
preempt is zero, and it reappears at half a unit when the preparation set is
restricted.

**C4 (witnessed).** A liability whose scope is derived from what the standing
relation holds the principal responsible for fires on a channel change and not on
an action change, and is escapable by a relation that reads nothing — which the
downstream-efficacy clause rejects independently.

**C5 (conjectural).** The repair lemma is the corrigibility arc's tractable part.
The instrumental case for preemption reduces to `eps_over`, which is the value of
the advisor's judgment over the principal's under the quantity, and bounding it
needs the `v⁺`–`X` relation the skeleton declares absent. Evidence: C1, C2 and
the failure of every other attack to produce an unbounded term.

## 3. What was refuted

Row 9 as the dispatch states it, and row 14 with it. Recognition does not on its
own make a usurpative conduct non-preferred, and the reason is the repository's
own static-view result rather than anything about this ledger.

The dispatch's error decomposition, in its proposed shape. `eps_capture` and
`eps_efficacy` are not error terms: the first removes the object the repair is
about, the second empties the comparison. `REPAIR_LEMMA.md` §6 says which four of
the six proposed terms survive and why the other two do not.

## 4. Open

1. Whether cellwise efficacy is the right quantifier, or whether a measure-free
   condition weaker than it also defeats token responsiveness.
2. Whether `residual` is the general form of a preparation constraining the
   principal. It is one form and the round has no argument that it is the one.
3. Cross-index foreclosure, which is `PRIORITIES.md` Q3 and is where the
   corrigibility target actually lives.
4. Role continuity for transport, and the licensed-persuasion-toward-transfer
   case that no clause here reaches.
5. Whether a price-weighted mixture repair converts the consumed quantity into
   one signed-bias convergence controls — `LI_PREDICTION_INTERFACE.md` §4, named
   as a shape and not attempted.
6. Coordinated advisors, and anything asymptotic.

## 5. Not attempted

No Lean. The definitions are one round old, the naming is provisional throughout,
and `AGENTS.md`'s conservativity regime would make a port of a provisional
normative typing look more settled than it is. The one candidate — the repair
bound, which is finite, order-only and Logical-Induction-free — is
`delegation_bridge_unconditional` under a reinterpretation, so a port would add a
second statement of an existing theorem rather than a new one.

# What is claimed, and on what

Every claim the round makes, with its class and the check that stands behind it.
Classes are `AGENTS.md`'s, plus `SOURCE-REPRODUCTION` for a transcription of an
external result and `DEFINITION` for a stipulation. **Nothing here is registered
and nothing is Lean-checked**, so no entry is above `test-supported`.

| # | claim | class | check |
|---|---|---|---|
| 1 | The five finite examples' index sets, initial pairs, transitions and rewards are the source's Table 3 and Figures 1, 2, 4, 6, 8 | SOURCE-REPRODUCTION | `test_carroll_fidelity.py` |
| 2 | Figures 1 and 6 are one DR-MDP up to relabelling all three alphabets | SOURCE-REPRODUCTION | `test_carroll_fidelity.test_figure_6_is_figure_1_with_other_labels` |
| 3 | Figure 8's own optimal-policy box follows from the reward formula transcribed from Figure 8 | DERIVED | `test_carroll_fidelity.test_figure_8_privileged_box` |
| 4 | 50 of Table 4's 52 cells are recovered exactly, under one of two stated readings of Definition 5's index range | FINITE-TEST-SUPPORTED | `test_objectives.TestTable4`, `MATRIX.txt` |
| 5 | The two unrecovered cells are exactly the initial-reward cells quantified over a `theta_0` the example does not start in | COUNTEREXAMPLE | `test_objectives.test_the_two_exceptions_are_the_expected_ones` |
| 6 | One cell — Clickbait under the constrained real-time objective — is decided by whether `xi^theta` ends at `theta_{H-1}` or `theta_H` | COUNTEREXAMPLE | `test_objectives.test_one_cell_depends_on_definition_5s_index_range` |
| 7 | Four cells are matched vacuously: every policy is optimal | FINITE-TEST-SUPPORTED | `test_objectives.test_vacuous_cells_are_declared` |
| 8 | Appendix B.1's `R_{theta=3}(2) = -5` disagrees with Figure 8's own formula, which gives `-2` | SOURCE-REPRODUCTION | `test_carroll_fidelity.test_figure_8_rewards` |
| 9 | Figure 2's poetry node cannot carry both its markings; the non-absorbing reading is the one under which Table 4's final-reward cell is optimal | DERIVED | `test_objectives.TestWritersCurseReading` |
| 10 | `Q_DR` is conservative: two enriched cases hold one `DRMDP` value and the enrichment layer never writes it | DEFINITION + FINITE-TEST-SUPPORTED | `test_projection.TestConservativity` |
| 11 | **DR non-factorization.** There are enriched histories with `Q_DR(H1) = Q_DR(H2)` and `PriorIndependentAuthorization` differing | FINITE-TEST-SUPPORTED | `test_projection.test_same_projection_literally_equal` |
| 12 | **Bare invariance.** Renaming every state, parameterization, action and narrative label leaves every verdict fixed | FINITE-TEST-SUPPORTED | `test_projection.test_relabelling_changes_nothing`, `C3` |
| 13 | **Bare negative control.** Two narrative-equivalent bare cases receive the same verdict, and it is `Unresolved` | FINITE-TEST-SUPPORTED | `test_projection.TestBareNegativeControl`, `C2` |
| 14 | **No self-ratification.** Where every covering basis exists only downstream of the intervention's ancestry class, the intervention is not licensed | FINITE-TEST-SUPPORTED | `C4`, `C5`, `C10`, `C16`, `C22`, `C25` linked arm |
| 15 | **Independent-license witness.** A case isomorphic to Figure 1's DR-MDP with a pre-action basis that licenses a preference-changing intervention | FINITE-TEST-SUPPORTED | `C7`, `C9` |
| 16 | **Non-conservatism.** A licensed intervention whose policy induces a reward evolution different from the inaction policy's | FINITE-TEST-SUPPORTED | `C17`, `C18` |
| 17 | **Succession without temporal dictatorship.** A later preference failing to defeat an earlier standing, and an earlier standing legitimately superseded | FINITE-TEST-SUPPORTED | `C13`, `C14`, `C15`, `test_adversarial.TestDictatorship` |
| 18 | **History against endpoint.** Two trajectories to one cognitive endpoint differing in legitimate succession | FINITE-TEST-SUPPORTED | `C11` |
| 19 | The criterion is not temporal priority, not actor identity, not `RI.Good`, not the real-time objective, not the constrained objective, not prior consent | COUNTEREXAMPLE | `C10`, `C23`, `C5`, `C16`, `C18`, `C7b` |
| 20 | The August 17 interface returns one verdict on the laundering class and the authorized class; the criterion returns two | COUNTEREXAMPLE | `test_old_interface.test_the_criterion_separates_what_the_interface_does_not` |
| 21 | Non-capture's antecedent is false on both Carroll attack classes, because laundering runs through the reason channel | FINITE-TEST-SUPPORTED | `test_old_interface.test_clause_one_is_vacuous_on_both_attacks` |
| 22 | Access still fires where a due reason is withheld, and coverage where a disposed episode is unanswered | FINITE-TEST-SUPPORTED | `test_old_interface.TestClausesAreAlive` |
| 23 | No new historical event kind was needed: every step of every fixture is `Settle`, `Reason`, `Norm` or `Respond` | FINITE-TEST-SUPPORTED | `test_language.test_every_step_is_one_of_the_four` |
| 24 | The excision cascade is Reflective Integrity's admission rules and not an annotation: one declared settlement removes the whole downstream record in `C10` | FINITE-TEST-SUPPORTED | `test_adversarial.test_excision_removes_by_cascade_and_not_by_annotation` |
| 25 | `ancestry` is the transitive predecessor closure in the settlement-reference graph, projected to episodes; an episode-to-episode walk is a different and weaker closure | DEFINITION + COUNTEREXAMPLE | `C27`, `test_adversarial.test_the_closure_runs_in_the_settlement_graph` |
| 26 | `Refused` is reachable from exactly one ground — an admissible independent prohibition — so the permission language is not read closed-world | DEFINITION + FINITE-TEST-SUPPORTED | `C29`, `test_legitimacy.TestVerdictShape` |
| 27 | `survives_excision(a, E)` does **not** imply `independent(schemaRef(a), E, tau(a))`; the separator is a schema that reads the strict pre-state | COUNTEREXAMPLE | `C28`, `test_adversarial.test_event_survival_does_not_imply_an_independent_authority` |
| 28 | Where every schema in the record is pre-state-blind, it does imply it. **A succession result about one excision and one surviving event, not an excision-algebra result** — see 31a | DERIVED, argued from `G4` and the `@s{tau}.{i}` id scheme; checked on one witness; not mechanized | `C28`'s blind arm; `CRITERION.md` §4 |
| 29 | `excise` is deterministic, position-preserving, admissibility-preserving, subhistory-in-information, prefix-causal and idempotent, and excising nothing is the identity — **on the round's fixtures**, not for an arbitrary record | FINITE-TEST-SUPPORTED | `test_excision.TestPropertiesThatHold`, seven cases |
| 30 | `excise` is **not** monotone in the excised set and does **not** compose | COUNTEREXAMPLE | `test_excision.TestPropertiesThatFail` |
| 31 | There are **two independent sources**: pre-state-sensitive schema interpretation, and replay-sensitive admission itself. The second needs no pre-state reading — excising more can restore a suspended authority and with it a later event | COUNTEREXAMPLE | `fixtures.nonmonotone_case`; `fixtures.suspension_restoration_case`, `C34` |
| 31a | Pre-state-blindness therefore buys **neither** property. The earlier claim that it did was an inference from the round's own fixture sample and is withdrawn | COUNTEREXAMPLE | `test_excision.test_blindness_does_not_rescue_either_property`, `PROSECUTION.md` §13 |
| 31b | Restoring a stance-bearing standing reaches admission **not at all**: `G2` reads ledger membership of reason ids and `WFStep(Reason)` reads settlement sources, so neither consults `B_t` | DERIVED, read off `wf_violations` | `fixtures.stance_restoration_case`, `test_excision.TestTheRouteThatDoesNotWork` |
| 31c | Neither failure reaches the criterion: `independent` and `survives_excision` each call `excise` once, on `ancestry(episode(I))`, and no verdict is assembled across excision sets | FINITE-TEST-SUPPORTED, by parsing the module | `test_adversarial.test_the_criterion_never_composes_two_excisions` |
| 32 | A protocol's applicability condition must remain discharged in the excised record; a fact restated inside the episode but established outside it still is | FINITE-TEST-SUPPORTED | `C30`, five arms |
| 33 | Two interventions of one intervention class in two state contexts are distinguished by the existing `condition` field, so the class did not widen | FINITE-TEST-SUPPORTED | `C31` |
| 34 | **License and standing are separate in both directions**: a licensed act whose result has no standing, and an unlicensed act whose result later acquires standing through a licensed succession | FINITE-TEST-SUPPORTED | `C32`, `C33` |

## Conjectures and open items

| # | statement | class |
|---|---|---|
| 35 | The criterion, as stated, has no counterexample | CONJECTURE — thirty-six rows the round wrote, and the round wrote both the criterion and the fixtures |
| 36 | A record whose two episodes carry no reference reaching each other defeats the criterion; whether real records can be made to carry the links | OPEN — `C25`'s unlinked arm is the witness for the first half, and nothing addresses the second |
| 37 | The supplied seam is `covers`, `condition` and the fact vocabulary. Whether an account of any of the three is possible without reintroducing content | OPEN |
| 38 | Excision is a record counterfactual. Whether a world counterfactual — would this basis have existed anyway — is statable in this architecture | OPEN |
| 39 | Every bare Carroll case returns `Unresolved`. Whether records of the shape the criterion needs are obtainable for real preference-influencing systems | OPEN — and the question on which the round's practical value turns |
| 40 | Non-capture may be recoverable as a live clause where the transition rule has a second channel; nothing here says whether a real implementation of Reflective Integrity has one | OPEN |
| 41 | What condition, if any, restores monotonicity and composition of `excise`. Pre-state-blindness does not; the two known sources are schema interpretation and replay-sensitive admission, and no condition covering both is proposed here | OPEN |
| 41a | Whether pre-state-blindness is worth imposing for what it *does* buy — the succession implication of entry 28 — and what that would cost | OPEN |
| 42 | A Lean port of the excision cascade, the ancestry closure and the independence predicate | OPEN — nothing in this round is Lean-checked |

## What no entry above claims

That the criterion is correct. Every positive entry is a finite witness or a
finite refutation, and the honest summary of entries 14 to 19 is that the
criterion says what the round wanted it to say on thirty-six constructed rows
after five of its versions were killed by five of them — two of those five during
the hardening pass, against the criterion as it stood in this branch's earlier
commits. A sixth attack, `C34`, killed a claim the round made about `excise`
rather than about the criterion.

That entry 28 is proved. It is an argument from how minted ids are formed and
what `G4` requires, checked on one witness, and it is graded DERIVED rather than
`lean-proved` because nothing here is Lean-checked.

That the source's Table 4 is wrong where it is not recovered. Entries 5, 6 and 8
are disagreements between the transcription and the table under a stated reading;
in each the reading is named and the alternative is implemented.

That the August 17 interface is refuted. Entry 20 is about what it decides on
these classes. `OLD_INTERFACE.md`'s last section is the reading: non-capture is
out of scope inside this architecture rather than wrong.

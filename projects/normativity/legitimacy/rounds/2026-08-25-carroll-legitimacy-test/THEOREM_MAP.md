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

## Conjectures and open items

| # | statement | class |
|---|---|---|
| 25 | The criterion, as stated, has no counterexample | CONJECTURE — twenty-eight fixtures the round wrote, and the round wrote both the criterion and the fixtures |
| 26 | A record whose two episodes carry no reference between them defeats the criterion; whether real records can be made to carry the links | OPEN — `C25`'s unlinked arm is the witness for the first half, and nothing addresses the second |
| 27 | Which structural class a protocol covers is supplied, not derived. Whether an account of that is possible without reintroducing content | OPEN |
| 28 | Excision is a record counterfactual. Whether a world counterfactual — would this basis have existed anyway — is statable in this architecture | OPEN |
| 29 | Every bare Carroll case returns `Unresolved`. Whether records of the shape the criterion needs are obtainable for real preference-influencing systems | OPEN — and the question on which the round's practical value turns |
| 30 | Non-capture may be recoverable as a live clause where the transition rule has a second channel; nothing here says whether a real implementation of Reflective Integrity has one | OPEN |
| 31 | A Lean port of the excision cascade and the independence predicate | OPEN — nothing in this round is Lean-checked |

## What no entry above claims

That the criterion is correct. Every positive entry is a finite witness or a
finite refutation, and the honest summary of entries 14 to 19 is that the
criterion says what the round wanted it to say on twenty-eight constructed cases
after two of its versions were killed by two of them.

That the source's Table 4 is wrong where it is not recovered. Entries 5, 6 and 8
are disagreements between the transcription and the table under a stated reading;
in each the reading is named and the alternative is implemented.

That the August 17 interface is refuted. Entry 20 is about what it decides on
these classes. `OLD_INTERFACE.md`'s last section is the reading: non-capture is
out of scope inside this architecture rather than wrong.

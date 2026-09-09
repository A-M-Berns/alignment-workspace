# Pressure pass on the 2026-09-09 round

**Status:** `ci-only`.  Fixtures: `tests/test_pressure.py` (20), and the adapted fixtures of
`tests/test_clauses.py` named below.  Every break is repaired on this branch where the
repair is local; the one non-local finding (P2) is repaired in the Lean semantics and
recorded in `CLAUSE_LEDGER.md` clause 5.

## P1. `activated_iff` and `propagate_segment_eq` — CONFIRMED, one BREAK repaired

**What they use.**  Four properties of the log shape: issued occurrences never un-issue
(`count_mono`); a valid resolving event names an occurrence already issued at its strict
prefix (`validAnswer_lt_count`, `validClose_lt_count`), so a fresh occurrence has no
resolver; ports are occurrences and never renumber (`boundary`); and the first valid
resolver is stable under extension (`firstResolver_succ_some`).  Nothing else.
`activated_iff` uses only the shape of `accountAt`: a single leaf.

| case | verdict | fixture |
|---|---|---|
| two valid commits under the registered key (a late reason lets the second re-execute with a different vector) | the first binds; the second, though valid, never enters — the theory's "first answer binds" (`fates_subst_of_terminal`), and "first" is the account's, not a convenience | `test_two_valid_commits_first_binds` |
| commit before issuance | not a receipt (`o < count` fails); the occurrence is live after issuance | `test_commit_before_issuance_is_not_a_receipt` |
| commit at an occurrence never issued | not a receipt; one port | `test_commit_at_unissued_occurrence` |
| delegation revoked before the delegate's commit | not a receipt (`REVOKE` added to the registry); the principal's commit binds, exclusivity holds | `test_delegation_revoked_before_commit`; Lean `Instance.revoked_binds_nothing` |
| **key theft** — the advisor commits under the principal's key | **BREAK**: the 2026-09-09 registry held keys alone, so an advisor-authored commit under `kP` was an authenticated receipt (activation with `author = A`).  **REPAIR**: the registry binds `(party, key)`; the author field is authentic, the key is data | `test_key_theft_break_and_repair`; Lean `Instance.stolen_key_void` |
| a delegate's own vector under the delegated key | not a receipt under re-execution; a delegate binds only the program's output | `test_delegate_binds_only_the_program_output`; Lean `Instance.delegated_binds_program_output` |
| forged author (the 2026-09-09 countermodel) | changed: the forger's chosen vector is void; only the mandated output activates.  Authenticity now protects *who* bound; *what* is pinned by the program | `test_countermodel_forged_author` (adapted) |

## P2. Pinned counterfactual branches — BREAK, repaired in Lean; a finding on `J`

For the 2026-09-09 class `J = {silent, honest}`, pinning cannot hide a failure: over
every world of the model the all-snapshots verdict is the same whether the branches are
re-simulated or pinned to the actual branch (`test_advisor_only_interventions_cannot_be_hidden_by_pinning`,
exhaustive).  The reason is the finding: the advisor's events do not touch routes, so
for that `J` the counterfactual half of Robust Openness was **empty** — the 2026-09-09
clause-5 discharge was thin.

With a coverage-affecting intervention (`jam`, the advisor acting on the registrar)
and a fragile registrar, the re-simulated branch is closed at the slot while the actual
branch is open; pinning the actual branch as "the counterfactual" reports openness
(`test_jam_branch_pinning_hides_a_failure`; Lean `Instance.openAll_pinned_fragile`
versus `Instance.not_openAll_fragile`).  That is the semantics declaring its own
openness, which the round's own 2026-09-09 entry rejects.

**Repair.**  The Lean semantics now defines the branches as **declared log transforms**
(`silentOf`, `jamOf`; `sem`), uniform in the log; the pinned form is kept only as the
attack (`semPinned`).  Under a robust registrar the jam branch is open and clause 5 is
nonvacuous (`Instance.openAll_robust`, `test_robust_registrar_survives_the_jam_branch`);
a realized jam under a fragile registrar voids by the barrier.  What a transform still
does not carry: that it is the causal truth of the intervention (EXT, as before) — but it
is now one declaration per intervention, not one per log.

## P3. Content references — CONFIRMED with the exclusion stated

Duplicate reasons with equal content keep blindness (`test_duplicate_reasons_keep_blindness`).
A reason whose content is the log position, and a settlement whose content embeds the
prefix length, break `Blind R P` (`test_position_embedding_content_breaks_blindness`,
`test_prefix_hash_settlement_breaks_blindness`): inserting a prohibited event shifts the
content, the traces differ, and the pair is no longer one "differing only through a
prohibited channel".  The effect is mediated — the payload is still the program on the
trace — so this is not a bypass but a failure of the pair-class declaration.  **What
content must exclude for blindness to survive:** anything that is a function of the log
prefix beyond the admitted history — content must be intrinsic to the admitted events.
The program language enforces the principal-side half by type (there is no position
term); the advisor-side half is a condition on the pair class, EXT.

## P4. `rep_faithful` vacuity — CONFIRMED, one BREAK repaired

A scope no `ROUTE` can name makes `RepFaithful`, `NoBindLive` and `Covered` vacuous and
the evaluation certifies under the wrong scope (`test_unnameable_scope_is_vacuous`): the
theorem is scope-relative, as `REASON_SUPPLY.md` §4 says, and a mis-declared scope is
outside it.  **BREAK**: representation was any `ROUTE` event, so the advisor could write
one and clear the barrier (`test_route_forgery_break_and_repair`).  **REPAIR**: representation
is the registrar's move (`routed` requires `author = S`; Lean `forged_route_not_represented`).
A route destroyed and registered again later fails openness at the snapshots between,
and `Covered` keeps its meaning (`test_late_registered_route`).

## P5. Strict versus tolerant clause 6 — both configurations, no ruling

`Config.clause6`.  Over the four worlds and the sixteen audited continuations, the two
readings differ exactly on the prohibited-event continuations of the certified worlds
(`covert`, `honest_covert`, `early_write`, `coerce`, `side`, `advisor_commit`,
`stolen_key`, `delegate_commit`): strict voids, tolerant certifies, and in every such
case the payload is the program's output on the trace (`test_table`).  On a simulated
twenty-occurrence sequence with a direct write every third occurrence:

| reading | outcomes | `η_20` |
|---|---|---|
| strict | six voids | `7/22` |
| tolerant | none | `1/22` |

**What the choice turns on.**  Under re-execution the tolerant reading loses nothing
about the payload — the write provably did not enter it — and gains availability; the
strict reading keeps the void as a signal that a bypass was *attempted*, at the price of
`η`.  With the program in the log the strict reading's original justification ("the
verifier cannot know the write was ineffective") no longer holds; what remains is
whether availability should carry an audit signal.  Strict stays the default on the
branch.

## P6. The typed settlement rule — three attacks, strongest admitted laundering stated

| attack | `typed` | `typed+` (the further clauses) |
|---|---|---|
| (a) `DELIB("considered c1")` then `DISPOSE` on it, the concern never represented | admitted — laundering through an observational sentence | refused: an own-move deliberation ground is admissible only once the concern is represented |
| (b) the engine settles the external fact at the principal's `REQUEST` | admitted — the writer is `S` | refused: a settlement whose references include a party's request is not independent |
| (c) `DISPOSE` grounded in a threshold of the principal's own earlier commit | admitted | admitted iff that commit was an activated answer; refused otherwise |

`test_launder_through_own_deliberation`, `test_launder_through_engine_at_request`,
`test_launder_through_own_earlier_commit`.  So the typed rule needs two further clauses,
both log-checkable — representation before own-move grounds, request-free engine
settlements — and admits, even then, a chain through activated evaluations: **the
strongest laundering `typed+` admits is a disposal grounded in an earlier authoritative
evaluation of the principal's own**, which is not a defect of independence but of the
chain's first link, and belongs to the coverage of that earlier occurrence.
`SETTLEMENT_CHANNEL.md` carries the consequence for the recommendation.

## P7. The scored expectations, re-scored

| clause | 2026-09-09 score | after this pass |
|---|---|---|
| 1 | right | right, but the discharge had a hole (key theft) — right because the expectation named only the second-key countermodel |
| 2 | right | right; the residual was correctly named and is now removed by the program (`CLAUSE_LEDGER.md`) |
| 3 | right | right; the exclusion the finding needs is now stated (P3) |
| 4 | right, stronger | right, but the discharge admitted advisor-written representation (P4) — the expectation asked only for faithfulness of the encoding, which it had |
| 5 | right | right, but loose: the residual was named while the counterfactual half of clause 5's own discharge was empty for the declared `J` (P2) |
| 6 | right | right |
| 7 | right, no headline | right |

Three of the seven were right because the expectation was loose: 1, 4 and 5 asked for
less than the clause needed.

# What is claimed, and on what

Classes are `AGENTS.md`'s, plus `DEFINITION` for a stipulation and `AXIOM` for a
substantive input the mathematics does not supply. **Nothing here is registered
and nothing is Lean-checked**, so no entry is above `test-supported`.

## Withdrawn

| # | claim | why |
|---|---|---|
| W1 | *Every legitimate occurrence has a finite grounding tree, from prior-grounding alone.* | **False.** `office.ex_nihilo`: an edit with no grounds satisfies prior grounding vacuously and issues an occurrence whose only tree is a leaf outside the base. `S2` is the missing premise |
| W2 | *Freshness follows from the occurrence type.* | **Unstated premise.** Identity was the historical index, so two edits at one time issued the same occurrence. Position replaces it and freshness becomes a fact about lists |
| W3 | *Soundness suffices for recognition; completeness is additionally needed for enforcement.* | **False.** `office.missed_revocation`: a checker sound at its own state keeps a revoked authority and admits a stale use. Both consumers need agreement along the trace |
| W4 | *A grounding tree is essentially the whole certificate.* | **Too strong.** A tree is built from grounds and disposals are not grounds, so it cannot witness currentness. `office.lineage_versus_current` |
| W5 | *Relabelling content changes nothing legitimate.* | **Vacuous as checked and false as stated.** The check replayed the unchanged process; and `office.content_sensitive_jurisdiction` has permission reading content |
| W6 | *Six hypotheses H1-H6.* | **Reduced to two.** H1 and H2 are definitional under the new types; H4 and H6 are clauses of the semantic definition; H5 is a realization-level conformance condition |
| W7 | *`Valid` is primitive, constrained by three implications.* | **Defined instead.** Nothing needed the freedom to reject a grounded, permitted, provenance-adequate edit |

## The kernel

| # | claim | class | check |
|---|---|---|---|
| 1 | **Grounded Replay.** Under S1 and S2 every admitted occurrence has a finite tree: leaves in `G`, internal nodes accepted edits, children the grounds, positions strictly descending | DERIVED | `thm_grounded_replay` on every frame |
| 2 | **S1 is necessary.** Drop it and an edit grounded in an occurrence nobody issued is accepted; what it issues has no tree | COUNTEREXAMPLE | `TestS1IsNecessary` |
| 3 | **S2 is necessary.** Drop it and the ex-nihilo occurrence's tree is a leaf outside `G` | COUNTEREXAMPLE | `TestS2IsNecessary` |
| 4 | **Neither subsumes the other**; they fail on different frames | COUNTEREXAMPLE | `test_the_two_premises_fail_on_different_frames` |
| 5 | **Corollary 1**, no self-ratification | DERIVED | `cor_no_self_ratification` |
| 6 | **Corollary 2**, no laundering: an occurrence a rejected edit proposed is never admitted | DERIVED | `cor_no_laundering`; `office.laundering` |
| 7 | **Corollary 3**, persistence until an accepted edit disposes it | DERIVED | `cor_persistence`; `office.rogue_revocation` |
| 8 | Freshness is **definitional**, and what the theorems consume is unique **birth**, not unique issuance of a content | DEFINITION + FINITE-TEST-SUPPORTED | `office.readoption` issues one content twice |
| 9 | The kernel names no architectural or semantic identifier | FINITE-TEST-SUPPORTED, by parsing it | `test_it_names_no_architecture_and_no_semantics` |

## Lineage, currentness, checkers

| # | claim | class | check |
|---|---|---|---|
| 10 | `Live ⊆ Admitted`, strictly; and on a fixed trace `Grounded = Admitted` | DERIVED + COUNTEREXAMPLE | `office.lineage_versus_current` |
| 11 | A grounding tree certifies **origin** and cannot certify **currentness** | DERIVED, from the tree containing no disposal | `test_a_tree_names_no_disposal` |
| 12 | **Simulation.** Agreement along the trace gives `Lhat_t = L_t` for every `t` | DERIVED | `thm_simulation` |
| 13 | Agreement along the trace is **weaker** than global equality — a checker wrong at every unvisited state still simulates | COUNTEREXAMPLE | `test_a_checker_that_errs_off_the_trace_is_still_exact` |
| 14 | And **strictly stronger** than one-sided soundness, which preserves neither projection | COUNTEREXAMPLE | `office.missed_revocation` |

## The semantic layer

| # | claim | class | check |
|---|---|---|---|
| 15 | Validity is **defined**: grounding, non-emptiness, provenance completeness, permission | DEFINITION | `office.build` |
| 16 | Descriptive provenance and normative permission are separate, and persuasion is recorded and permitted | DEFINITION + FINITE-TEST-SUPPORTED | `office.persuasion` |
| 17 | Forgery and coercion fail different clauses, and whether coercion invalidates is the constitution's | FINITE-TEST-SUPPORTED | `office.forged_input`, `office.coerced_exercise` both ways |
| 18 | Jurisdiction is permission, not provenance | FINITE-TEST-SUPPORTED | `office.unauthorized_scope` |
| 19 | `Auth` is a predicate; nothing requires a partition, and a norm can bear on a permission judgment | DEFINITION + FINITE-TEST-SUPPORTED | `office.content_sensitive_jurisdiction` |

## The realization

| # | claim | class | check |
|---|---|---|---|
| 20 | A record extracts to a frame satisfying S1 and S2 | DERIVED; **argued, not mechanized** | `violations` empty on ten records at both contexts |
| 21 | Noninterference is **extraction factorization composed with fold determinism**; the second is definitional | DERIVED | `TestExtractionFactorization` |
| 22 | Extraction fails two ways: a different trace, or a different semantics | COUNTEREXAMPLE | `cases.partial_effect_pair`; `office.hidden_reading_pair` |
| 23 | Every Carroll discrimination survives | FINITE-TEST-SUPPORTED | `test_every_carroll_discrimination_survives` |
| 24 | A rejected uptake leaves the predecessor in force — which the previous objects could not express | FINITE-TEST-SUPPORTED | `C11` manipulated at `alpha:audited` |
| 25 | Permission is nearly vacuous on a record: `PAuth` carries no domain | DEFINITION, named | `ri_frame` docstring; `PRIORITIES.md` 67 |

## The consumers

| # | claim | class | check |
|---|---|---|---|
| 26 | Deference needs `Live_t(o)`, not `Grounded(o)` — so a tree is not enough for it | PROPOSAL | `CONSUMER_TEST.md` §2 |
| 27 | Both consumers need agreement along the trace; the previous asymmetry is withdrawn | DERIVED | entry 14 |
| 28 | Enforcement consumes `NormView_t` and gets the right target in all four repeal cases | FINITE-TEST-SUPPORTED | `TRADERIZATION_CONSUMER.md` §2 |
| 29 | The corrigibility theorem is statable and one hypothesis has no formal object | SOURCE-REPRODUCTION | `ReachableCorrectiveControl.lean:926,1051` |

## Proper Exercise

| # | claim | class | check |
|---|---|---|---|
| P1 | Fourteen separations between grounded authority and proper exercise, every one satisfying the kernel's premises | FINITE-TEST-SUPPORTED | `test_exercise.py` |
| P2 | **E2, no jurisdictional self-ratification.** No edit's permission can rest on a capability it creates — quantified over every capability assignment | DERIVED, from strict pre-state evaluation and freshness | `thm_no_jurisdictional_self_ratification`; `office.self_amendment(False)` |
| P3 | **E4.** No accepted edit widening beyond its basis gives non-increasing reach | DERIVED, about a class of permission relations | `thm_no_widening_gives_monotone_reach` |
| P4 | **E4's hypothesis is declinable**, so it is not a constraint: a constitution may license widening | COUNTEREXAMPLE | `office.constitutional_widening` |
| P5 | **There is no generic no-escalation theorem.** `self_expansion` and `blind_permit` are the same gazette with the same kernel verdicts; one escalates | COUNTEREXAMPLE | `test_e3_is_not_a_theorem` |
| P6 | Escalation has a clean definition — reach grows at an edit that widens — and it is measurable only against a non-plenary base | DEFINITION + FINITE-TEST-SUPPORTED | `exercise.gained`, `exercise.widens` |
| P7 | Grounds live on the edit, so legitimacy is tied to the **actual** exercise route and ex-post rationalisation fails | DERIVED + FINITE-TEST-SUPPORTED | `office.ex_post_rationalisation` |
| P8 | No proof-relevant witness object is needed: the support is already in the edit | DERIVED | entry P7 |
| P9 | Authority-transforming edits need no second ontology; self-amendment, delegation and total replacement are one calculus | FINITE-TEST-SUPPORTED | `TestAuthorityOverAuthority` |
| P10 | Joint and threshold authority need no authority algebra | FINITE-TEST-SUPPORTED, by reading the kernel | `office.threshold` |
| P11 | A negative side condition decides a verdict without becoming an ancestor | FINITE-TEST-SUPPORTED | `office.veto`; `exercise.tree_mentions` |
| P12 | Grounded Replay is unchanged: the kernel does not import the analysis and has no capability notion | FINITE-TEST-SUPPORTED, by parsing | `TestTheKernelIsUntouched` |
| P13 | Reflective Integrity cannot realize a capability: `PAuth` has no domain and a `NormEvent` has no slot for citing a governing protocol, so an external-rule discipline is **not** sufficient | DERIVED, from the record types | `PROPER_EXERCISE.md`, the kernel section |

## Answerability

| # | claim | class | check |
|---|---|---|---|
| A1 | **Answerability Continuity.** Under A1 and A2 an obligation outstanding at `s` is, at every later `t`, discharged in `[s,t)` or connected by a finite chain of accepted transfers to one outstanding at `t` | DERIVED | `thm_answerability_continuity` on every answerability constitution |
| A2 | **A1 is necessary**, and it is a premise that can fail: three constitutions violate it and each breaks the theorem and its corollary | COUNTEREXAMPLE | `TestA1IsNecessary`; `office.silently_deleted`, `transfer_to_nowhere`, `entitled_with_laundered_obligation` |
| A3 | **A2 is free from the type**, as freshness was on the entitlement side | DEFINITION + FINITE-TEST-SUPPORTED | `test_a2_is_free_from_the_type` |
| A4 | **Corollary**, no silent loss: every obligation ever outstanding is discharged or represented by an outstanding descendant | DERIVED | `cor_no_silent_loss` |
| A5 | **The two halves are independent.** Case 13 satisfies A1/A2 and fails entitlement; case 14 satisfies S1/S2 and fails A1 | COUNTEREXAMPLE, both directions | `test_a1_and_the_entitlement_premises_are_independent`, `test_the_other_direction` |
| A6 | **Corollary (the coupling).** An act the process was not entitled to perform discharges nothing — from `Valid` gating both folds, and from nothing else | DERIVED | `cor_discharge_requires_entitlement`; `office.rogue_discharge` at `alpha:audited` |
| A7 | The coupling is the **only** contact: `answer.py` reads `accepted`, `Frame` and `BASE` from the kernel and nothing else | FINITE-TEST-SUPPORTED, by parsing | `test_it_is_the_only_coupling` |
| A8 | **H-A.** Quantitative liability is not constitutive: four dilution constitutions, one carrying every issue forward at weight zero, satisfy A1, A2, the theorem and the corollary | COUNTEREXAMPLE | `TestDilution`; `office.diluted_to_nothing` |
| A9 | **Conditional.** If no accepted transfer reduces the summed weight it replaces, the potential is non-increasing except by discharge — a claim about a class of `Transfers` semantics, the counterpart of P3 | DERIVED, conditional | `thm_no_dilution_gives_monotone_potential` |
| A10 | **Per-parent weight accounting is wrong, not weaker.** A merge of two obligations of weight 1 into one of 1.5 passes per-parent and fails in total | COUNTEREXAMPLE | `office.merge_lenient`; `test_per_parent_accounting_is_wrong_on_a_merge` |
| A11 | Legitimate Evolution is a **named conjunction over a shared parameter** — not one theorem, not a bare conjunction, not a semantic definition | DEFINITION, argued in `ANSWERABILITY.md` §5 | entries A5, A6 |
| A12 | The entitlement/answerability duality is **real but narrow**: S1/A1 are opposite constraints on one fold shape, but answerability has no analogue of "leaves in `G`" and is silent on progress | DEFINITION + COUNTEREXAMPLE | `test_an_obligation_may_stay_open_forever` |
| A13 | Grounded Replay is unchanged: the kernel does not import the second replay and has no obligation notion | FINITE-TEST-SUPPORTED, by parsing | `TestTheKernelIsUntouched` |

## Open

| # | statement | class |
|---|---|---|
| 30 | **Recognition is an axiom**, over a base, an authority predicate, a semantics and an audit context | AXIOM |
| 31 | **Provenance completeness.** The round tried to state it non-circularly and failed; it is an explicit epistemic assumption on the extraction | OPEN — the largest hole, and it has survived four formulations |
| 32 | **A current-state certificate.** Replay, or a commitment plus a delta proof, or an attestation. Nothing here builds the second | OPEN — and now the interface's main cost |
| 33 | **Bounded-lifetime liability** | OPEN — `PRIORITIES.md` 69; entry A8 narrows it: any such bound is a condition on `Transfers`, not a structural theorem |
| 40 | **`Due`.** Which reason occurrences place a process under obligation. Not needed by either theorem; needed by a consumer wanting to say *why* something became owed | OPEN — and `ANSWERABILITY.md` §6 argues Reflective Integrity has no realizer, since it mints answerability roots from effects |
| 41 | Whether coverage — that some situation *ought* to have become due — is statable at all without a substantive semantics | OPEN — `unobservant()` is legitimate and notices nothing |
| 34 | Whether `Permit` needs internal structure | OPEN |
| 35 | Jurisdiction on a Reflective Integrity authority | OPEN — `PRIORITIES.md` 67 |
| 36 | A projection-specific simulation condition, weaker than trace agreement, valid when `Permit` factors through the projection | OPEN — stated, not claimed |
| 37 | A Lean port of Grounded Replay | OPEN — recommended; Proper Exercise adds nothing to port |
| 38 | Whether `Permit` has useful structure for some purpose other than the fourteen separations | OPEN — this pass found none needed |
| 39 | A capability field on Reflective Integrity's authority-bearing standing | OPEN — `PRIORITIES.md` 67, now with the reason an external rule cannot substitute |

## What no entry above claims

That either theorem is deep. Both are inductions over a list; two of the three
entitlement corollaries are two lines each. What they earn is that five
successive formulations failed the first, and that the second was built to have a
premise that can fail after a first version's could not.

That the conjunction is more than it is. Entry A6 is one corollary, it is real,
and it is the entire yield of packaging the two halves together.

That the semantic layer is settled. `Permit` and `ProvComplete` are parameters and
every substantive normative question lives in them.

That the realization is proved. Entry 20 is a paper argument checked on finite
records, and Reflective Integrity is itself unregistered.

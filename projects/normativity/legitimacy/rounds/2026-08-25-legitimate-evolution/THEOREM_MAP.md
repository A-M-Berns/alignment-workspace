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
| A1 | **Withdrawn.** The previous conclusion — discharged in `[s,t)` or carried to something outstanding at `t` — is **false** on transfer-then-discharge, split-then-discharge-both and merge-then-discharge, all with clean premises | WITHDRAWN, by countermodel | `TestTheOldConclusionWasFalse` |
| A2 | **Withdrawn.** The premise `A2` (fresh openings) was never load-bearing: a hand-built cycle violating freshness maximally satisfies the corrected theorem | WITHDRAWN, by countermodel | `TestA2WasNotLoadBearing` |
| A3 | **Withdrawn.** `thm_no_dilution_gives_monotone_potential` checked per-parent rather than total dilution, ignored fresh openings, and its discharge escape clause made it unfalsifiable on any trace with a discharge | WITHDRAWN | `test_the_withdrawn_version_is_gone` |
| A4 | **Withdrawn.** The shared acceptance bit gating both folds. It cannot represent a process answerable for an act it refused | WITHDRAWN, by countermodel | `office.unauthorized_act_opens_complaint` |
| A5 | **Answerability Continuity.** Under **A1**, every obligation outstanding at `s` has, at every later `t`, a finite resolution derivation whose frontier is non-empty and contains only obligations outstanding at `t` or discharged by an accepted edit before `t` | DERIVED | `thm_answerability_continuity` on every answerability constitution |
| A6 | **A1 is necessary**, and it is a premise that can fail: three constitutions violate it and each breaks the corollary | COUNTEREXAMPLE | `TestTheKernelIsUntouched`; `office.A1_BROKEN` |
| A7 | The witness is a **finite tree unfolded from a DAG**; a reconverging split gives one obligation two distinct leaves | DEFINITION + FINITE-TEST-SUPPORTED | `test_succession_is_a_dag_and_the_derivation_is_still_a_tree` |
| A8 | Termination comes from the **interval**, not from occurrence identity: an obligation may be its own descendant and the unfolding is still finite | DERIVED | `test_termination_comes_from_the_interval_not_from_freshness` |
| A9 | A `carried` node with no children is **not** a derivation; the conclusion requires a non-empty frontier, and A1's transferred-to-nothing clause supplies it | DERIVED | `office.transfer_to_nowhere` |
| A10 | **D1, due realization.** What the semantics says is owed at `t` is outstanding at `t+1` | AXIOM (structural premise) | `d1_due_realization` |
| A11 | **D1 is necessary.** A process with impeccable entitlement, no removals at all, and a represented reason its own semantics calls owed, passes everything else and enters nothing | COUNTEREXAMPLE | `office.recognized_due_but_never_entered` |
| A12 | **Corollary.** Every obligation the semantics ever made due has a resolution derivation from where it became due | DERIVED | `cor_recognized_is_entered` |
| A13 | **D1 requires neither coverage nor progress.** A process that represents nothing owes nothing; an entered obligation may stay open forever | COUNTEREXAMPLE, both | `office.unobservant`; `test_d1_does_not_smuggle_in_progress` |
| A14 | `Due` reads the normative state, so a reason represented at `u` can become owed at `t > u`; D1 is indexed by position for that reason | DEFINITION + FINITE-TEST-SUPPORTED | `office.due_arrives_later` |
| A15 | **Strict pre-state on the resolution side** is structural, not a clause: openings are unioned last, so opening-and-discharging in one act and self-ratifying resolution are both refused by A1 | DERIVED | `TestStrictPreState` |
| A16 | **Coupling, asymmetric.** An act the process was not entitled to perform discharges nothing | DERIVED | `cor_discharge_requires_entitlement`; `office.rogue_discharge` |
| A17 | **Coupling, converse.** An obligation may open at an edit the process refused, and one act may exercise both channels with only the opening taking effect | DERIVED + COUNTEREXAMPLE | `cor_opening_needs_no_entitlement`; `office.unauthorized_act_attempts_discharge` |
| A18 | The asymmetry does not open a laundering route: transfer is a removal and removals stay gated | DERIVED | `test_a_rejected_edit_still_removes_nothing` |
| A19 | **Quantitative burden conservation is not a generic structural consequence** of answerability continuity. Stated narrowly: it does not claim no semantics may impose one | COUNTEREXAMPLE | `TestTheQuantitativeRepair` |
| A20 | **Conditional, repaired.** No total dilution *and* every opened obligation a named successor gives non-increasing potential. Both hypotheses are needed | DERIVED, conditional | `thm_conserving_transfers_give_monotone_potential`; `office.high_regret` |
| A21 | Per-parent weight accounting is wrong, not weaker | COUNTEREXAMPLE | `office.merge_lenient` |
| A22 | Legitimate Evolution is a **named package of two closure theorems and two coupling laws** — option D. The entitlement/answerability duality is dropped, not narrowed | DEFINITION, argued in `ANSWERABILITY.md` §9 | entries A10, A16, A17 |
| A23 | Grounded Replay is unchanged: the kernel does not import the second replay, has no obligation notion, and `answer.py` reads only `accepted`, `Frame` and `BASE` from it | FINITE-TEST-SUPPORTED, by parsing | `TestTheKernelIsUntouched` |

## Open

| # | statement | class |
|---|---|---|
| 30 | **Recognition is an axiom**, over a base, an authority predicate, a semantics and an audit context | AXIOM |
| 31 | **Provenance completeness.** The round tried to state it non-circularly and failed; it is an explicit epistemic assumption on the extraction | OPEN — the largest hole, and it has survived four formulations |
| 32 | **A current-state certificate.** Replay, or a commitment plus a delta proof, or an attestation. Nothing here builds the second | OPEN — and now the interface's main cost |
| 33 | **Bounded-lifetime liability** | OPEN — `PRIORITIES.md` 69; entry A8 narrows it: any such bound is a condition on `Transfers`, not a structural theorem |
| 40 | **`Due` has no realizer.** Now a structural premise (D1), and Reflective Integrity cannot discharge it: `roots()` mints from `NormEvent`s only, `ReasonOcc` is never consulted, and RI's own `due()` is a different predicate. Smallest seam: a minting trigger keyed on reason occurrences, one function, no new event kind | OPEN — the pass's headline gap; checked against `ri_core.py`, `PRIORITIES.md` 71 |
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

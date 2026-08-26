# What is claimed, and on what

Classes are `AGENTS.md`'s, plus `DEFINITION` for a stipulation and `AXIOM` for a
substantive input the mathematics does not supply. **Nothing here is registered
and nothing is Lean-checked**, so no entry is above `test-supported`.

## The abstract theorems

| # | claim | class | check |
|---|---|---|---|
| 1 | **T1.** `|-_q` is a partial order and every derivation is finite, from L1 | DERIVED | `frame.derivable` terminates; `test_frame` runs it on both realizations |
| 2 | **T2, lineage existence.** Under L1 and L2 every authority has a finite well-founded provenance whose minimal elements lie in the base, **with no legitimacy clause taking part** | DERIVED | `thm_finite_lineage` on four records and three registers |
| 3 | **T2 is not vacuous.** A manufactured authority is in force, has a provenance reaching the base, and is not derivable | FINITE-TEST-SUPPORTED | `C10`, `laundered_register` |
| 4 | **T2', canonicity.** Under L2' the provenance is determined by the target, so a process cannot present a flattering lineage | DERIVED | `l2_unique_issuance` clean on both realizations |
| 5 | **T3a.** L0 + L3 give `G \|-_q y => q \|= y` | DERIVED | `thm_stability_of_derivable` |
| 6 | **T3, no self-ratifying authority.** L0 + L3 + L3' + L4 give that no ancestor of a certified authority, at any depth, was issued by a challenged exercise. Step-local obligations, global conclusion | DERIVED | `thm_no_bootstrap` on `C10`, `C23`, `laundered_register`, `merge_register` |
| 7 | **T4, content independence.** No relabelling of content changes what is derivable | DEFINITION at the abstract level; FINITE-TEST-SUPPORTED as a condition on the realization | `test_relabelling_what_the_standings_say_changes_nothing_derivable` |
| 8 | **T5 / T5'.** Delegation and disposal are expressible in the account layer and not in the spine | DERIVED | `thm_delegation_is_invisible_on_authorities`, `thm_disposal_is_invisible_on_authorities` |
| 9 | **T6, visible discontinuity.** Under L5 and L6 an account fails continuity exactly when one beneath it is outstanding | DERIVED | `thm_visible_discontinuity` on three records and one register |
| 10 | **Verifier soundness.** `verify(f,c) => base(c) \|- target(c)`, by re-derivation | DERIVED | `test_the_verifier_recomputes_rather_than_reading_the_verdicts` |
| 11 | **Composition.** `\|-_q` is a least fixed point, so one bridge principle suffices for arbitrarily long evolution | DERIVED | the closure in `frame.derivable` |

## The realization

| # | claim | class | check |
|---|---|---|---|
| 12 | A Reflective Integrity record with the Carroll challenge operator satisfies **L0, L1, L2, L2', L3', L4** and, with the account layer, **L5, L6** | DERIVED from RI §§13, 15.2, 17, 19, 24 and the identifier scheme; **argued, not mechanized** | `fr.violations` empty on every fixture |
| 13 | It satisfies **L3** exactly where the record's schemas are pre-state-blind, and a legal record violates it otherwise | COUNTEREXAMPLE | `C28`, both arms |
| 14 | **L3' rests on the identifier scheme alone** and holds in the arm where L3 fails, so the two are different hypotheses | COUNTEREXAMPLE | `test_origin_necessity_needs_no_such_hypothesis` |
| 15 | `Chal` is read off the reason ledger and stability off the replay, so **L4 is a claim about the operator** rather than a stipulation | DEFINITION + FINITE-TEST-SUPPORTED, by reading the function | `test_the_challenge_set_is_read_off_the_reasons_not_the_replay` |
| 16 | A register of warrants and appointments satisfies the whole spine and both account axioms, importing `frame` and nothing else of this repository's | FINITE-TEST-SUPPORTED, by parsing the module's imports | `test_the_second_realization_imports_no_normative_architecture` |
| 17 | Both realizations run the same theorems and the same refusals: a laundered warrant and a manufactured protocol are excluded by one relation | FINITE-TEST-SUPPORTED | `TestNoBootstrap` |

## Design decisions with a witness

| # | claim | class | check |
|---|---|---|---|
| 18 | Derivability requires **all** of `src(t)`. The merge register separates that from the one-of rule; the RI realization cannot, because `G6` refuses a supersession with an absent target | COUNTEREXAMPLE | `merge_register`, both rules run |
| 19 | The account layer is **not** a conjunct of `\|-`. A record with a clean spine, a derivable authority and a permanently outstanding account is the reason | COUNTEREXAMPLE | `delegated_custody(answered=False)` |
| 20 | A chain certificate cannot carry the branch: a derivation to one successor of a two-way supersession leaves the base discontinuous and says nothing about it | COUNTEREXAMPLE | `split_with_due_branch` |
| 21 | No verdict is assembled across two challenges; the relation intersects per-challenge judgments and never excises a union | FINITE-TEST-SUPPORTED, by reading the function | `test_no_verdict_is_assembled_across_two_challenges` |

## The consumer

| # | claim | class | check |
|---|---|---|---|
| 22 | The legitimacy fact a deference theorem consumes is `G \|-_B x`, and its job is to make `GradeTrust` a proposition the advisor did not select | PROPOSAL | `CONSUMER_TEST.md` §2; no theorem is proved |
| 23 | The current kernel cannot state it: `W` carries no index, and `FUTURE_AGENT_SPEC.md`'s own diagnosis is that the authorization relation has to be in the type | SOURCE-REPRODUCTION + reading | `DelegationBridge.lean:52`; `FUTURE_AGENT_SPEC.md` status block |
| 24 | The required change is one field — `W : A -> C -> P -> Q` — plus the hypothesis that the grade is a function of the authority in force. Neither revises a registered statement | PROPOSAL | — |
| 25 | The corrigibility theorem is statable and one of its three hypotheses has no formal object: `ReachableCorrectiveControl`'s registered refutations say its capability predicate measures advisor cooperation | SOURCE-REPRODUCTION | `ReachableCorrectiveControl.lean:926,1051` |

## Open, and what would close it

| # | statement | class |
|---|---|---|
| 26 | **Recognition transport is not a theorem.** It is the recognition axiom **(R)** plus verifier soundness plus composition, and this round does not derive (R) | AXIOM — stated, not hidden |
| 27 | The stability half of a certificate does not compress in the Reflective Integrity realization. A positive survival witness for one exercise is the excised prefix that admits it, and the operator is neither monotone nor composable | OPEN — the interactive route is sketched in `CROSS_PROCESS_INTERFACE.md` §3 and nothing here builds it |
| 28 | `Q` is only as wide as the record's provenance links. An external process satisfying L0-L4 with a `Chal` naming almost nothing is certified by the interface | OPEN — the largest hole, and inherited unchanged from the Carroll round's `C25` |
| 29 | Whether the spine is minimal. L2' is used only for T2'; nothing shows the remaining six cannot merge | OPEN |
| 30 | Whether pre-state-blindness is worth imposing on Reflective Integrity for what L3 buys, and what it would cost | OPEN — the Carroll round's item 41a, now with a second consumer |
| 31 | A Lean port of the frame, the spine and T2/T3. The abstract layer is finite, first-order and has no dependency on the reference models | OPEN — nothing here is Lean-checked |
| 32 | Whether `A` can come to be *entitled* to the stability judgments, as against a theorem consuming them | OPEN — the epistemic lifting problem, unchanged from the August 17 interface §7 |

## What no entry above claims

That the axioms are correct. Each is a condition the round wrote, and the
evidence that any of them is doing work is a countermodel the round also wrote.
The two exceptions are the places where an existing artefact refuted a choice:
`C28`, which is the Carroll round's fixture and which killed the unconditional
form of the realization theorem, and `G6`, which made the all-of-`src` decision
undecidable in our own architecture and forced a second realization to settle it.

That the abstraction is complete. `prospective_license` — whether a particular
act was permitted — is **not** lifted to the frame and reads content in three
fields the Carroll round names as one supplied seam. Only *possession* of
authority is abstracted here, and that is the half recognition needs.

That the realization is proved. Entry 12 is a paper argument from Reflective
Integrity's statements, checked on finite records. It is not mechanized and RI
itself is unregistered.

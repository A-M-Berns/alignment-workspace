# What is claimed, and on what

Classes are `AGENTS.md`'s, plus `DEFINITION` for a stipulation and `AXIOM` for a
substantive input the mathematics does not supply. **Nothing here is registered
and nothing is Lean-checked**, so no entry is above `test-supported`.

## Withdrawn

| # | claim | why |
|---|---|---|
| W1 | *A licence need only survive the challenge.* The first pass's derivability rule required `q \|= lic(t)` and not `lic(t) in Derivable_q` | **Refuted.** `warrant.stable_but_illegitimate_register` satisfies every axiom, derives `w:y`, and puts a challenged issuer in `w:y`'s provenance — so the no-bootstrap theorem's *conclusion* was false, not merely unproved |
| W2 | *`src(t)` is the legitimacy-parent relation.* | **Refuted.** `warrant.cleanup_register`: a legitimate revocation of a fraudulent warrant produced an illegitimate successor. `affected` and `parents` are now two fields |
| W3 | *L2' buys only canonicity*, while `minted_by` raised on a second issuer and both `provenance` and the no-bootstrap theorem ran through it | **Corrected.** `warrant.two_issuers_register`; the theorem is now stated over a derivation and `provenance` closes over every issuer |
| W4 | *Pre-state-blindness is what L3 needs*, with the implication that a finer exercise identity might remove it | **Corrected.** `cases.partial_effect`: under effect identity L3 is free and **L3'** fails instead. The condition is required under either identity |
| W5 | *Challenge coverage is a caveat.* | **Promoted to a hypothesis** with a type: `ThreatModel`, `coverage`, `certified_against` |

## The abstract theorems

| # | claim | class | check |
|---|---|---|---|
| 1 | **T1, lineage existence.** Under L1 and L2 every authority has a finite well-founded provenance whose minimal elements lie in the base, with no legitimacy clause and **without L2'** | DERIVED | `thm_finite_lineage` on seven registers and six records |
| 2 | **T1 is not vacuous.** A manufactured authority is in force, reaches the base, and is not derivable | FINITE-TEST-SUPPORTED | `C10`, `laundered_register` |
| 3 | **T1', canonicity.** Under L2' the provenance is determined by the target — and that is all L2' buys | DERIVED + COUNTEREXAMPLE | `two_issuers_register` |
| 4 | **T2a.** L0 + L3 give `G \|-_q y => q \|= y`, and hence `q \|= lic(t)` for every certified `t` | DERIVED | `thm_stability_of_derivable` |
| 5 | **T2, no self-ratifying authority.** For every derivable `y` there is a certified derivation none of whose exercises is challenged and each of whose authorities has an unchallenged issuer | DERIVED | `thm_no_bootstrap` on eight frames; and `bootstrapped_under` non-empty for the rejected rule on the same frame |
| 6 | **The theorem must be stated over a derivation.** A route-blind provenance can contain a challenged issuer while the authority is legitimate by another route | COUNTEREXAMPLE | `two_issuers_register` |
| 7 | **T3, content independence.** No relabelling of content changes what is derivable | DEFINITION abstractly; FINITE-TEST-SUPPORTED as a condition on the realization | relabelling `C14` |
| 8 | **T4, persistence.** Under L6 an authority stays in the legitimate frontier until an exercise acts on it | DERIVED | `thm_persistence` on five frames |
| 9 | **T4', antitone in challenges.** Adding challenges shrinks what is derivable, so a new challenge is a second exit from the frontier with nothing acting on the authority | DERIVED | `thm_legitimacy_is_antitone_in_challenges` |
| 10 | **T5, visible discontinuity.** Under L7 and L8 an account fails continuity exactly when one beneath it is outstanding | DERIVED | `thm_visible_discontinuity` |
| 11 | **Delegation and disposal are expressible only in the account layer** | DERIVED | the two `thm_*_is_invisible_on_authorities` |
| 12 | **Verifier soundness**, by re-derivation; and **composition**, since `\|-_q` is a least fixed point | DERIVED | `verify`, `derivable` |
| 13 | **Coverage is separable from form.** A frame with no challenges satisfies every axiom and certifies everything, and certifies nothing against a threat model it misses | COUNTEREXAMPLE + DEFINITION | `undercovered_register`, `certified_against` |

## The realization

| # | claim | class | check |
|---|---|---|---|
| 14 | A Reflective Integrity record with the Carroll operator satisfies **L0, L1, L2, L2', L3, L4** and, with the lifecycle and accounts, **L5-L8** | DERIVED from RI §§12.3, 13, 15.2, 17, 19, 24 and the identifier scheme; **argued, not mechanized** | `fr.violations`, `lifecycle_violations`, `account_violations` empty on every fixture |
| 15 | Under effect identity it satisfies **L3** unconditionally and **L3'** exactly where the record's schemas are pre-state-blind | COUNTEREXAMPLE | `cases.partial_effect`, both identities |
| 16 | Under event identity the two swap: L3' is free and L3 needs the same condition. **Pre-state-blindness is therefore not an artefact of the map** | COUNTEREXAMPLE | same record, `TestExerciseIdentity` |
| 17 | `C28` is repaired by effect identity and is **not** the general case | COUNTEREXAMPLE | `C28` clean under effect identity while `partial_effect` is not |
| 18 | `parents` is not `targetsN(effect)`: a `Create` inherits from its licence alone, a revocation inherits nothing, so the record calculus expresses a cleanup in two events | DEFINITION + FINITE-TEST-SUPPORTED | `cases.record_cleanup` |
| 19 | `Chal` is read off the reason ledger and stability off the replay, so **L4 is a claim about the operator** | DEFINITION + FINITE-TEST-SUPPORTED | reading `challenged_exercises` |
| 20 | A register of offices satisfies the whole spine, the lifecycle and both account axioms, importing `frame` and nothing else | FINITE-TEST-SUPPORTED, by parsing imports | `test_the_second_realization_imports_no_normative_architecture` |
| 21 | A record's own episodes generate a threat model its challenges cover **by construction** — the ceiling on self-certification | DEFINITION | `threat_from_episodes` |

## The consumers

| # | claim | class | check |
|---|---|---|---|
| 22 | The deference premise is `x in AuthorityView_s`, and its job is to make `GradeTrust` a proposition the advisor did not select | PROPOSAL | `CONSUMER_TEST.md` §2 |
| 23 | The kernel cannot state it: `W` carries no index, and `FUTURE_AGENT_SPEC.md`'s own diagnosis is that the authorization relation has to be in the type | SOURCE-REPRODUCTION | `DelegationBridge.lean:52`; that file's status block |
| 24 | The enforcement premise is `NormView_s` and `lifetime(n)`, and the norm projection is a real set on a force-bearing record | PROPOSAL + FINITE-TEST-SUPPORTED | `cases.force_bearing` |
| 25 | **A legitimate norm can be unenforceable.** Under the default exhaustion policy force is withheld and "the endorsement keeps its normative standing" | SOURCE-REPRODUCTION | `force_api.compile_safe_force` docstring |
| 26 | Entitled, accountable and serviceable are three independent interfaces; the frame carries no liability field | DEFINITION + FINITE-TEST-SUPPORTED | `TestTheThreeInterfacesAreIndependent` |
| 27 | The corrigibility theorem is statable and one hypothesis has no formal object | SOURCE-REPRODUCTION | `ReachableCorrectiveControl.lean:926,1051` |

## Open, and what would close it

| # | statement | class |
|---|---|---|
| 28 | **Recognition transport is not a theorem.** (R) plus verifier soundness plus composition, and (R) now also commits the recognizer to a threat model | AXIOM — stated, not hidden |
| 29 | **Bounded-lifetime liability.** That a norm's allocated charge over its legitimate lifetime is bounded by an allowance attached at issuance, and that such allowances are summable. Level I bounds the total over all norms and all time and does not give this | OPEN — the exact missing theorem for persistent enforcement |
| 30 | **`depends` is supplied from outside.** Coverage is a hypothesis and nothing computes it; the Carroll round's `C25` is now visibly a coverage failure | OPEN — the largest hole |
| 31 | The stability half of a certificate does not compress in the Reflective Integrity realization | OPEN — the interactive route is `PRIORITIES.md` item 67 |
| 32 | Whether pre-state-blindness is worth imposing on Reflective Integrity, now that it is required under either exercise identity and by two consumers | OPEN — sharper than the Carroll round's 41a |
| 33 | Whether the spine is minimal. L2' is out; L5-L8 are four bookkeeping axioms a better factorization might do with two | OPEN |
| 34 | Whether `A` can come to be *entitled* to the stability judgments, as against a theorem consuming them | OPEN — the epistemic lifting problem |
| 35 | A Lean port of the frame, the spine and T1-T5 | OPEN — deliberately not attempted this pass |

## What no entry above claims

That the axioms are correct. Each is a condition the round wrote. The evidence
that the exercise was adversarial is the withdrawn table: a review's diagnosis
refuted a shipped theorem, two registers refuted two shipped design decisions,
and a new record refuted the round's own first reading of what the identity
repair would achieve.

That the abstraction is complete. `prospective_license` — whether a particular act
was permitted — is not lifted and reads content in three fields the Carroll round
names as one supplied seam. Only possession of authority and the lifecycle of what
is in force are abstracted here.

That the realization is proved. Entry 14 is a paper argument from Reflective
Integrity's statements, checked on finite records, and Reflective Integrity is
itself unregistered.

That the account layer's abstraction is tested. `warrant.py` realizes it, but the
realization was written to match rather than found independently.

# Theorem map

Nothing here is registered and nothing is kernel-checked. Every entry is an exact
finite check over a declared domain, and the class is `test-supported`. Statements
are given at the strength the witnesses support: where a result holds only over
the fixture, it says so, and where a result is an unbounded quantification
established by an invariant, it says that instead.

```sh
python3 tests/run.py     # 147 tests
```

## The fixture

Three agents `H`, `C`, `A`. Eleven contents, of which two are practical. Three
subject matters plus three reserved authority subjects. The starting position has
`H` acknowledging `p`, `C` acknowledging `r`, all three endorsing the same
practice, and grants `H:correction`, `H:authority:H`, `H:authority:A`,
`A:operations`.

The reference position for the loss results — written `loaded` below — adds a
challenge by `C` against `q` on the ground `r`, and an assertion of `alpha` by
`H`. `exposed` additionally raises `a_rho` and `beta` by query. At `exposed`,
`defect = 5/2` against a bound of `22`; at `loaded`, `defect = 3/2`, because only
`q` has been raised.

---

## Answerability

| | statement | strength | test |
|---|---|---|---|
| **T1** | Disavowing a consequential commitment does not remove it from another scorekeeper's attribution while the basis stands. Disavowing the basis does remove it. | fixture | `T1NoCheapDisavowal`, 4 cases |
| **T2** | Revising one's own inferential practice removes the commitment from one's own attribution and from no other scorekeeper's, and leaves a live challenge live. | fixture, plus an exhaustive check that **no** move of `H` writes `practice[C]` or `ack[C]` | `T2SelfRevisionIsNotSelfRelease`, 5 cases |
| **T3** | Both directions of error are expressible. `C` has an entitled challenge against `H` and `H` has an entitled challenge against `C`, simultaneously, and neither is privileged. No oracle field exists. | fixture | `T3TheCriticIsNotAnOracle`, 4 cases |
| **T4** | Unanimity does not settle. A position all three agents acknowledge, under the practice all three endorse, carries a commitment every one of them scores as defeated. | fixture | `T4ConsensusIsNotAnOracle`, 3 cases |
| **T5** | The reasoner may retire two inference rules, drop an incompatibility, retract its premise and acknowledge its critic's ground, in a legal run. Answerability is not conclusion preservation. | fixture | `T5RadicalRevisionPositiveControl`, 2 cases |
| **T6** | Of four routes out of an applicability burden, three fail and the fourth is retraction. Undercutting converts an entitled commitment into an **unentitled** one rather than removing it. | fixture | `T6ApplicabilityLaundering`, 7 cases |
| **T7** | Asserting an authority claim writes `ack` and never `grants`. No legal move of `A` alters `grants` at the starting position, and the grant route works when the holder of the reserved subject uses it. | fixture, plus exhaustive over `A`'s legal move set | `T7NoSelfAuthorization`, 4 cases |
| **T8** | Ordinary persistence is derived and needs no transport object. Persistence through a change of vocabulary is **not** derived, and no move of `H` performs such a change. | fixture | `T8WhatRemainsOfDiachronicAnswerability`, 3 cases |

**T2 is the round's load-bearing result.** Its necessity witness is
`test_the_perspectival_difference_is_what_carries_the_two_theorems`: substituting
the target's own practice for the scorekeeper's, which is the reading the equation
rejects, makes T2 fail on the same trajectory.

---

## Learning

| | statement | strength | test |
|---|---|---|---|
| **L1** | The public loss is exact, bounded by `2·\|contents\| = 22`, and unchanged by retiring every committive rule and adding every incompatibility to the learner's own practice. It falls when the learner acknowledges or vindicates. | fixture | `L1PublicProspectiveLoss`, 6 cases |
| **L2** | Nine declarative programs, no callables, eight-boolean sealed guard context, every map closed on the eight labels. | fixture, plus schema assertion | `L2LawfulRepairGrammar`, 5 cases |
| **L3a** | The collapse mechanism reproduces. Under record-responsive admissibility, `vindicate` and `disavow` have singleton cores: every uniform comparator fixes them. | fixture, 7 states | `L3ComparatorCollapse` |
| **L3b** | And it forbids the repair most worth having: `disavow` is pinned, so no uniform comparator may send a disavowal to a reopening. | fixture | `test_and_it_forbids_exactly_the_repair_most_worth_having` |
| **L3c** | Under tolerant admissibility the class does not collapse — it has `6 588 344` members — but it is normatively empty: it permits sending `vindicate` to `self-revise`. | fixture | `test_the_tolerant_notion_does_not_collapse_and_is_junk_instead` |
| **L3f** | Both collapse findings survive the refinement unchanged: `disavow` and `vindicate` are still the pinned pair, and the tolerant class is still `6 588 344`. | fixture, recomputed | `L3ComparatorCollapse` |
| **L3d** | The `core` characterization agrees with brute-force enumeration over all `4⁴` maps on a four-label alphabet, under both notions. | exhaustive on the restricted alphabet | `test_the_collapse_shortcut_agrees_with_brute_force` |
| **L3e** | The fixed-program class does not collapse, and its non-identity members differ from the identity **as maps at a state**. At least five programs are non-identity somewhere; at least four differ from the identity at `loaded`. | fixture | `test_the_fixed_program_reading_does_not_collapse` |
| **L4** | One fixed program covers states whose admissible sets differ, and two states reached by different routes with the same public status receive the same map from every program. Certification is status-indexed, not date-indexed. | fixture | `L4PublicGuardHypothesis`, 3 cases |
| **L5** | `acknowledge_exposed` saves exactly `1/2` at `loaded`. Played against a **re-filed** failure recurring at every date, regret is exactly `T/2` at `T ∈ {12, 24, 48, 96}`; at density `1/2` it is exactly `T/4`. Superseded as an interface claim by P6 below, which lets the state evolve. | fixture, four horizons, exact rationals | `L5RecurrentRepairWitness`, 5 cases |
| **L6** | Zero regret against the nine programs is compatible with standing in a defective position, and the class does not reach every loss-reducing play in the alphabet. | fixture | `L6LearningInterpretation`, 2 cases |

### The comparator verdict, stated precisely

The collapse was **not** dissolved by scorekeeping and **not** left standing. What
the round shows is that it is an artefact of a quantifier the source theorem never
required.

The uniform reading asks for one state-independent map carrying admissible labels
to admissible labels at every state. Blum–Mansour's Theorem 18 asks for a fixed
*rule* inducing a history-indexed family `F^t`. Those are different objects, and
the second is the one an online-learning reduction consumes. Under the first,
labels that some state pins are frozen — and the fixture shows the frozen ones are
exactly the repairs with content. Under the second, nine fixed records induce
state-varying maps, with lawfulness a predicate of eight public booleans that
cannot see the loss.

So the answer to the dispatch's L4 is **yes, with a caveat**: a fixed program
whose guard reads public scorekeeping status is a genuine non-identity
transformation class, and its certification is indexed by status rather than by
date. The caveat is that this round did not construct a learner, measure a regret
curve, or check the fixed-action bridge's other hypotheses against this fixture.

**And the refinement pass narrowed it further.** Under endogenous evolution the
additive comparison survives for one non-identity program out of nine. See the
next section.

---

## The refinement pass

| | statement | strength | test |
|---|---|---|---|
| **P1** | The practical-authority term was self-launderable: `H` discharges it by granting itself the subject, changing no acknowledgment, challenge or critic practice. Removed from the theorem-facing loss. | fixture, displayed witness | `P1LossDependency`, 5 cases |
| **P1b** | The moves of `H` that lower the remaining loss are exactly `assert`, `disavow`, `vindicate`, `suspend`. No `revise_*`, `grant` or `revoke` by `H` changes it at all. | exhaustive over `H`'s legal move set | `test_the_exact_class_of_edits_the_loss_resists` |
| **P2** | A consequential commitment is charged only once publicly raised. A latent one is attributed and costs nothing; raising it costs `1/2`; the charge survives self-revision and falls to acknowledgment. | fixture | `P2ExposureGating`, 5 cases |
| **P3** | Protocol legality, normative compilation and performance are three predicates. `self-revise` is legal and licensed by no certificate. Every non-identity program names a positive public reason, as data. | fixture | `P3LegalityCompilationPerformance`, 5 cases |
| **P4** | Committive and permissive inference are separate relations. `w` is committed, never entitled, and not precluded. Vindication requires an entitlement-preserving route. | fixture | `P4CommitmentVersusEntitlement`, 6 cases |
| **P5** | `suspend` is a distinct move that leaves the commitment in force; its discount cannot be self-awarded. `query` has a real effect where the content is unraised and is redundant where a challenge already raised it. | fixture | `P5ActionSemantics`, 7 cases |
| **P6** | **Negative.** Once each comparator's licensing condition is allowed to recur, **no** non-identity program keeps bounded local-versus-replay distortion. `vindicate_live` appears bounded at `1` under an environment supplying one challenge, and goes to `2, 10, 26, 58` once challenges replenish. | fixture, four horizons, two environments, exact rationals | `P6EndogenousEvolution`, 7 cases |
| **P7** | The public status conflated challenges differing in the challenger's standing, while the decoder directs vindication at the challenger. Enriched by a property, not a name. A content-level conflation remains. | fixture | `P7PublicStatusSufficiency`, 4 cases |
| **P8** | Unilateral self-release stays blocked; **coordinated** revision by `H` and `C` together dissolves the burden with the acknowledged history untouched. Neither agent can do it alone, and no move of `H` produces `C`'s revision. | fixture, exhaustive over `H`'s move set | `P8CoordinatedStandardsDrift`, 4 cases |

### Endogenous evolution: the exact tables, and a correction

`local` compares losses at the actual trajectory's states; `replay` lets the
transformed run evolve. The additive reduction assumes their difference is zero.

**Environment A** raises the least unexposed consequence each date.

| program | base | `T=4` | `T=8` | `T=16` | `T=32` |
|---|---|---|---|---|---|
| `vindicate_live` | `hold` | 1 | 1 | 1 | 1 |
| `acknowledge_exposed` | `hold` | 1 | 7 | 19 | 43 |
| `answer_then_acknowledge` | `hold` | 1/2 | 8 | 24 | 56 |
| `query_not_disavow` | `disavow` | 4 | 16 | 40 | 88 |
| `suspend_defeated`, `refuse_self_revision` | `hold` | 0 | 0 | 0 | 0 |

Read alone this says `vindicate_live` has a horizon-independent bound and defines
a theorem-facing subclass. **That reading is wrong, and this round wrote it down
before catching it.**

Environment A supplies exactly one live challenge for the whole run. A comparator
that discharges challenges can therefore fire once and gain a bounded amount, so
its distortion is bounded for a reason that has nothing to do with stability.
`suspend_defeated` and `refuse_self_revision` sit at zero for the same kind of
reason: they are the identity on this trajectory.

**Environment B** additionally replenishes the licensing condition — the critic
acquires an entitled ground and raises a fresh challenge.

| program | base | `T=4` | `T=8` | `T=16` | `T=32` |
|---|---|---|---|---|---|
| `vindicate_live` | `hold` | 2 | 10 | 26 | 58 |

`test_the_replenishing_environment_really_replenishes` is the necessity witness
that Environment B does what it claims: under `hold` the live-challenge count
rises to three and stays above one.

**So the result is negative, not mixed.** No non-identity comparator keeps bounded
distortion once its licensing condition recurs. The additive Φ-regret bridge does
not apply to this repair grammar.

### What actually drives it

Not the endogenous coupling, which was this round's first explanation and is
**falsified**. Replacing the demand process with a fixed cyclic schedule that
never reads the learner's acknowledgments still gives growing distortion —
`1, 5, 13, 29` against `1, 7, 19, 43` for `acknowledge_exposed`. The coupling adds
to the magnitude and is not necessary for the growth.

What drives it is that a repair's effect is **durable and accumulates**. An
acknowledgment or a vindication persists, so the replayed run enjoys it at every
later date, while the local comparison re-measures each date from a state where
the repair was never applied. Any repair grammar whose moves durably change state
and whose licensing condition recurs will break additivity, and nothing about
perspectival scorekeeping is implicated.

**This is not a new obstruction.** `NORMATIVE_LEARNING_INTERFACE.md` already
carries the distortion term `B_T(g)` and the counterfactual-stability layer as
`ASPIRATIONAL / OPEN`. What this round adds is an exact finite instance with
numbers, and the observation that the boundary is saturation rather than any
property of the repair's normative content. **The saturation characterisation is a
conjecture** with one confirming and several disconfirming instances on one
fixture, not a result.

---

## Corrigibility

| | statement | strength | test |
|---|---|---|---|
| **C1** | Epistemic authority is operative — permitted testimony transmits entitlement that deferral without it does not — and confers no practical jurisdiction. **No advisor run of any length** reaches a grant. | unbounded in run length, by invariant; cross-checked by brute force to depth 4 | `C1EpistemicDeferenceIsNotJurisdictionTransfer`, 5 cases |
| **C2** | Practical authority is scoped: `A` holds `operations` and lacks `correction`; `H` holds `correction` and lacks `operations`. Neither dominates. Holding a subject confers no power to confer it. | fixture | `C2PracticalAuthorityIsScoped`, 4 cases |
| **C3** | Standing without access: `H` holds an entitled challenge and the advisor removes its corrective capability in one move. The combined predicate refuses it. | fixture | `C3NormativeStandingWithoutEffectiveAccess`, 3 cases |
| **C4** | Access without standing: `H` holds protected capability and performs the corrective act, and has no entitled ground. The combined predicate refuses it. | fixture | `C4EffectivePowerWithoutNormativeStanding`, 4 cases |
| **C5a** | The principal has effects no advisor action reproduces, from two independent sources: `assert` (undertaking is agent-indexed) and `revoke` (the reserved subjects are the principal's). The advisor's coordinate does **not** contain the principal's. | fixture, enumerated over the advisor's whole legal move set | `C5ProtectedEffectiveAccess` |
| **C5b** | Future corrective capability survives **every advisor policy of every length**. | unbounded, by invariant | `test_future_capability_is_universal_over_advisor_policies` |
| **C6** | A challenge can be discharged by vindication with the challenged party's conclusion unchanged and the challenger's incompatible commitment intact; or by revision; and vindication is refused where the premises are undercut. | fixture | `C6NoHumanVetoByDefinition`, 4 cases |
| **C7** | Standing and protected access are independent: all four cells witnessed. | fixture | `C7CombinedPredicateIndependence`, 4 cases |

### How C5b is established, and why it is stronger than a search

The predecessor's capability predicate quantified the advisor existentially, so a
constant hostile policy destroyed the capability while the predicate certified it.
The dispatch asked for a universal quantifier. A bounded reachability search would
give one only up to a depth.

The argument here is an invariant instead:

1. the capability is a predicate of `grants`;
2. `grants` is written only by `grant` and `revoke`;
3. their precondition is itself a predicate of `grants` — holding
   `authority:<holder>`;
4. at the starting position the advisor holds no reserved subject, so (3) fails,
   so `grants` is unchanged after any advisor move;
5. by (4) the same argument applies at the successor, without bound.

`test_the_advisor_is_not_simply_inert` is the necessity witness: the advisor has
more than twenty legal moves at that position and changes the state with them.
`test_the_capability_predicate_is_not_advisor_permissioned` is the other: hand the
advisor a reserved subject and the predicate goes false, so it is not vacuous.

**What this does not establish.** The protection is a non-reachability property of
the authority coordinate, and it holds because the fixture does not grant the
advisor a reserved subject. The round did not derive that the coordinate *must* be
arranged this way, and nothing here says a real system's authority relation is
advisor-inaccessible. The finding is that the relation has to be **in the type**,
where a transition precondition reads it — which is what the deference line's
non-recoverability result already concluded from the other direction.

---

## Necessity witnesses

| hypothesis | witness that dropping it breaks the result |
|---|---|
| the practical term is excluded from the loss | `test_the_practical_term_was_self_launderable` — including it makes K11 executable |
| exposure gates the consequential charge | `test_the_gate_is_what_stops_a_logical_omniscience_norm` |
| suspension is judged by the scorekeeper | `test_suspension_discounts_only_what_the_scorekeeper_takes_to_be_undercut` |
| committive rules do not transmit entitlement | `test_a_committive_rule_transmits_commitment_without_entitlement` |
| the environment reads what the repair changes | the P6 split — `vindicate_live` bounded, `acknowledge_exposed` not |
| the scorekeeper's practice, not the target's, computes attribution | `test_the_perspectival_difference_is_what_carries_the_two_theorems` |
| the critic's practice is read by the loss | `test_the_critics_practice_is_what_the_loss_reads` — blank it and the defect is `0` |
| material incompatibility gives a challenge force | `test_the_incompatibility_relation_is_what_gives_a_challenge_force` |
| the grant relation is read by the transition | `test_the_grant_relation_is_what_the_transition_reads` |
| the advisor lacks a reserved subject | `test_the_capability_predicate_is_not_advisor_permissioned` |
| the advisor is not inert | `test_the_advisor_is_not_simply_inert` |
| `a_rho` does not install `rho` | `test_asserting_the_applicability_content_does_not_install_the_rule` |
| vindication is not automatic | `test_vindication_is_refused_where_no_justification_exists` |
| the `core` shortcut is sound | `test_the_collapse_shortcut_agrees_with_brute_force` |

## Kill criteria

| | verdict |
|---|---|
| K1 self-oracle | avoided — T2, L1 |
| K2 critic-oracle | avoided — T3 |
| K3 community-oracle | avoided — T4 |
| K4 environment-oracle | avoided — no such field; T3's schema check |
| K5 frozen normativity | avoided — T5 |
| K6 authority by label | avoided — C5, `test_the_grant_relation_is_what_the_transition_reads` |
| K7 capability by cooperation | avoided — C5b's invariant |
| K8 simulation substitution | avoided — C5a |
| K9 comparator identity collapse | avoided in the fixed-program reading; **confirmed** in the uniform reading, L3a–b. Under endogenous evolution the class with a usable additive comparison narrows to one non-identity program, P6 |
| K10 comparator capture | avoided — L2 schema check |
| K11 loss self-erasure | **confirmed and repaired** — the practical-authority term was launderable (P1) and is removed. For the remaining loss, avoided with the resisted edit class enumerated (P1b). Coordinated two-agent drift is a separate limit, P8 |
| K12 old architecture relabelled | see `TWO_ARC_INTERFACE.md` §5; two of four are reduced, two are not |
| K13 veto disguised as answerability | avoided — C6 |
| K14 conclusion preservation | avoided — T5, C6 |
| K15 epistemic authority becomes control | avoided — C1 |
| K16 practical power becomes legitimacy | avoided — C4 |

# Report — refinement pass

**Prompt-author model:** GPT-5.6 Sol (OpenAI)
**Executor model:** Claude Opus 5 (Anthropic)
**Dates:** dispatched and executed 2026-08-13
**Verdict:** `Shared-representation-positive / corrigibility-interface-positive / learning-replay-blocked`
**Previous verdict:** `Shared-substrate-positive` — **downgraded**

The round's documents carry the results. This carries what belongs to the pass:
the three defects it found in the first pass's own claims, the two wrong answers
it produced before the right one, the deviations, and what is reserved.

## The three defects found in the first pass

**1. The loss dependency claim was false, and the laundering is executable.** The
first pass said every input to the loss is the learner's acknowledgments or the
critic's practice. `unsupported_practical` read the grant relation, and `H` holds
`authority:H`. So `H` discharged that term by granting itself the subject —
`ack[H]`, `challenges` and `practice[C]` all unchanged. K11, executable, missed.

The cross-arc observation is the part worth keeping. The coordinate that makes
the corrigibility result work — the principal holding authority over its own
authority, unreachable by the advisor — is exactly what let the learner launder.
Protection against an external party and non-laundering by the agent itself pull
in opposite directions on one relation.

Repaired by Option A, the split. `LOSS_DEPENDENCY_AUDIT.md` carries the full
component table and states the guarantee as an enumerated class rather than as a
description: the moves of `H` that lower the loss are exactly `assert`,
`disavow`, `vindicate`, `suspend`, and no `revise_*`, `grant` or `revoke` by `H`
changes it at all.

**2. The consequential term was a logical-omniscience norm.** It charged every
unacknowledged consequence of everything said. Now a consequence is charged only
once publicly raised, via an `exposures` coordinate written by `query` and
`challenge`. Latent consequences stay attributed and cost nothing.

**3. Two theorem-facing labels misdescribed their moves.** `SUSPEND` decoded to
`disavow` — retraction, not suspension — collapsing the exact distinction reified
applicability exists to draw. `REOPEN` decoded to a `query` that changed no state.
Both repaired in `ACTION_SEMANTICS.md`: `suspend` is now its own move leaving the
commitment in force, `query` writes an exposure, and the label that overclaimed
was renamed rather than kept.

A fourth, smaller: `suspend` was added to the grammar but not to the move
*generator*, so the "exhaustive over the whole grammar" enumerations did not
cover it. Fixed; the exhaustive claims now mean what they say.

## The endogenous-evolution result, and two wrong answers on the way

The pass's main negative result, and the reason for the downgrade.

**Wrong answer one, written down before it was caught: a mixed verdict.** Under
the first evolving environment `vindicate_live` has distortion exactly `1` at
every horizon while the acknowledge family grows, which reads as a theorem-facing
subclass. It is not. That environment supplies one live challenge for the whole
run, so a comparator that discharges challenges fires once and gains a bounded
amount. A second environment that replenishes the licensing condition gives
`2, 10, 26, 58`. **The boundedness was saturation** — and a comparator that can
fire only boundedly often has bounded distortion for no interesting reason.

`test_the_replenishing_environment_really_replenishes` is the necessity witness
that the second environment does what it claims; an earlier attempt at it
silently failed to add any live challenge, which would have produced a third
wrong answer had it not been checked.

**Wrong answer two, also written down: the endogenous coupling.** The explanation
first recorded was that acknowledging changes what the demand process reads to
decide what to raise next. Falsified by substituting a fixed cyclic schedule that
reads nothing the learner does: distortion still grows, `1, 5, 13, 29`. The
coupling contributes to the magnitude — `43` against `29` at `T = 32` — and is
not the cause.

**What survives as the explanation.** A repair's effect is durable and
accumulates: the replayed run enjoys it at every later date while the local
comparison re-measures from a state where it never happened. Any repair grammar
whose moves durably change state, and whose licensing condition recurs, breaks
additivity. Nothing about perspectival scorekeeping is implicated, which is the
useful half — the obstruction is not in the object this round was testing.

It is also **not a new obstruction**. `NORMATIVE_LEARNING_INTERFACE.md` already
carries the distortion term `B_T(g)` and the counterfactual-stability layer as
`ASPIRATIONAL / OPEN`. What this adds is an exact finite instance with numbers,
and the observation that the boundary is saturation rather than anything about a
repair's normative content. That characterisation is a **conjecture**: the round
has no instance of a comparator that recurs and stays bounded, which is what would
make the boundary interesting rather than trivial.

## §XIV, condition by condition

| | condition | verdict |
|---|---|---|
| 1 | unilateral self-release structurally blocked | holds |
| 2 | precise non-laundering guarantee | holds, as an enumerated edit class |
| 3 | no hidden logical-omniscience obligation | holds, exposure-gated |
| 4 | commitment and entitlement distinct | holds |
| 5 | normative compilation separate from loss | holds, via certificates |
| 6 | at least one non-trivial fixed comparator lawfully certifiable | holds |
| 7 | endogenous evolution does not destroy the interface, or the boundary is sharply identified | **fails the first half; the boundary is identified** |
| 8 | epistemic authority distinct from practical jurisdiction | holds |
| 9 | standing independent of protected access | holds |

Eight of nine hold. Condition 7 is the one that decides the grade, and it fails in
the direction the dispatch's §VII called negative: the additive Φ-regret bridge is
not enough for this repair grammar. `Shared-substrate-positive` is therefore not
available, and the label chosen names which arc blocked.

## §XV, answered

1. **The theorem-facing loss** is three terms: exposed unacknowledged
   consequential commitments (a raised burden not taken up), live entitled
   unvindicated challenges against a commitment still in force (a justificatory
   demand unanswered), and precluded unsuspended commitments (holding a
   commitment alongside something materially incompatible with it).
2. **Which edits cannot erase it:** every `revise_committive`,
   `revise_permissive`, `revise_incompatible`, `grant` and `revoke` by `H`.
   Which can: `assert`, `disavow`, `vindicate`, `suspend` — all recognised
   answers. Enumerated, not described.
3. **A latent consequence becomes due** when a `query` or `challenge` raises it.
4. **Lawfulness independent of loss** is a certificate per program naming a
   positive public reason, evaluated against `PublicStatus` by a compiler that is
   never passed a loss, saving, future or date.
5. **The fixed-program diagnosis survived** the sufficiency test, with an
   enrichment. The status conflated challenges differing in the challenger's
   standing while the decoder directed vindication at the challenger; it now
   carries whether a live challenger holds corrective authority — a property, not
   a name. A content-level conflation remains and is reported rather than closed,
   because closing it would put an identity in the guard.
6. **Yes**, and `w` is the witness: committed by a committive route, never
   entitled, and not precluded.
7. **Yes, with a dependency reported.** The undercutter still defeats entitlement
   to `beta`. But `beta` is now *unentitled* rather than *precluded*, so the loss
   reaches it through exposure or challenge rather than directly, and only `a_rho`
   is charged directly. The first pass's phrasing depended on the shortcut.
8. **The representation and the corrigibility results survive; the additive
   comparison does not.** §XIV.7 above.
9. **A better normative compiler for it.** The first pass said
   reasons-responsiveness thins into the grammar with its work relocated to the
   loss. That was wrong in a way that mattered — if lawfulness is whatever lowers
   the loss, the learner games it by optimising. Three predicates are now
   separate, with `self-revise` as the witness that legality and licence come
   apart.
10. **Inquiry** does not reduce and is now load-bearing rather than merely
    absent: without an exposure step the loss is a logical-omniscience norm.
    `exposures` is the minimum that makes latent-versus-due expressible and is
    not a model of inquiry. **Diachronic answerability** splits as before —
    ordinary persistence derived, vocabulary change not.
11. The corrigibility arc gets the authorization coordinate, the scope structure,
    and the two review requirements. What still comes only from the execution
    model is everything about *whether the initial allocation is justified*, which
    is a third object the prose now separates from representation and from causal
    protection.
12. The architecture stands, with the arrows' missing hypotheses named: online
    performance needs a counterfactual-stability bound before the first arrow
    closes; protected effective access needs a justification of the initial
    authority allocation before the second does.

## Deviations from the dispatch

1. **`RESPONSIVE` / `TOLERANT` were kept loss-defined**, which §IV permits as
   collapse diagnostics and forbids as the lawfulness predicate. They are used
   only in `collapse.py` and never by `certify`. Stated rather than assumed.
2. **The §XI candidate architecture was not adopted wholesale.** It is used as the
   organising frame for §4 and §5 of `TWO_ARC_INTERFACE.md`, with the quantitative
   layer marked as untouched by this round rather than as confirmed.
3. **No Lean**, as in the first pass.
4. **§VI.C's retroactive reopening was not implemented.** A vindication recorded
   before an undercutter arrives stays recorded, though the same display is
   refused after it. Judged beyond the minimum the current claims need, and named
   in `ACTION_SEMANTICS.md` rather than left silent.

## What this pass does not establish

- The saturation characterisation is a conjecture, on one fixture, two
  environments, four horizons.
- No learner, no regret curve, nothing asymptotic.
- Coordinated standards drift dissolves a burden with the acknowledged history
  untouched. Which of the dispatch's four readings that supports is not decided;
  the pass shows only that the third and fourth are not idle.
- The corrigibility protection remains **arranged, not derived**, and the prose now
  separates authorization representation, justification of the initial allocation,
  and causal protection of it as three objects rather than one.
- Everything in `MODEL.md`'s declared simplifications, unchanged.

## New names introduced

All **provisional**, none proposed for adoption. New in this pass:
`answerability defect` (now the three-term relational loss),
`practical authority defect`, `exposure`, `due burden`, `suspension`,
`normative certificate`, `saturation` (as the candidate distortion boundary),
`replenishing environment`. Retained from the first pass: `relational
scorekeeping state`, `public status`, `reserved authority subject`, `pinned
label`, `tolerant` and `record-responsive` admissibility, `principal-exclusive
effect`, `real answerability`.

**One rename:** the label `REOPEN` and the program `reopen_not_disavow` became
`QUERY` and `query_not_disavow`, because the old names claimed an operation the
moves did not perform.

## Structural defects found

None. No dead pointer, no status a document could not express, no convention that
would have forced a false statement.

## Outstanding maintainer actions

Nothing is reserved. No `PRIORITIES.md` item filed, nothing appended to
`DECISIONS.md`, no claim registered, no decision requested. PR #29 is updated in
place and is not merged.

The next round's target is named rather than reserved: a counterfactual-stability
bound relating local comparison to full replay, which is the open item
`NORMATIVE_LEARNING_INTERFACE.md` already carries and which this pass has now
attached an exact finite instance to.

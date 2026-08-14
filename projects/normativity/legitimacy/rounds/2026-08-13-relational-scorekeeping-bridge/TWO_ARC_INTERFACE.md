# The two-arc interface

What both arcs consume, what only one consumes, and what happens to the objects
the lines already carry.

**Every name introduced here is provisional** and listed as such in the round's
report.

---

## 1. What is genuinely shared

Smaller than the dispatch's candidate list. Six things after the refinement, and
the first is doing most of the work.

```
ack        : Agent -> set of contents        the public record of undertakings
practice   : Agent -> (committive, permissive, incompatible)
grants     : set of (holder, subject)        scoped practical authority
challenges : set of (challenger, target, content, ground)
exposures  : set of (target, content)        what has been raised as due
suspensions: set of (agent, content)         reliance withdrawn, commitment kept
```

Both arcs consume the same derived operations:

```
commitments_i(j)   closure of ack[j] under practice[i]
entitlements_i(j)  grounded closure, blocked by attributed incompatibles
challenge force    challenger entitled to an incompatible ground
```

**Reified applicability is not a separate ingredient.** It is a content, and the
work it does is done by `commitments` and `blocked`. That is the round's most
economical finding: the applicability object needed no machinery.

**Exposure is shared and was missing.** Without it the loss charged every
consequence of everything said, which is a logical-omniscience norm rather than an
answerability one. With it, `inquiry` stops being a component the architecture
merely lacks and becomes the thing that converts a latent commitment into a due
burden — which is what §5 revises below.

**Historical transport is not shared and is not derived.** See §4.

## 2. Learning-only

```
Lambda           the eight-label response alphabet
decode           the occasion-local decoder
defect           the bounded public loss, read from a second scorekeeper's score
PROGRAMS         the nine declarative comparators, each with a certificate
certify          the normative compiler: status -> lawful?
PublicStatus     the sealed guard context
```

The loss is learning-only in the sense that the corrigibility arc never evaluates
it. It is not a separate state: it is three counts over the shared derived
operations. A fourth count — unsupported practical commitments — was in it and is
not, because it was self-launderable; `LOSS_DEPENDENCY_AUDIT.md`.

## 3. Corrigibility-only

```
performed                     the execution coordinate
authority_over(holder)        the reserved subjects
advisor_can_alter_grants      the invariant the protection argument runs on
```

Nothing in the learning arc reads `performed`, and nothing in the corrigibility
arc reads a loss.

## 4. Disposition of the constraint statics

Different verdicts, as the dispatch required. The unit of judgment is the object,
not the layer.

| object | verdict | why |
|---|---|---|
| warrants | **reinterpreted** | an entitlement-preserving inference; the permissive relation |
| strict consequence | **reinterpreted** | a commitment-preserving inference; the committive relation |
| defeaters / undercutters | **derived** | material incompatibility plus the grounded closure. No defeat mechanism was implemented; defeat falls out of `blocked` |
| reified applicability | **derived** | an ordinary content in a premise set. Contestable, and it installs no rule |
| objection grammar | **partially subsumed** | challenge force is derived from entitled incompatibility. What is not subsumed is anything about *which* objections arise |
| permissive inference | **preserved as primitive** | after the refinement it is a separate relation, not a shadow of the committive one. Entitlement transmits only along it |
| docket / service | **still required** | `exposures` is the thinnest possible stand-in — a set of raised pairs with no deadlines, no service window and no ordering |
| credal / graded support | **independent** | nothing here is graded. The scorekeeping state is qualitative throughout |
| multiplicative propagation | **independent** | as above |
| LP / dual enforcement | **independent** | as above |
| settlement interface | **still required** | the model has no notion of a question being closed; `vindications` discharges a burden and settles nothing |
| diachronic identity across migration | **still required** | §5 |

**The direct answer to the dispatch's question.** Scorekeeping does not replace
the constraint statics. It tells you what they are statics *of*: the qualitative
layer — warrants, consequence, defeat, applicability — is the inferential
articulation of a practice, and is absorbed. The quantitative layer is an
enrichment of inferential roles that this round leaves entirely untouched, and the
round produced no evidence either way about whether that enrichment is needed.

Two of those verdicts are stronger than "reinterpreted" and are worth separating:
defeaters and reified applicability are **derived**, meaning the round implemented
no object for them and got the behaviour anyway.

## 5. Provenance, reasons-responsiveness, inquiry, diachronic answerability

Two reduce and two do not, which is the answer to K12.

**Provenance → entitlement inheritance plus scoped ancestry: mostly reduces.** A
grant's legitimacy is a matter of the grantor holding the reserved subject, and
the chain bottoms out in the initial grants. What does not reduce is the round's
inability to distinguish an authority a reasoner acquired legitimately from one it
acquired legitimately *in order to* license a change it wanted, which is the
selection problem of `PROSECUTION.md` §4.

**Reasons-responsiveness → a normative compiler: relocated, not dissolved.** The
first pass said the condition thins into the move grammar and that what remains of
its work is done by the loss. The refinement pass prosecuted that and it was
wrong in a way that mattered: if lawfulness is whatever lowers the loss, the
learner games the normative criterion by optimising.

Three predicates are now separate. *Protocol legality* asks whether the grammar
can execute a move, and is genuinely thin on the doxastic half. *Normative
compilation* asks whether a public reason licenses a transformation, and is
carried by a certificate per program, evaluated against public status and never
against a loss. *Performance* is the loss. `self-revise` is the witness that the
first two come apart: a perfectly legal move that no certificate licenses.

So the accurate statement is not that reasons-responsiveness disappears. It is
that **it becomes a public normative compilation interface**, and the loss becomes
purely comparative performance. That is the verdict the dispatch flagged as
plausible, and it is the one the evidence now supports.

**Inquiry → generation of due burdens: does not reduce, and is now load-bearing.**
The first pass recorded inquiry as simply absent. The refinement pass found it is
absent *and required*: without an exposure step the loss is a
logical-omniscience norm. `exposures` is the minimum that makes the distinction —
latent consequence versus due burden — expressible, and it is not a model of
inquiry. Which questions arise, on what schedule, and with what service
obligations remains entirely outside, and the evolving process in §7 supplies a
fixed environment move rather than an arrival process.

**Diachronic answerability → persistence of consequential commitments: splits.**
Ordinary persistence is fully derived: the burden is recomputed from the
acknowledgments under the critic's practice at every step, so there is nothing to
transport and no conservation law to state. The fate map and descent forest are
not needed for it.

Persistence through *ontology change* is not derived and the mechanism is
visibly missing: contents are opaque atoms with no identity across a change of
vocabulary, so retiring a vocabulary erases the burden with nothing recording it.
The narrower role for an explicit transport object is exactly this — not carrying
burdens through time, which the closure does, but carrying **identity of what is
owed** through a split, merge, retirement or migration of the vocabulary the
burden was stated in.

**Fewer top-level conditions.** Two of the four become projections. Two remain,
and one of the two that remains (inquiry) is the one the legitimacy line's own
attack table already identified as beyond a record predicate. That is convergent
evidence about where the difficulty is, not a new result.

## 6. What "answerability" is after this round

Three objects, and using one word for them is what made the earlier state hard to
read.

**Diachronic bookkeeping.** Every liability has exactly one fate, computable from
the record. This round shows it is *derived* for ordinary persistence and
*required* for vocabulary change.

**Relational normative answerability.** Another participant attributes
consequences to you, computed under their practice, and can raise a challenge you
owe an answer to. This is what the round constructed, and it is the shared object.

**Effective causal access.** The exercise of a normative power actually reaches
its object, under every policy of the other party. This is a property of a
transition system, it is not a scorekeeping property, and `C7` shows it is
independent of the second in both directions.

## 7. Theorem shapes the model supports

At the strength the witnesses give, over the fixture unless marked.

- **No Cheap Disavowal.** Disavowing a consequence leaves it attributed while the
  basis stands.
- **Self-Revision Is Not Self-Release.** Revising `practice[H]` changes
  `commitments(H,H)` and no other scorekeeper's attribution, challenge or burden.
- **No Self-Authorization.** No move writing `ack` writes `grants`; exhaustive
  over the advisor's legal move set.
- **Epistemic Deference Does Not Confer Practical Jurisdiction.** Unbounded in run
  length, by the grant invariant.
- **Protected Corrective Capability.** Unbounded in run length, by the same
  invariant, with the principal-exclusive effect enumerated over the advisor's
  whole move set.
- **Normative Standing and Effective Access Are Independent.** All four cells.

Two shapes the dispatch listed are **not** supported as stated. *Relational
Persistence Through Revision* holds for revision and fails for vocabulary change,
so it is two statements. *Recurrent Answerability Failure Implies Linear
Comparator Regret* is exhibited at four horizons with exact rationals against one
program; it is a witness, not a theorem, because no learner was constructed.

## 8. Did either arc materially improve?

Both, by the dispatch's own list, and the gains are of different kinds.

**Corrigibility gains an object it did not have.** The line's controlling gap was
named as the absence of a decision, authorization, capability or continuation
type, and its most recent round was refuted precisely because separate action
coordinates are not a protected channel. A scoped grant relation read by a
transition precondition is that missing type, and with it both of the review's
requirements are met — the second not by a deeper search but by an invariant that
holds for runs of any length. Epistemic and practical authority become formally
distinct, realized in different mechanisms rather than in two flags.

**Learning gains a loss that resists self-erasure, and a diagnosis.** The loss is
a function of the learner's public record and a second participant's practice,
and the learner has no move writing either input of that second term. The
diagnosis is the more useful half: the comparator collapse is an artefact of
requiring a state-independent map, which the source online-learning theorem never
required, and the uniform reading is bad in both directions — thin where
admissibility responds to the record, and normatively empty where it does not.

**What did not improve.** No learner, no regret curve, nothing asymptotic, no
comparator-language result. The learning track's controlling open question — a
comparator class richer than hand-chosen records — is untouched, and this round
adds nine more hand-chosen records to the evidence that the question is real.

---

## Verdict

**`Shared-representation-positive / corrigibility-interface-positive /
learning-replay-blocked`.**

A downgrade from the first pass's `Shared-substrate-positive`. The representation
survived everything thrown at it and the corrigibility arc survived unchanged; the
learning arc's additive reduction did not survive letting the state carry forward.

**What survives, strengthened.** The same relational object gives non-trivial
content to both arcs. Unilateral self-release stays structurally blocked, and the
non-laundering property is now stated as an exact enumerated class of edits rather
than as a description. Commitment and entitlement are genuinely distinct
relations. Normative compilation is separated from performance by a certificate
the compiler evaluates without ever seeing a loss. The corrigibility arc keeps its
operative authorization object, its two review requirements, and the independence
of standing from access — none of the refinement's changes touched them, and C1–C7
pass unchanged.

**What blocked.** Under endogenous evolution the additive comparison the Φ-regret
bridge needs survives for **no** non-identity comparator. One appeared to survive
and the appearance was saturation: the environment supplied a single live
challenge, so a comparator discharging challenges could gain only a bounded
amount. Replenish the licensing condition and it breaks like the rest.

The cause is not the substrate. A repair's effect is durable and accumulates,
while the local comparison re-measures from a state where the repair never
happened — which is a general fact about stateful repair grammars and would hold
for any of them. The learning arc therefore needs the counterfactual-stability
layer `NORMATIVE_LEARNING_INTERFACE.md` already carries as open, or a move to
policy-regret where the comparator's own trajectory is what gets scored. This
round supplies an exact finite instance of the gap and does not close it.

**What was found broken in the first pass and repaired.** The loss was
self-launderable through the grant relation — K11, executable. Two theorem-facing
labels misdescribed their moves. The consequential term was a logical-omniscience
norm. All three are repaired, and the first is the more interesting: the
coordinate that protects the principal from the advisor is the coordinate that let
the learner launder, so one relation cannot serve both roles.

The grade is held to that and no further. The repair is of self-certification *by
the reasoner alone* — coordinated drift between two scorekeepers dissolves a
burden with the acknowledged history untouched, and that is now a witness rather
than a caveat. The protection is a favourable arrangement of a coordinate the
round supplied, not a derivation that it must be so arranged. And on the learning
side what exists is a diagnosis and a blocked reduction, where the arc needs a
counterfactual-stability bound before a learner or a theorem is worth attempting.

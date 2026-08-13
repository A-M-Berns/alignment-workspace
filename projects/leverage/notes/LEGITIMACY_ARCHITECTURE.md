# The legitimacy architecture

**Status: consolidated view, `ci-only`. Provisional terminology throughout** —
*normative constraint*, *diachronic answerability*, *record legitimacy*,
*endpoint legitimacy*, *ground provenance*, *filing gap*, *constraint core*,
*comparator collapse*. What these are finally called is the maintainer's.

A reader who has read nothing else in this line should be able to state the
program from this document. The abstract theory is §§2–6; the finite models that
witness it are named as models and are not the theory. What is proved, checked,
conjectured or open is in §7 and in
`rounds/2026-08-12-legitimacy-architecture/THEOREM_MAP.md`, which carries the
derivations.

---

## 1. The problem

Empirical facts, reasons, warrants, commitments and defeaters are supposed to
bear on normative propositions, which do not settle against ground truth the way
factual ones do. The question the program starts from is how that bearing can be
made numerical or decision-relevant rather than gestural.

The question it has arrived at is narrower and sharper:

> What makes a trajectory of a bounded reasoner legitimate, and when does
> movement through the space of legitimate trajectories constitute learning?

The shift matters because it changes what a theorem is about. The first question
asks for a relation between reasons and conclusions. The second asks for a
relation between a reasoner's history and its present state — and that is where
the results are, because it is where accountability lives. A reasoner can always
be made to look correct at a moment; what it cannot easily be made to look is
answerable across a change of standards.

## 2. Core objects

Four, and nothing else is primitive.

**State.** `x = (commitments, standards, vocabulary, ledger, cost)`. The
reasoner's substantive positions; the applicability machinery saying which kind
of ground may reach which coordinate; the conceptual repertoire; the identified
demands it owes answers to; and what it has paid. Standards and vocabulary are
**coordinates of the state**, not a background — the single decision on which the
whole architecture turns.

**Reason context.** `r` — the grounds on the record, read at a date. Reading is
date-relative by construction, so a ground filed later is invisible rather than
inadmissible.

**Constraint.** `Gamma(x, r)` — the admissible successors.

**Liability.** An identified demand with an opaque identifier. Opacity is a
hypothesis with work to do: it is what lets a demand survive the retirement of
every word it was first stated in.

Two derived objects carry the results. The **record** is everything a legitimacy
verdict is a function of. The **fate** of a liability is where the record says it
ended up, and what backs the ending.

## 3. Normative constraint theory

`Gamma` is presented as a decision rather than a set, because its structural
properties are properties of the decision:

- **non-emptiness** — the no-op is always admitted, so the legitimate
  trajectories are not accidentally empty;
- **availability-monotonicity** — more record admits weakly more, which is what
  makes a later licence not a retroactive one;
- **standards-mediated scope** — a ground reaches a coordinate only if the
  state's own standards let a ground of its kind reach it;
- **cost-blindness** — the decision reads a declared footprint and accrued cost
  is not in it, so licensing cannot be a function of what a move saves.

The verdict is three-valued. `unresolved` is reserved for the question whether
directional support licenses a particular endpoint magnitude; answering it by
rejecting would be answering it.

**What the former statics results become.** Constraint propagation is the credal
interval machinery: what the endorsed region and the settled record jointly force
on a target. Strength of constraint is the credal interval's width and the
incoherence functional. Feasibility under constraint is the per-date linear
program of `NL-SI-A3`. Enforcement of constraint is the settlement interface —
reports, timing, enforcement, the core minimum, the downside limit. These are
statics; none of them says anything about a trajectory.

## 4. Reasons-responsiveness

    x_{t+1} in Gamma(x_t, r_t).

It ranges over belief change, commitment change, standards change and vocabulary
change alike, because all four are coordinates. It is not binary: a step is
admitted, refused, or uncertified.

The existing certificate machinery witnesses it. The nine checks of the finite
substrate are the availability, defeat, scope, connection, magnitude, burden,
ratification and footprint clauses, with three parametric relations left as named
policy functions.

**Arbitrary changes to the standards satisfy the naive condition.** With the
reasoner's own machinery outside the coordinate structure, a trajectory that
widens the standard judging it and then closes the objection under the widened
standard is fully responsive. That is why the reflexive reading is the condition
and the naive one is not.

**The constraint does not compose**, in two ways. A declared magnitude allowance
is compared against a step's movement and is never spent, so one bounded
impediment cited at `n` dates licenses `n` times its allowance — every step
admitted, the composite refused. And a later step may be licensed by standards an
earlier step installed. The first is a defect with an obvious repair
(consumability); the second is not a defect (§6).

## 5. Diachronic answerability

Each transition supplies a disposition for every live liability, in one of seven
modes: carry, refine, identify, suspend, reinstate, discharge, lose. The
condition is that the disposition map is total; that terminal modes carry their
backing — an adequacy witness for a discharge, an authorization *and* a
disclosure for a loss; that suspension does not close and carries a route; that
identification is licensed; and that descendants are fresh.

**Conservation.** Under the condition, every liability live at the start has
exactly one fate at the end: live descendants, a backed terminal disposition, or
a routed suspension. The fate is computed by folding the record, and it composes
— the fate of a concatenation is fixed by the first segment's fate and the second
segment, so the audit at the endpoint needs no replay.

**Non-laundering.** A change of representation alone never terminates a
liability. This does not require preserving any vocabulary; it requires liability
identity to be independent of vocabulary, which is a design decision about
identifiers rather than a constraint on conceptual change.

This is a conservation law over normative history, and the frozen consolidation
proves its concrete form: `AL-J1`, `AL-J3`, `AL-J4` for the ledger; `ST-J1`,
`ST-J2`, `ST-J3`, `ST-N3` for transport across versions; `AM-J3`, `AM-J4`,
`AM-X10`, `CM-J1`, `CM-J2` for migration and its composition. The abstraction's
contribution is not these theorems; it is that they are the diachronic half of a
legitimacy condition rather than results about identity.

## 6. Legitimate trajectory — the candidate definition

    tau is record-legitimate  iff  every step is reasons-responsive
                              and  tau is diachronically answerable.

**What it gives.** At `x_T`, from the record alone: for every liability live at
`x_0`, its fate and the backing of that fate; and per-step certification relative
to the reasons available at each date.

**What it does not give, deliberately.** That `x_T` is admissible from `x_0`. The
trajectory that retires a vocabulary, refines its demands into the new one,
widens its own standard and reverses its verdict is legitimate, and its endpoint
is refused by its own initial constraint. A condition requiring the start to
endorse the end would forbid the conceptual improvement the framework exists to
license. What survives across the transformation is not endorsement of the
conclusion but the traceable fate of every demand — **process trust rather than
conclusion endorsement**, in a precise form.

**What it does not give, as a defect.** The conjunction is not sufficient. Two
conditions are missing, and they are different in kind:

- **Ground provenance.** No clause reads who filed a ground. A move the
  constraint refuses is admitted after one filing, and the reasoner may do the
  filing. Standard laundering and defeater laundering both come back through this
  door.
- **Coverage.** Both conditions quantify over what is on the record, and a demand
  that was never docketed is not. An advisor controlling what becomes salient
  faces no obstacle from either.

So the working equation is

    legitimacy = reasons-responsiveness + diachronic answerability
                 + ground provenance + coverage,

with the first two constructed, the third named but undefined, and the fourth
defined against a declared arrival process.

**Where this framing comes from.** The legitimacy programme is the deference
line's: `projects/deference/note-dump-2026-08-11/notes/li-deference.md` §0.3
identifies the legitimacy of feedback as the missing object, and
`.../notes/legitimacy-theory-v1.md` §2.3 states the principle that in a coupled
system every safety-relevant boundary is a fact about where a value came from and
never about what the record says, with its §3 classifying trace conditions as
provably empty. The ground-provenance condition below is that principle one level
down — provenance of *reasons* rather than of beliefs — and is the third
independent instance of it the workspace has recorded, after the two adjudicated
in `projects/deference/rounds/2026-08-12-corpus-reconciliation/RECONCILIATION.md`.

**The second sense of the word.** The deference corpus uses *legitimacy* for a
different condition: an advisor's influence is legitimate when it changes the
rate at which the reasoner's deliberation converges and not the endpoint it
converges to. The two senses are independent, and provably so. Record legitimacy
is a function of the record; the corpus's kernel-checked non-recoverability
result exhibits a faithful and a fully steered run with the same record, so no
record predicate separates them. Both senses are live and both are needed; where
either could be meant, say which.

## 7. Theorem and conjecture map

| statement | status |
|---|---|
| the four structural properties of `Gamma` | checked in the model; the reading against the substrate's checks is a reading |
| the naive local condition admits standard laundering | witness |
| the constraint does not compose (allowance non-consumption; standards bootstrapping) | witness |
| composition under constant standards, date-0 availability, one movement per magnitude coordinate | conjecture |
| conservation: exactly one backed fate per liability | derivation, with its case analysis exhaustive over `343` mode sequences; refuses `316` of them when the backing is stripped |
| non-laundering under representation change | exhaustive over the same sweep with vocabulary churn |
| fate composition without replay | exhaustive over `2401` segment pairs |
| both conditions are functions of the record | derivation by construction, plus the latent-pair witness |
| record legitimacy does not detect endpoint corruption | derivation from the above plus the corpus's `gate_blind` |
| transformative change is permitted | witness |
| the filing gap | witness |
| coverage is independent | witness |
| the comparator core formula and its collapse condition | derivation, exhaustive over `512` families |
| the decoder obligation for an online-learning theorem | open |
| the corrigibility composition | conjecture |

## 8. Normative learning

Legitimacy says which changes are permissible. Learning says whether the reasoner
improves through that permissible space. The extension is legitimacy, plus
coverage, plus an online performance criterion — and the three are independent:
there are trajectories legitimate and covering that pay four times the charge of
an available legitimate alternative, and there are illegitimate trajectories that
attain the *same* charge as the best legitimate one. At its optimum the
performance criterion does not discriminate legitimacy at all.

The comparator class the abstraction suggests is the maps of the response space
carrying admissible responses to admissible responses, uniformly along the
trajectory. It has an exact description: such a map must send each response into
the intersection of every admissible set containing it, so the class is a product
of those intersections. **It is the identity alone exactly when the admissible
sets pin down their own elements** — which is what a constraint that responds to
the record does. Regret against the uniform legitimacy-preserving class is
therefore vacuous on any trajectory whose constraint separates responses.

The class with content is state-indexed: a rule is a map from (public state,
response) to response, which is what the nine declarative programs of the
constructed finite learner already are. Its cost is that legitimacy-preservation
becomes a per-state condition, so certifying a comparator means running the
constraint wherever the comparator could apply.

What an online-learning theorem needs from this layer is therefore a decoder from
occasion-local responses to a fixed finite response space under which the decoded
constraint is date-independent. Constancy of the decoded constraint is what makes
a fixed-action reduction apply, and it is what empties the comparator class. That
tension is the controlling open question of the learning track.

## 9. Relation to Logical Induction

They constrain different things, and the difference is representational rather
than a matter of strength.

Logical Induction bounds a price sequence: no efficiently computable trader
exploits it unboundedly. Its record is prices, trades and settlements. It has no
object for a demand that is owed an answer, no authorization column, and no
notion of a move being licensed by a ground — so no logical-inductor property
implies reasons-responsiveness, and its bookkeeping conservation is over trades
rather than over obligations. In the other direction, the deference line's
static-view factorization result says a valuation over price and realization
cannot distinguish who authorized an action, which is precisely the column a
backed disposition requires.

The reading the mathematics supports: the legitimacy layer is **substrate-
independent**, defined over a record containing grounds, dispositions and
authorizations; a logical inductor is one possible supplier of the commitments
coordinate, and the settlement interface is one possible supplier of exogenous
grounds. Implementing legitimacy as a constraint *on* an inductor is not
available without first enlarging its record, and enlarging its record is the
open work rather than a modelling choice.

What remains relevant from the constrained-marketmaker and underwriting work is
the statics: the settlement interface says what makes a constraint bite — who
writes, when, and with what weight standing behind it — and the core minimum and
downside limit are the enforcement terms. That is orthogonal to what makes a
transition licensed, and keeping them apart is one of the reorganization's
clearer gains.

Whether the eventual learning theorem should be derived from Logical Induction or
from ordinary online learning is **not settled by anything here**. The one
constructed result is ordinary-online-learning-derived, and the obstruction the
abstraction exposes is representational, which suggests the choice of learning
engine is not where the difficulty is.

## 10. Deference and corrigibility interface

The deference problem has a less capable reasoner `H`, an advisor `A`, and
trajectories in which interaction with `A` changes `H`. Endpoint endorsement is
self-certifying: `A` may alter `H`'s standards so that the resulting state
endorses a transformation the prior trajectory would not have licensed.

**What the legitimacy layer exposes.** The state space and constraint
`(X, Gamma)` with its footprint; the ledger and the disposition map; the fate
fold; the record; and the ground-provenance partition, carried but unread.

**What it certifies about an `H`-trajectory.** Every demand live at `H_0` has, at
`H_T`, exactly one fate with its backing named, computable from the record
without replay; every transition was certified against the reasons available at
its own date; and no demand was removed by a change of representation,
bookkeeping, or standard.

**What composes from `H_0` to `H_T`.** The fate map, and only the fate map.
Admissibility does not compose, and should not: requiring it would forbid
legitimate transformation.

**What deference must add.** A counterfactual condition. Record legitimacy is a
record predicate, and the corpus's non-recoverability result exhibits a faithful
and a steered run with equal records; so steering cannot be excluded by any
strengthening of the two conditions. The corpus's own candidate — an
endpoint-preservation certificate, published by the advisor and settled against
the sealed counterfactual, grounded in a blind target so the audit does not eat
its own tail — is the shape of the missing hypothesis.

**Candidate statement (conjecture).**

> Let `tau` be an `H`-trajectory that is record-legitimate and covering, and let
> `A` supply an endpoint-preservation certificate whose defect is bounded on the
> family in question. Then `H_0` has grounds to trust `H_T` as a continuation:
> every demand `H_0` held is answerable at `H_T` with named backing, and the
> advisor's contribution to `H_T`'s positions is bounded by the certificate.

The first conjunct is proved here in its finite form. The second is entirely the
deference layer's, and the composition of the two has not been attempted.

**Relation to the trust condition already in the workspace.** The deference line
works in the tradition of *Deference Done Better*, where trust is weak
endorsement and the working formalizations are the tower, Total Trust and Value,
with `Value <=> Total Trust` by the two-option witness and domain-relative. Those
are conditions on a *valuation*: what the novice's estimates must satisfy given
the expert's. Record legitimacy is a condition on a *history*: what the record
must show about how a state was reached. They take different arguments, so
neither is a strengthening of the other, and combining them is addition rather
than refinement.

One structural echo is worth recording. That line's D12 conjectures that trust is
not transitive under delegation, recoverable only under an observability
condition. The constraint here is likewise not transitive, and its two failure
modes — an allowance that is never spent, and a later step licensed by standards
an earlier step installed — are of the same shape: a property that holds at each
link and not along the chain, with the repair in both cases a condition on what
the intermediate step is allowed to supply. Whether the two non-transitivities
are instances of one fact is unexamined.

**Manipulation ruled out by the two conditions.** Struck obligations; obligations
discharged on someone else's warrant; silent merges of two demands onto one
answer; retroactive ratification; erasure by retiring a vocabulary; licensing
that depends on what a move saves.

**Manipulation that survives.** Steering with impeccable books; controlling which
demands ever arise; producing a defeater for every inconvenient reason; and
supplying the ground that licenses the change to the standard. The last three are
the filing gap; the first is the counterfactual gap.

## 11. Counterexamples and limitations

The prosecution is in
`rounds/2026-08-12-legitimacy-architecture/PROSECUTION.md` with its verdicts and
the tests that decide them. The four that constrain how the architecture may be
described:

- a trajectory legitimate under the naive local condition that launders its own
  standard;
- a legitimate trajectory that launders its standard anyway, by filing the ground
  that licenses it;
- two legitimate trajectories with identical records and influence defects `0`
  and `1/2`;
- a constraint family on four responses whose legitimacy-preserving comparator
  class is the identity alone.

Limitations: no Lean; one occasion, two substantive coordinates, at most four
liabilities, horizons of at most four dates; the parametric normative relations
are represented by weaker defaults than the substrate's; the ground-provenance
repair is named and unimplemented; nothing asymptotic.

## 12. Open mathematical obligations

1. **A decoder under which the decoded constraint is date-independent**, or a
   proof that constancy and non-collapse are incompatible. This decides whether
   the online-learning target can be stated at all in the uniform form.
2. **The composition conjecture for the constraint**, and the consumable-allowance
   repair that its first hypothesis calls for.
3. **A definition of ground provenance** that a clause can read, and the version
   of the local condition that reads it — with the necessity witness that it does
   not simply forbid the reasoner from ever filing anything.
4. **Coverage against a generated arrival process** rather than a declared one,
   which is where an advisor controlling what *arises* would have to be caught.
5. **The corrigibility composition** of §10.
6. **Lean ports** of the conservation and comparator-core statements, which are
   both short and both currently rest on Python.

## 13. Where each part lives

| part | artifact |
|---|---|
| statics: objection grammar, credal constraint, migration, transport, ledger, settlement interface | `consolidation-aug9/`, cited by claim identifier |
| the local certificate interface | `rounds/2026-08-11-phi-regret-prep/REASONS_RESPONSIVENESS_INTERFACE.md` |
| the fixed-action representation and its nine programs | `rounds/2026-08-11-phi-regret-bridge/` |
| the constructed learner and its integration audit | `rounds/2026-08-11-phi-regret-learner/` |
| the negative applicability audit | `rounds/2026-08-11-phi-regret-applicability/` |
| the abstract conditions, prosecution and comparator analysis | `rounds/2026-08-12-legitimacy-architecture/` |
| the learning-track routing note | `notes/NORMATIVE_LEARNING_INTERFACE.md` |
| the second sense of legitimacy, and non-recoverability | `projects/deference/note-dump-2026-08-11/` |

The finite constructions are **models**: proof laboratories, witnesses and
countermodels. None of them is the theory, and the reorganization's practical
effect is that they can now be cited as instances of a stated condition rather
than as the condition itself.

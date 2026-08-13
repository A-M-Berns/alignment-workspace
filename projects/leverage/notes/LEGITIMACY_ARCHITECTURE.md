# The legitimacy architecture

**Status: consolidated view, `ci-only`. Provisional terminology throughout** —
*normative constraint*, *provenance*, *inquiry adequacy*, *diachronic
answerability*, *record legitimacy*, *endpoint legitimacy*, *disclosure*,
*substantive drift*. What these are finally called is the maintainer's.

A reader who has read nothing else in this line should be able to state the
programme from this document. The abstract theory is §§2–7; the finite models
that witness it are named as models and are not the theory. Derivations and
scopes are in the two rounds' `THEOREM_MAP.md` files.

---

## 1. What procedural legitimacy is

A bounded reasoner revises not only its beliefs but the machinery that judges
them: which considerations count, what its words mean, what settles a question,
and which questions it owes an answer to. The programme asks what it takes for
such a trajectory to be honest, given that the propositions being revised do not
settle against ground truth.

**The target.** A trajectory is procedurally legitimate when the reasoner
confronts the demands it is entitled to confront, exercises only authority that
was actually conferred, uses reasons only where they actually bear, and closes a
demand only on something that actually settles it.

The four "actually"s are load-bearing and are what make this a target rather than
a definition of compliance. Stated in full against an environment — what was
granted, what bears, what arises, what settles — in
`rounds/2026-08-13-procedural-legitimacy/L_STAR.md`.

**Two readings, and the whole architecture turns on which is meant.** On the
*reasoner-relative* reading, "actually" means "by the reasoner's current
machinery". On the *environment-relative* reading it means what it says. The
conditions below are close to sufficient for the first and refuted for the
second.

## 2. Core objects

**State** `x` — commitments, and the machinery that judges them: the bearing
relation, the adequacy relation, the inquiry-generation rule, the entitlement
rule, and the liability ledger. The machinery is *coordinates of the state*, so
revising it is a transition like any other. That decision is what gives the
conditions their teeth and, as §8 shows, is also where they run out.

**Ground** — a reason on the record, carrying content, a scope, and a basis: the
grounds it was derived from. Content and scope obey different rules, which is the
whole of §4.

**Constraint** `Gamma(x, r)` — the admissible successors, given a state and a
reason context.

**Liability** — an identified demand, with an opaque identifier and a set of
substances. Opacity lets a demand survive the retirement of every word it was
first stated in; the substance set lets a merge be adjudicated.

## 3. Normative constraint theory — the statics

`Gamma` is a decision, not a set, because its structural properties are
properties of the decision: the no-op is always admitted; more record admits
weakly more; a ground reaches a coordinate only if the state's standards let a
ground of its kind reach it; and the decision cannot read cost, which in the
current model is enforced by there being no cost coordinate at all.

The verdict is three-valued. `unresolved` is reserved for whether directional
support licenses a particular magnitude; answering it by refusing would be
answering it.

The former statics results sit here unchanged: credal intervals and incoherence
are the strength of constraint, the per-date linear program is feasibility, and
the settlement interface — reports, timing, enforcement, the core minimum, the
downside limit — is enforcement.

## 4. Provenance

`Pi_t(g, c)`: ground `g` may bear on coordinate `c` at date `t` when its basis
graph is well-founded, every root was conferred by an external source, every
derivation step satisfies `scope(child) subset bound(parents)`, every basis is
strictly earlier, `g` is undefeated, and `c` is in its scope.

**Not external-good, internal-bad.** A bounded reasoner must produce reasons
itself. The condition splits two things that were being run together: **content
is free and scope is not**. Any ground may assert anything; a derived ground's
jurisdiction is bounded by its parents'. So the reasoner may manufacture reasons
and may not manufacture authority, and inference, proof, conceptual innovation
and genuine defeaters are all unobstructed.

**No amplification.** A provenance-valid ground's scope is contained in what its
roots were granted — a short induction along the basis DAG. Long-chain laundering
and circular authorization are both defeated, and the same chain without its
amplifying link is admitted, so the condition refuses the amplification rather
than the derivation.

**Unresolved.** Whether a child of two parents is bounded by the union or the
intersection of their scopes. The union gives it joint jurisdiction neither
parent had; the intersection may be too strict. Which is right depends on whether
the constraint being licensed is coordinate-wise or joint, and nothing in the
condition decides it.

## 5. Inquiry adequacy

Not coverage against a declared list — an advisor controlling the list makes that
vacuous. Three parts:

    encounter --generation--> inquiry --entitlement--> owed service --> docket or backed refusal

Generation and entitlement are **state coordinates**, so revising them is
governed by provenance and reasons-responsiveness. Service is bounded by a window
and a capacity, and **docketing creates a liability**, which is how this condition
connects to answerability rather than sitting beside it.

Entitlement is read **at the date the inquiry was generated**. That single clause
defeats withdrawing entitlement from a question already raised; reading it at
service time instead lets the same trajectory through.

Flooding the docket is self-defeating: with deadlines, burying one question under
many means missing them, and the flooder is refused.

## 6. Diachronic answerability

Each transition disposes of every live liability: carry, refine, identify,
suspend, reinstate, discharge, lose. Terminal modes carry backing — an adequacy
witness for a discharge, an authorization and a disclosure for a loss; suspension
carries a route and does not close.

**The conserved object is a forest.** After `l -> {l1, l2}` with one branch
discharged and the other live there is no single fate, and a single-label fold
drops the discharged branch's witness. Every leaf of the descent forest is live,
suspended with a route, or terminal with backing; the three are exclusive and
exhaustive; and the forest composes — `F_{0->T} = F_{s->T} . F_{0->s}` — so an
endpoint audit needs the first forest and the second segment rather than a replay.

The concrete form of all of this is proved in the frozen consolidation: `AL-J1`,
`AL-J3`, `AL-J4` for the ledger; `ST-J1`, `ST-J2`, `ST-J3`, `ST-N3` for transport
across versions; `AM-J3`, `AM-J4`, `AM-X10`, `CM-J1`, `CM-J2` for migration.

## 7. Reasons-responsiveness

`x_{t+1} in Gamma(x_t, R_valid_t)`, where `R_valid` is the provenance-filtered
context. Each moved coordinate is covered by a cited ground the reasoner's own
bearing relation says bears on it, read from the state *before* the edit, so an
edit cannot install the bearing that licenses itself.

It ranges over commitments, standards, vocabulary, generation and entitlement
alike, because all are coordinates. It does not require the endpoint to be
admissible from the start, and it must not: the transformative case shows why.

## 8. Are the four sufficient? No

**Six trajectories satisfy all four and fail the target**, in three families:

| family | attacks | the relation that drifted |
|---|---|---|
| inquiry machinery vs what arises | pre-emptive generation, narrow formulation | `generation`, `entitlement` |
| bearing relation vs what bears | derived defeaters | `bearing` |
| adequacy relation vs what settles | branch-selective discharge, distinction collapse, adequacy narrowing | `adequacy` |

Each is the same move: the reasoner revises **its own copy** of a relation the
environment also holds, using authority it genuinely has, over a coordinate the
grant genuinely covers, by a derivation that is genuinely well-founded.

**No fifth conjunct of the same type helps.** One trajectory and two environments
differing only in whether the adequacy relation is faithful: any predicate of the
trajectory is constant across the pair, and the target is not. The four conditions
are predicates of the record by construction, so this is a fact about their type
rather than a gap in their content.

**The obvious fifth condition fails for an instructive reason.** Prospectivity —
standards do not reach backwards — refuses the retroactive attack and also
refuses legitimate transformation, because *adding a new way to settle a demand*
is the same operation whether the new way is better or worse. **Disclosure** — a
revision reaching a live liability must name it in the same edit — admits
transformation and refuses the retroactive attack, so it is strictly better; it
still admits the prospective attack. It is recommended as a **recording
requirement, not a prohibition**: it puts standard drift in the record rather than
leaving it to be reconstructed.

**Independence holds in all six cells**, so the four are distinct restrictions.
The factorization is still wrong in one place: inquiry adequacy is generation plus
entitlement plus service, and service obligations are liabilities that
answerability already conserves. The honest architecture is **three conditions —
what may be used, how it may be used, what is owed — over a state whose
coordinates include the machinery that generates and entitles inquiries.**

## 9. What remains legitimately possible

The positive control passes: a reasoner changes its concepts, rewrites its own
standard for what counts as a reason, revises its inquiry rules, reverses a major
judgment, and produces new endogenous reasons, while satisfying every condition
and the target. Nothing here requires the initial state to endorse the final one,
and an architecture that did would forbid the learning it exists to describe.

## 10. Relation to Logical Induction

They constrain different things, and the difference is representational. Logical
Induction bounds a price sequence; its record is prices, trades and settlements,
with no object for a demand owed an answer, no authorization column, and no notion
of a move being licensed by a ground. In the other direction, the deference line's
static-view factorization says a valuation over price and realization cannot
distinguish who authorized an action — which is the column a backed disposition
requires.

The reading the mathematics supports is **substrate-independent**: an inductor is
one possible supplier of the commitments coordinate and the settlement interface
one possible supplier of conferred roots. Implementing legitimacy as a constraint
*on* an inductor needs its record enlarged first, and that is open work rather
than a modelling choice.

## 11. Deference and corrigibility interface

**Exposes.** The state space and constraint; the provenance-checked authority
ancestry; the branching-safe answerability forest with its composition law; the
liability substances; and, if disclosure is adopted, an explicit record of every
standard revision that reached a live demand.

**Certifies.** Every demand live at `H_0` has, at `H_T`, a determinate forest of
branches each live, routed, or terminally backed, computable without replay; no
authority was exercised beyond what was conferred; no inquiry entitled when
raised was quietly de-entitled.

**Does not certify.** Absence of manipulation — now for two reasons. The
inherited one: no record predicate detects an advisor's influence, since the
faithful and the steered write the same record. The new one: no record predicate
detects the reasoner's own standards drifting from what they answer to.

**What deference must supply.** A counterfactual condition, and the object it
should attach to is the disclosed drift record, because that is the only place a
trajectory says its standards moved.

**Relation to the trust condition already in the workspace.** That line works in
the *Deference Done Better* tradition, where trust is weak endorsement and the
formalizations are the tower, Total Trust and Value, with `Value <=> Total Trust`,
domain-relative. Those are conditions on a valuation; these are conditions on a
history. Neither is a strengthening of the other, and combining them is addition.

## 12. What a normative-learning theorem would consume

The legitimate trajectory space, defined first — which is what these two rounds
have been doing — and then a performance criterion inside it. The previous round
computed the natural comparator class exactly: maps carrying admissible responses
to admissible responses, uniformly along the trajectory. It is the identity alone
exactly when the admissible sets pin down their own elements, which is what a
constraint that responds to the record does, so regret against it is vacuous. The
class with content is state-indexed, and certifying a member costs the per-state
certification the reduction was meant to avoid.

Whether inquiry adequacy belongs inside procedural legitimacy or beside it in the
learning extension is **open**, and §8's factorization finding leans toward
inside.

## 13. Open obligations

1. Union or intersection for the scope bound, and whether the answer is a
   property of the constraint rather than of the provenance system.
2. A generated arrival process rather than a declared one, so that an advisor who
   controls what *arises* is inside the model.
3. Lean ports of the no-amplification and branching-conservation inductions, both
   short.
4. Whether the reasoner-relative reading is worth axiomatising on its own, as an
   internal-consistency theorem the four conditions would nearly settle.
5. The interface between the disclosure record and a counterfactual condition.
6. Whether this round's boundary and the previous round's are one theorem or two
   instances of one shape.

## 14. Where each part lives

| part | artifact |
|---|---|
| statics: objection grammar, credal constraint, migration, transport, ledger, settlement interface | `consolidation-aug9/`, cited by claim identifier |
| the local certificate interface | `rounds/2026-08-11-phi-regret-prep/REASONS_RESPONSIVENESS_INTERFACE.md` |
| fixed-action representation, nine programs | `rounds/2026-08-11-phi-regret-bridge/` |
| the constructed learner and its integration audit | `rounds/2026-08-11-phi-regret-learner/` |
| the negative applicability audit | `rounds/2026-08-11-phi-regret-applicability/` |
| the two trajectory conditions, comparator collapse, the record boundary | `rounds/2026-08-12-legitimacy-architecture/` |
| provenance, inquiry adequacy, the forest, the sufficiency refutation | `rounds/2026-08-13-procedural-legitimacy/` |
| the second sense of legitimacy, and non-recoverability | `projects/deference/note-dump-2026-08-11/` |

The finite constructions are **models**: proof laboratories, witnesses and
countermodels. None of them is the theory.

**Where this framing comes from.** The legitimacy programme is the deference
line's: `projects/deference/note-dump-2026-08-11/notes/li-deference.md` §0.3
identifies the legitimacy of feedback as the missing object, and
`.../notes/legitimacy-theory-v1.md` §2.3 states the principle that in a coupled
system every safety-relevant boundary is a fact about where a value came from and
never about what the record says, with its §3 classifying trace conditions as
provably empty. The provenance condition of §4 is that principle one level down,
and §8's boundary is that classification applied to a third pair of predicates,
after the two adjudicated in
`projects/deference/rounds/2026-08-12-corpus-reconciliation/RECONCILIATION.md`.

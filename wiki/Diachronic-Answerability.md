# Diachronic answerability

**Status: open / unregistered.** The structural core is a Lean spine with exact
fixtures; the conservation and liveness results are paper-derived from an unpublished
note and its repository counterparts; two central assumptions — semantic
authentication and settlement integrity — are supplied by the application rather than
proved.

## The problem

A reasoner that improves must be able to change: its rules, its procedures, its
evaluators, its concepts, the very way it represents an unresolved obligation. But a
reasoner that can change anything can change its way out of anything. Revise the rule
under which a criticism was raised, and the criticism evaporates. Rewrite the
representation of a debt, and the debt is no longer legible. Nothing was ever refused;
there is simply nothing left to answer.

So the question is not *what must a reasoner keep believing*. The answer to that is
nothing — a later reasoner may reject an earlier norm, defeat an earlier reason,
replace an evaluator. The question is narrower and structural:

> What must remain invariant under self-revision if revision is not to *erase*
> prior answerability?

Answerability is the conservation principle for incurred normative obligation. It
presupposes [Integrity](Integrity) — a history that cannot be rewritten — and it is
stated over the full normative history read against its
[settlement view](Settlement-Interface).

## Four invariants

**Authority has provenance.** Every change in what rules apply must be licensed by
rules that were already applicable before the change. Replaying those citations
backward terminates: each currently applicable rule has a finite recorded ancestry
reaching the initial rule set. This does not require earlier rules to still apply —
only that the current authority came from somewhere and the somewhere is recorded.

**Procedure revision is prospective.** A case is judged by the protocol in force when
it was opened. Changing a protocol creates a fresh version; it does not retroactively
change the terms under which an old episode was decided. To put a continuing case
under new procedural terms, you close the old episode and open a successor under the
new protocol — and any reset of accumulated state has to be explicitly authorized
rather than silently taken.

**New burdens enter through fresh slices.** A continuing case may incur answerability
at several different times, and lumping them together loses the historical fact that
the later burden was not owed earlier. So each increment is a separate object with its
own birth stage and its own anchored content, fixed when it enters and never
redefined.

**Incurred content is conserved.** Every inherited obligation component has exactly
one legitimate fate at every later stage:

> **answered**, or **settlement-discharged**, or **faithfully carried live**.

There is no fourth, silent fate. What remains can never grow — genuinely new
obligation enters as a fresh increment, not by rewriting an old one — and an increment
cannot lose its last carrier until all of it has been accounted for. The immediate
consequence is the one that matters:

> Relabelling cannot discharge a debt. Changing a protocol, ontology, evaluator,
> encoding, or label cannot by itself reduce what is owed. Any decrease appears as an
> authenticated answer or a settlement-backed discharge.

## Defeat carries; it does not extinguish

Reasons defeat one another, and a theory of answerability that could not say so would
be useless. The question is what defeat *does* to the obligation it defeats. The
program's ruling is the **Defeat Principle**:

> A participant may answer an obligation or contest whether it is owed; only an
> authenticated settlement-backed terminal condition may make an unanswered obligation
> disappear.

Equivalently: defeat or disposition *carries* an obligation; it does not extinguish
it. Contesting a debt moves it onto the grounds for saying it is not owed — a fresh
successor that inherits the disposed obligation's load and whose content is "these
grounds suffice to dispose of it". Pure challenge or defeat is therefore an
obligation-to-obligation transition, an identity-frame carry with no loss and no
error, and it is *not* progress: nothing has been answered and nothing has been
settled. Only settlement extinguishes.

The alternative — disposition as a terminal exit, content ceasing to be owed without
being answered — was rejected because it makes the disposition term an unaudited hole
in every conservation law. That hole is exactly the laundering channel a self-improving
reasoner would use, and the transfer reading closes it by construction at the price of
requiring a successor.

An **answerable** disposition is one that is *grounded* — every ground it cites is
already in the record and is not the disposed issue itself — *routed* — its successor
is fresh in the same batch and inherits the load — and *separated* — a named
participant other than the resolver holds standing on the successor, and some cited
ground was opened by someone other than the resolver, or is a settlement fact that
nobody opened. A trace is **defeat-disciplined** when every resolution is an answer,
an answerable disposition, or the settlement of a settled fact. That specification has
a kernel-checked model, and a second trace proved to fail it at exactly one clause.

Two facts about the standing side are worth recording plainly. First, a version of the
specification once bound a participant its body never mentioned, so that half of
separation was vacuous and the laundering result rested on the grounds half alone; the
repair put the participant into the licence itself, and with it the standing side
alone refuses a single-handed disposition. Second, the grounds half cannot do that job
by itself: a settlement fact is foreign to everyone, so a disposition citing only
settlement facts passes the grounds test trivially and is refused, if at all, by
standing.

## Answerability is answerability to someone

Separation as stated stops one participant from laundering a debt through a chain of
dispositions. It does **not** stop two: an alternating pair, each supplying the
other's foreign ground and foreign standing, satisfies separation at every edge and
launders indefinitely. A condition quantifying over *all* coalitions is unsatisfiable
— take the coalition to be everyone.

What does close the alternating walk is naming a party: a disposition is answerable
*for* a protected participant `P` when, in addition, `P` holds standing on the
successor. Then no coalition excluding `P` can hold all the standing on any edge. The
lesson is not that this is the theory of non-capture — it is a definition and its
one-line consequence, deliberately not offered as more — but that

> answerability is answerability **to someone**; preservation of standing is relative
> to a protected principal or a declared relation.

Whether a legitimacy predicate may name a party is one of the maintainer's open
rulings. A purely structural condition cannot do what the principal-relative one does;
the principal-relative one pays by no longer being purely structural. What answerability
can and cannot guarantee about *who* gets to challenge is the boundary with
[Openness](Openness-Coverage-and-Non-Capture).

## Being ignored is a failure too

Conservation is a safety property: nothing disappears. It says nothing about anything
ever *happening*. A perfectly conserved obligation can be perfectly ignored forever.

The liveness half rules out one specific evasion — endless internal rewiring. A
reasoner could keep a case permanently idle by adding a fresh prerequisite or rerouting
an old one every time a real blocker was about to become visible; the case never
closes and no single obstacle ever persists long enough to be named. Forbidding exactly
that, and only while the case genuinely has no available work, forces permanent
idleness to *stabilize on one fixed, unrouted blocker*. Idleness becomes something
with a name and an address. Because a disposed issue meets no prerequisite, a wait on
it reroutes rather than going extinct: a prerequisite cannot be disposed away.

Add the assumption that no fixed blocker persists forever, and the assumption that a
case with recurring opportunities is not starved of attention, and you get the
dichotomy: **either the case eventually has no live instance at all — with everything
it incurred terminally accounted for — or the attention it receives grows without
bound.** Disposition adds one thing to the service side of that horn: for a contested
obligation to be persistently served, the total time it spends in contest must be
summable — shown so far only for contest durations fixed from outside the loop.

## Where this meets the mathematics

That dichotomy is exactly where [Serviceability](Serviceability) begins. The
conceptual theory ends at *"attention diverges"* and says so itself: unbounded
attention is not improvement, and turning attention into improvement needs a structure
identifying which responses a live reason favours plus a condition ensuring persistent
comparisons cannot remain behaviorally inert. That structure is
[Actionability](Actionability-and-Normative-Force), and with it divergent attention
becomes vanishing defect at a known rate. The whole of that handoff — what
answerability exports and what the quantitative side does with it — is the subject of
[Normative Induction](Normative-Induction).

One genuine disagreement resolves favourably. The conceptual theory's attention budget
is renewable — a share of each moment; the mathematics' budget is consumable — a
lifetime stock spent at prices that vary by date. The same construction works on both
sides, shrinking tranches one per case, and non-starvation survives the move at exactly
one price: the cost of enforcement must dip near zero infinitely often.

## What is proof technology and what is the claim

The successor and ancestry machinery — fresh successors, prefix-determined ancestry,
`Live` and `Routes` computed from the trace — is how the invariants above are proved.
It is not itself the public definition. The public content is the three fates, the
Defeat Principle, and the principal relativity of standing; a realization with
different bookkeeping owes the same three things.

## The two holes

**Semantic authentication is assumed.** Everything above turns on the ledger's labels
meaning what they say: that a claimed answer really is an answer on the terms the
burden was incurred on, and that a changed representation has not silently dropped a
distinction the ledger claims to preserve. The theory models this as an interpretation
*anchored to the increment* — not "what the current evaluator says the old
representation means" — and that anchoring is the right property. It is also supplied
by assumption; nothing constructs it, and quantitatively — how *much* a reason changed
while it waited — nothing certifies it. This is the same hole the serviceability
endpoint has, seen from the other side, and it is the program's highest-value open
problem.

**What licenses a disposition is upstream.** The Defeat Principle says what a
disposition *does* — carry, with a successor — and separation says on whose grounds
and standing. Neither says which rules of a practice license contesting which debts;
that content lives in the practice's own licence rules, and the coalition question
above is where its limits show.

## What this does not claim

That any substantive norm survives. That agreement with the past is required — a later
reasoner may reject an earlier norm outright. That the record is *complete*: whether
everything externally important becomes represented at all is the question
[Openness](Openness-Coverage-and-Non-Capture) asks, and it is relative to a declared
scope.

---

**Evidence.** The conceptual theory is a maintainer-supplied note that is not published
here; its repository counterparts are the answerability carriers, anchored slices, and
faithful semantic preservation rounds, and the reconciliation with the service
mathematics is
[`ANSWERABILITY_AND_SERVICE.md`](https://github.com/A-M-Berns/alignment-workspace/blob/939c459974fd1a7365f2c050e883eb1a630123cc/projects/normativity/legitimacy/checkpoint-2026-09-01/ANSWERABILITY_AND_SERVICE.md).
The Defeat Principle ruling and the reasons for it are in the decision ledger; the
definition of answerable disposition is
[`DEFEAT.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f7489cf5a610927b9e85e33d5d42228cd64da7de/projects/normativity/legitimacy/rounds/2026-09-02-unified-grounds-answerable-defeat/DEFEAT.md),
the standing repair and the principal-relative form are
[`STANDING_REPAIR.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f7489cf5a610927b9e85e33d5d42228cd64da7de/projects/normativity/legitimacy/rounds/2026-09-03-defeat-landing-horty-standing/STANDING_REPAIR.md),
and the Lean model of a defeat-disciplined trace is
[`WITNESS.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f7489cf5a610927b9e85e33d5d42228cd64da7de/projects/normativity/legitimacy/rounds/2026-09-03-defeat-landing-horty-standing/WITNESS.md).
How the defeat theory differs from default logic and structured argumentation is on
the [prior art](Prior-Art) page.

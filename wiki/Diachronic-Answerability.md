# Diachronic answerability

**Status: open / unregistered.** Paper-derived results from an unpublished note and
three research rounds, with two central assumptions explicitly supplied by the
application rather than proved.

## The problem

A reasoner that improves must be able to change: its rules, its procedures, its
evaluators, its concepts, the very way it represents an unresolved obligation. But
a reasoner that can change anything can change its way out of anything. Revise the
rule under which a criticism was raised, and the criticism evaporates. Rewrite the
representation of a debt, and the debt is no longer legible. Nothing was ever
refused; there is simply nothing left to answer.

So the question is not *what must a reasoner keep believing*. The answer to that is
nothing — a later reasoner may reject an earlier norm, defeat an earlier reason,
replace an evaluator. The question is narrower and structural:

> What must remain invariant under self-revision if revision is not to *erase*
> prior answerability?

## Four invariants

**Authority has provenance.** Every change in what rules apply must be licensed by
rules that were already applicable before the change. Replaying those citations
backward terminates: each currently applicable rule has a finite recorded ancestry
reaching the initial rule set. This does not require earlier rules to still apply —
only that the current authority came from somewhere and the somewhere is recorded.

**Procedure revision is prospective.** A case is judged by the protocol in force
when it was opened. Changing a protocol creates a fresh version; it does not
retroactively change the terms under which an old episode was decided. To put a
continuing case under new procedural terms, you close the old episode and open a
successor under the new protocol — and any reset of accumulated state has to be
explicitly authorized rather than silently taken.

**New burdens enter through fresh slices.** A continuing case may incur
answerability at several different times, and lumping them together loses the
historical fact that the later burden was not owed earlier. So each increment is a
separate object with its own birth stage and its own content, fixed at admission
and never redefined.

**Incurred content is conserved.** For each such increment, what was originally
owed decomposes at every later stage into three parts: what has been **satisfied**,
what has been legitimately **disposed of**, and what **remains**. The remaining
part can never grow — genuinely new obligation must enter as a fresh increment, not
by rewriting an old one's content — and an increment cannot quietly lose its last
carrier until all of it has been accounted for.

The immediate consequence is the one that matters:

> Relabelling cannot discharge a debt. Changing a protocol, ontology, evaluator,
> encoding, or label cannot by itself reduce what is owed. Any decrease has to
> appear as authenticated satisfaction or authorized disposition.

## Being ignored is a failure too

Conservation is a safety property: nothing disappears. It says nothing about
anything ever *happening*. A perfectly conserved obligation can be perfectly
ignored forever.

The liveness half rules out one specific evasion — endless internal rewiring. A
reasoner could keep a case permanently idle by adding a fresh prerequisite or
rerouting an old one every time a real blocker was about to become visible; the
case never closes and no single obstacle ever persists long enough to be named.
Forbidding exactly that (and only while the case genuinely has no available work)
forces permanent idleness to *stabilize on one fixed, unrouted blocker*. Idleness
becomes something with a name and an address.

Add the assumption that no fixed blocker persists forever, and the assumption that
a case with recurring opportunities is not starved of attention, and you get the
dichotomy: **either the case eventually has no live instance at all — with
everything it incurred terminally accounted for — or the attention it receives
grows without bound.**

## Where this meets the mathematics

That dichotomy is exactly where [Serviceability](Serviceability) begins.

The conceptual theory ends at *"attention diverges"*. It says so itself: unbounded
attention is not improvement, and turning attention into improvement would need a
structure identifying which responses a live reason favours, plus a condition
ensuring persistent comparisons cannot remain behaviorally inert. That structure is
[Actionability and normative force](Actionability-and-Normative-Force), and with it
divergent attention becomes vanishing defect at a known rate.

The two bodies of work meet at exactly one point, and it is a clean join.

There is one genuine disagreement, and it resolves favourably. The conceptual
theory's attention budget is **renewable** — a share of each moment. The
mathematics' budget is **consumable** — a lifetime stock, spent at prices that vary
by date. Under a renewable budget, not starving anyone is nearly free. Under a
consumable one it is not: there are norms no schedule can discharge at any budget.
The reconciliation is that the same construction works on both sides — shrinking
tranches, one per case — and non-starvation survives the move at exactly one price:
the cost of enforcement must dip near zero infinitely often. Nothing more.

## The two holes

**Semantic authentication is assumed.** Everything above turns on the ledger's
labels meaning what they say: that a claimed satisfaction really is satisfaction on
the terms the burden was incurred on, and that a changed representation has not
silently dropped a distinction the ledger claims to preserve. The theory models
this as an interpretation *anchored to the increment* — not "what the current
evaluator says the old representation means", which is the reading that would let a
revision rewrite the ledger auditing it. That anchoring is the right property. It
is also supplied by assumption; nothing constructs it.

This is the same hole the serviceability endpoint has, seen from the other side.
Closing it is the program's highest-value open problem.

**Disposition has no theory.** Content may "legitimately cease to be owed without
being answered" — and what licenses that is uncharacterized. This matters more than
it sounds. It is the obvious laundering channel; it is where **defeat** lives, since
one reason defeating another just *is* a licence to stop owing the first; and it
changes the affordability question, because if obligations can legitimately be
disposed of then what has to be sustained is undisposed obligation. The
serviceability mathematics has no disposition at all: claim mass is served or it
persists.

A theory of authorized disposition would supply all three at once, which is why the
[roadmap](Roadmap) puts it second.

## What this does not claim

That any substantive norm survives. That agreement with the past is required — a
later reasoner may reject an earlier norm outright. That the record is *complete*:
whether everything externally important becomes represented at all is a separate
consumer-relative question the theory deliberately leaves outside itself.

---

**Evidence.** The conceptual theory is a maintainer-supplied note that is not
published here. Its three repository counterpart rounds — answerability carriers,
anchored slices, and faithful semantic preservation — are **not on the main branch**:
their pull requests merged into each other on a stacked branch that was never landed.
Until that stack lands, the note itself is the only citable statement of the results
on this page. The reconciliation with the service mathematics is
[`ANSWERABILITY_AND_SERVICE.md`](https://github.com/A-M-Berns/alignment-workspace/blob/939c459974fd1a7365f2c050e883eb1a630123cc/projects/normativity/legitimacy/checkpoint-2026-09-01/ANSWERABILITY_AND_SERVICE.md).

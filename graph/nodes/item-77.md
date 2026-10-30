---
id: item-77
kind: leaf
leaf_kind: question
action: "Execute PRIORITIES item 77: a theory of what licenses MayDispose, the route by which incurred content legitimately ceases to be owed without being answered."
who: agent
item: "77"
title: "What licenses authorized disposition?"
section: "Deference line — second wave"
maintainer_order: 73
difficulty: "entry"
project: normativity
dispatchable: true
item_status: open
deliverable: "a stated theorem with exact-rational fixtures, including a legitimate disposition and a laundering attempt the licence rejects."
acceptance: "the round's runner is discovered by `python3 tests/run.py` and passes."
context: ["projects/normativity/legitimacy/checkpoint-2026-09-01/ANSWERABILITY_AND_SERVICE.md", "projects/normativity/legitimacy/rounds/2026-08-30-anchored-slices-auth-transfer/", "projects/normativity/legitimacy/rounds/2026-08-31-faithful-semantic-preservation/"]
work:
  - {kind: decision, ref: 2026-09-02--grounds-unified-defeat-answerable-coalition-proof}
  - {kind: decision, ref: 2026-09-03--defeat-principle-adopted}
author: "@smithy-verity"
size: L
size_reason: "one item that is three questions at once"
version: 1
---
## Statement
A theory of authorized disposition says what licenses incurred content to cease
being owed without being answered.

## Source
PRIORITIES.md, item 77 ("What licenses authorized disposition?"), which the
item calls the highest-value unfiled question in the line because it is three
questions at once;
projects/normativity/legitimacy/checkpoint-2026-09-01/OPEN_PROBLEMS.md, section
2.

## Item
The answerability calculus lets incurred content leave the account by one of two
routes: **satisfaction**, and **authorized disposition** — content that legitimately
ceases to be owed *without* being answered. Satisfaction has an authentication
obligation. Disposition has a licence predicate, `MayDispose`, and no theory of
what licenses it.

This is the highest-value unfiled question in the line, because it is three
questions at once.

**It is where defeat lives.** "Reason `r'` defeats reason `r`" is, in this
vocabulary, exactly a licence to stop owing `r`'s remaining content. So the open
Layer II question *when may one reason replace another* is this question.

**It is the laundering channel.** An unaudited disposition term makes every
insolvency and every unanswered burden disappear; the no-laundering theorem is true
only because it *assumes* each disposition term is authenticated.

**It changes the affordability question.** The persistence analysis rests on the
obligation stream diverging. If content can be legitimately disposed of, what has to
diverge is *undisposed* content, and a reason that looks permanently insolvent may
be affordable after authorized disposition.

Settle it. Give a licence predicate with an authentication obligation and a
soundness theorem — disposed content is content that could not have been owed, or
was answered under a different description, or was superseded by an authorized
revision whose grounds trace back to the initial rule set — and then say what it
does to the obligation stream the affordability theory consumes.

**A prior-art check is part of the deliverable.** Horty's priority orderings among
defaults are the obvious place to look and are probably *not* enough: a priority
ordering says which reason wins, not what licenses the loser to stop being owed.
Whether that machinery can express `MayDispose` at all is worth settling before
building something new.

*Deliverable shape:* a stated theorem with exact-rational fixtures, including a
legitimate disposition and a laundering attempt the licence rejects.
*Acceptance check:* the round's runner is discovered by `python3 tests/run.py` and
passes.

*Context:*
`projects/normativity/legitimacy/checkpoint-2026-09-01/ANSWERABILITY_AND_SERVICE.md`
§6 for why the three questions are one, and that checkpoint's `OPEN_PROBLEMS.md` §2;
`projects/normativity/legitimacy/rounds/2026-08-30-anchored-slices-auth-transfer/`
for the conservation law the disposition term sits in, and
`projects/normativity/legitimacy/rounds/2026-08-31-faithful-semantic-preservation/`
for the authentication side.
*A solution ships:* the licence, its soundness theorem, and a statement of what the
affordability theory's obligation stream becomes once disposition is available.

*Partly answered, 2026-09-02*, by
`projects/normativity/legitimacy/rounds/2026-09-02-unified-grounds-answerable-defeat/`,
conditional on the Defeat Principle (`DECISIONS.md`, queued in *Awaiting the author*).
**Shipped:** the licence — answerable disposal, grounded and routed and separated — with
a soundness theorem, a no-self-grounding theorem, and a laundering theorem; the
disposition term's effect on the obligation stream, which is that disposal is an
obligation-to-obligation transport step contributing zero to either terminal fate, so
what must diverge is undisposed content and the F3 bound gains one term `D·κ^r_N`; and
the type a disposal's grounds live in, which no previous type supplied.
**Not shipped, and the item stays open for them:** the **Horty prior-art check** this
item asks for was not performed; and the licence **does not stop coalitions** — two
participants alternating disposals satisfy separation at every edge and launder
indefinitely, so the laundering channel this item names is narrowed and not closed.

*Prior-art check partly done, 2026-09-03*, by
`projects/normativity/legitimacy/rounds/2026-09-03-defeat-landing-horty-standing/HORTY.md`.
**Verdict: Horty's machinery cannot express `MayDispose`** — and the reason is deeper
than this item states. A priority ordering does not merely fail to license the loser's
release; Horty's theory says what to *conclude* rather than what is *owed*, so there is
no account for a licence to operate on and the question does not arise inside it. Of the
round's three clauses, grounds have an image and successor and separation do not — the
last because a default theory has no **participants**, not because the ordering is
exogenous, which in variable-priority default logic it is not. **Exclusion is
challengeable in-system** (undercutting is a triggered default lowering a weight, and
the undercutter is itself defeasible), so an exclusionary reason is closer to `dispose`
than to `settle` and the two summands do not collapse. ASPIC+ has no successor, and its
attack relation is unauthored.

**Checked against primary text.** The verdict above is verified against **Horty,
*Reasons as Defaults*, Draft #2, 16 August 2006** — the paper the 2012 book develops,
carrying the whole apparatus: Definitions 1–7, fixed- and variable-priority theories,
and the threshold theories that become "exclusionary default logic". Horty states the
crux himself: exclusionary reasons "can themselves be excluded", and he rejects a
stratified hierarchy of reason-orders.

**What still blocks the item.** Two things, and neither is the theory question.
First, the **OUP 2012 book** was not read — its contribution over the paper is that
development plus the Dancy material, so a citation *of the book* is not yet licensed.
Second, and larger, **the laundering channel this item names is closed against single
participants and not against coalitions**: two participants alternating disposals
satisfy separation at every edge. The item closes when a maintainer either obtains the
book or rules the paper sufficient, **and** when the coalition hole is closed.

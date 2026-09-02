# The Horty check

`PRIORITIES.md` item 77 names a prior-art check as part of its deliverable, points at
Horty's priority orderings, and predicts they are not enough. `PRIOR_ART.md` §7 records
the same thing as "an open question and a good literature target". This settles it, and
one of the five findings comes out **against** the shape the dispatch predicted.

## 0. What was actually read, and what was not

`AGENTS.md` standard 7 forbids a remembered label. So, precisely:

| source | status |
| --- | --- |
| Modgil & Prakken, *The ASPIC+ framework for structured argumentation: a tutorial* (Argument & Computation, 2014) | **read** — PDF fetched from the author's site, <https://webspace.science.uu.nl/~prakk101/pubs/ASPICtutorial.pdf> |
| *Defeasible Reasoning*, Stanford Encyclopedia of Philosophy, <https://plato.stanford.edu/entries/reasoning-defeasible/> | **read** — the source for Pollock's rebut/undercut definitions and for Horty's undercutting mechanism |
| Horty, *Reasons as Defaults*, OUP 2012 | **NOT read.** Every copy reachable from here failed: the author's site (`horty.umiacs.io`) serves a certificate that does not cover the host it redirects to, the CiteSeerX draft resolves only into `web.archive.org`, which is blocked, and the Springer/OUP copies are paywalled. |
| Pollock, *Defeasible Reasoning*, Cognitive Science 11(4), 1987 | **NOT read.** `PRIOR_ART.md` §2 records this citation as "verified 2026-09-01" against a URL on `umiacs.umd.edu`; **that URL is now dead**, by the same redirect-and-certificate failure. Filed below. |

**So the findings below rest on the ASPIC+ primary text, on SEP, and on the
publisher's own description of the book's two default-logic variants — not on the book
itself.** Where a claim about Horty depends on the primary text, it is marked
*unverified* and is not asserted. That is a smaller check than item 77 asks for, and
the item does not close on it.

## Finding 1 — Expressibility: can a priority ordering express `dispose`?

**Verdict: no, and for a deeper reason than the item states.**

Item 77 says "a priority ordering says which reason wins, not what licenses the loser
to stop being owed." That is right, but it concedes too much: it presupposes that in
Horty's framework something *is* owed, and that the ordering merely fails to license
the loser's release. Neither is so.

Horty's apparatus computes, from a fixed default theory and a priority ordering, a
**proper scenario** — a rationally acceptable subset of defaults to reason from — and
the conclusions it supports. A default that loses on priority is simply **not in the
selected set**. There is no object in the theory that records that it was ever a
candidate, no quantity attached to it, and nothing that a later stage must discharge.

Mapping the round's three kinds onto that apparatus:

| round's kind | image in Horty |
| --- | --- |
| `answer` | **none.** Horty has conclusions being *drawn*, not obligations being *discharged*. Drawing a default's conclusion is not paying anything. |
| `dispose` | **partial.** A default losing on priority, or being excluded, is the closest thing — but it leaves no successor and no residue. |
| `settle` | **partial.** A change in the facts changes which defaults are triggered, which is settlement lowering demand. |

So the honest statement is not "Horty has defeat but no licence to stop owing". It is:

> **Horty's theory is a theory of what to conclude, not of what is owed.** There is no
> account, so there is nothing for a disposal to move, and the question "what licenses
> the loser to stop being owed" does not arise inside it.

*Unverified against the primary text:* whether a defeated default can become binding
again when the facts change. The apparatus plainly permits it — the default is still in
`D` — but that is reactivation by *recomputation*, not by any participant's licensed
act, and nothing is owed in the interim.

## Finding 2 — The direction of the gap

**Verdict: the prediction is right about *which* of D1–D3 have images and wrong about
*why*.**

The dispatch predicted: grounds (D1) yes, successor (D2) no, separation (D3) no,
"because the ordering is exogenous and unauthored."

| clause | image in Horty | |
| --- | --- | --- |
| **D1 grounded** | **yes.** The winning higher-priority default is the ground of the loser's defeat, and in **variable priority default logic** the priority itself is established by higher-order defaults, so the ground is in the record. | prediction correct |
| **D2 routed** | **no.** No successor, no inherited load, nothing carried forward. | prediction correct |
| **D3 separated** | **no.** | prediction correct, reason wrong |

The reason D3 has no image is **not** that the ordering is exogenous. Horty
specifically built the variant in which it is *not*: SEP records that he "allows for
defeasible reasoning about priorities … by means of higher-order default rules." The
ordering is endogenous in exactly the sense the prediction denies.

What is missing is **authorship, not endogeneity**. A default theory has no
participants — no openers, no resolvers, nobody who holds standing. Reasoning
determines the priority; no *one* does. D3 asks a question about *who*, and there is no
`who` in the ontology to ask it of.

This matters beyond bookkeeping: it says the gap between the two frameworks is not
repairable by making Horty's priorities more dynamic. It is repairable only by adding
participants, which is a change of subject.

*(The prediction is, however, exactly right about canonical ASPIC+ — see Finding 5.)*

## Finding 3 — Undercutting: is exclusion answerable? **(the crux)**

**Verdict: yes, exclusion is challengeable in-system. So an exclusionary reason is
*not* a settlement fact, and the theory does not have one summand where the round has
two.**

The dispatch set this up as the crux: *if an exclusionary reason is unchallengeable, it
is a settlement fact in the round's typing, not a disposal.* The antecedent fails.

SEP states the mechanism: Horty "addresses undercutting by treating it as a triggered
default that lowers the weight of the undercut rule below some threshold, with the
result that the undercut rule can no longer be triggered." Three consequences:

1. **The undercutter is itself a default.** It is triggered, it has premises, and it is
   subject to the same priority machinery as everything else — so it can itself be
   defeated or excluded. Exclusion is *not* at a level the system cannot challenge.
2. **Undercutting is implemented as a priority operation**, not as a separate
   primitive. Horty's exclusion and his priorities are the same machinery, which is why
   the book investigates "connections among concepts like exclusion and priorities."
3. **But the effect leaves no residue.** The undercut rule "can no longer be triggered"
   — it drops out. No successor, nothing owed.

So in the round's typing, an exclusionary reason is a **`dispose` without D2**: a
grounded, in-system, challengeable move that moves nothing. It is emphatically not
`settle`, because `settle` is the kind whose warrant no participant may contest, and
Horty's exclusions are contestable by construction.

**This is a positive result for the round's two-summand structure.** The worry the
dispatch raised — that the prior art collapses `dispose` and `settle` into one — does
not obtain. The round's separation of the two is not a distinction Horty's framework
lacks the resources to draw; it is a distinction that does not arise there because
nothing is owed.

Raz's exclusionary reasons, which Horty is formalizing, are second-order reasons that
exclude first-order reasons from consideration. SEP's framing — "an exclusionary reason
is an undercutting defeater in the practical domain" — is the bridge, and it is the
same bridge the round crosses when it applies Pollock's belief-level distinction to a
debt.

## Finding 4 — What survives as new, and what becomes a dependency

**New.** Phrased so a reader of the books can check it:

> In Horty and in ASPIC+, the objects computed — proper scenarios, extensions — are a
> function of the *current* theory: facts, defaults, priorities, arguments, attacks.
> **Nothing in either apparatus is a function of the history of defeats.** Delete every
> record of which defaults lost, and recompute: you get the same answer.
>
> The round's defeat theory adds exactly that dependence. A disposed issue leaves a
> named successor carrying its load; `Live`, `Routes`, and the conservation law all
> read it; and the trace's future is not recoverable from its current outstanding set
> alone. Deleting the record of a defeat changes the theorems.

That is the account, and it is what neither framework has. The three clauses D1–D3 are
the terms on which a defeat is allowed to create such a successor, and none of them has
an antecedent in either book because neither book has anything for them to constrain.

**Dependency, not resemblance.** `PRIOR_ART.md` §2 already says of Pollock "What we
take: the undercut/rebut split." That is right and should be strengthened in its
wording: the round's `answer`/`dispose` distinction **is** Pollock's rebut/undercut
distinction, transposed from a belief's warrant to a debt's warrant. `answer` rebuts
the challenge-warrant; `dispose` undercuts it. This is a conceptual dependency in the
strong sense — the round did not arrive at two kinds independently — and the
`SUPERSESSION`-style honesty the repository applies elsewhere applies here.

For Horty, the entry should change from "open question" to: **his machinery cannot
express `MayDispose`, because it has no account for a licence to operate on; and his
exclusion mechanism is challengeable in-system, so it is closer to `dispose` than to
`settle`.**

## Finding 5 — ASPIC+ in one section

Read from the Modgil–Prakken tutorial directly.

- **Attack types.** Undermining (attacks premises), rebutting (attacks a conclusion
  with a contrary), undercutting (attacks the inference rule). The three-way split is
  finer than the round's two, and the round's `answer`/`dispose` cuts across it:
  `answer` is rebutting, `dispose` is undercutting, and undermining has no image
  because a disposal attacks the *warrant of the challenge*, not the challenge's
  premises.
- **Does defeat have a successor?** **No.** A defeated argument is excluded from the
  extension; the framework retains no residual trace and no successor. There *is*
  **reinstatement** — an argument defeated at one level may be reinstated if all its
  attackers are themselves defeated — but reinstatement is automatic and structural,
  computed by the semantics, not a licensed act by a participant with a recorded
  ground. It is the opposite of a transfer: nothing moved, so nothing had to come back.
- **Is the attack relation authored?** **No, and here the dispatch's prediction is
  exactly right.** The preference ordering is exogenous in canonical ASPIC+, supplied
  externally rather than derived from arguments. Making preferences themselves argument
  conclusions is possible in principle and is explicitly non-standard. So ASPIC+ has
  neither D2 nor D3, and unlike Horty it does not even have the endogeneity that would
  make the *reason* for lacking D3 interesting.

Prakken 2018 is already cited in `PRIOR_ART.md` for the statics and is not re-derived
here.

## Consequences for the ledger

1. `PRIOR_ART.md` §2's Horty entry and §7's dependency note get the verdict, replacing
   "open question".
2. Pollock's entry is strengthened from "what we take" to a stated conceptual
   dependency of the two kinds.
3. **`PRIOR_ART.md` §2's Pollock URL is dead** and its "*Citation verified 2026-09-01*"
   mark now over-claims — the link does not resolve today. Recorded per standard 7,
   with the verification date left standing as a fact about that date and the link
   marked unreachable.
4. Item 77's prior-art deliverable is **partly** discharged: ASPIC+ and the
   undercutting question are settled from sources; the book itself was not read, so the
   item stays open on that.

## Reservation

None new. The dispatch offered one — *whether the round's `settle` and Horty's
exclusionary reasons are the same object* — conditional on the Horty check producing
it. **It did not.** Finding 3 answers the question rather than raising it: exclusionary
reasons are challengeable, `settle` is not, so they are different objects and there is
nothing to reserve. The related settlement-independence reservation from PR79 stays in
the queue on its own terms.

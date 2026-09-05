# Normativity

Normativity asks what it means for a changing reasoner to remain responsive to
reasons. A fixed objective can score behavior from outside. This project instead
asks how warrants, challenges, permissions, and failures can be represented in a
public practice that the reasoner participates in without giving the reasoner
unilateral control over the score.

The line moves from static assessment to learning:

1. A **relational score** records what one participant attributes to another.
2. A quantitative **book** projects parts of that score into exact constraints
   and accounted quantities.
3. **Answerability** determines when a participant owes an answer.
4. A response-learning theorem asks whether repeated, publicly exposed failures
   place diminishing weight on an inferior response.

[Reasons, Answerability, and the Score](Reasons-Answerability-and-the-Score)
develops the first three layers. [Normative Response Learning](Normative-Response-Learning)
explains the current `Due / Licensed / Performance` interface and conditional
theorem.

## Core idea

A practice can assess a response without pretending to possess a view from
nowhere. Participant `i` may attribute commitments and entitlements to
participant `j` using `i`'s inferential practice and `j`'s public
acknowledgments. A challenge then has a source, a target, and a standing
relation. Disagreement is represented rather than averaged away.

The quantitative layer is downstream of that representation. It uses bounds,
holdings, intervals, charges, and caps to make finite questions exact.
**Leverage** survives only as the name of a technical quantity: how far a forced
interval endpoint clears a relevant threshold.

Learning adds a further demand. Static admissibility can say that a response is
allowed now. It does not show that a bounded learner will stop repeating a
recognized failure. That requires an explicit response space, a loss-blind
compiler of lawful edits, a performance margin, learning dynamics, and enough
coverage for the relevant burdens to recur.

## Current status

> **Established — `lean-proved`.** The traderization arc is the line's registered
> result: Logical Induction generalized from a deductive process to an assessment
> process, the enforcement position as a legal strategy with its conformance
> algebra, preservation of the criterion under bounded assessed liability, and —
> for deduction — the original criterion together with finite-date coherence, from
> a compiled market that assumes nothing about the deductive process beyond the
> pinned source's own certificate. The
> <!--state:workspace:counts.registered_claims_by_project.normativity-->27<!--/state-->
> entries in this line's registry each name a Lean declaration and the priority
> item it answers.

> **Open / unregistered research.** The frozen consolidation is a separate
> <!--state:workspace:counts.foundation_claims-->180<!--/state-->-claim
> foundation with its own ledger and status vocabulary. The modern
> workspace registry does not translate or promote those claims. The current
> response-learning theorem and dynamics witness remain unregistered.

The abstract response-learning theorem is settled at its stated conditional
interface level. The normative content remains open: there is no satisfactory
substantive `Due`, no proof of substantive soundness for `Licensed`, no general
performance theory, and no delivered coverage conclusion. An audit transport
object for liabilities stated across vocabulary change is also absent. What the
registered results establish is force, not legitimacy: the map from a normative record
to a region a market can be made to respect is specified by the
[Normative Inductor](Normative-Inductor)'s compiler contract and not yet proved.

## A current research direction: operative force

A constraint that cannot change what a reasoner does is a description of the
reasoner, not a demand on it. So a normative architecture needs an account of how
a constraint acquires **operative force** — and that account should not be
supplied by fiat, as an unexplained primitive of whatever dynamics the reasoner
runs.

One candidate is to make the constraint a **participant**. If the reasoner's
credal state is a set of prices in a market, an admissible region can be given
force by a distinguished trader that trades against violations of it: when the
displayed price leaves the region, the trader takes a position whose payoff
improves as the price moves back in, and the market's own price-setting has to
answer it.

Two distinctions the work turns on.

**Constraint source versus enforcement mechanism.** The mechanism is indifferent
to where the region comes from. Logical consequence, a settled record, a trusted
process and an endorsed normative book are all *sources*, and one enforcement
mechanism can serve any of them — provided the source delivers something the
mechanism can consume, which is not a set but a finite system of rational
inequalities. A source that names a region without presenting it that way names
nothing the mechanism can act on.

**Force versus legitimacy.** Force turns out to be cheap. Any nonempty region
with a presentation gets it, at any trading intensity, and the mechanism will
hold a region that fixes a single credal state exactly as readily as a defensible
one. Whoever writes the inequalities therefore sets the reasoner's beliefs, which
makes this a channel for manipulation before it is anything else. Operative force
is no evidence of legitimacy, and this direction supplies no legitimacy result.
It sharpens the question by separating it cleanly from a mechanism it might
otherwise be confused with.

### Deduction as the calibration case

Ordinary deduction fits. What a deductive process has settled by a given date
determines the credal states some distribution over the still-possible worlds
reproduces, and enforcing membership in *that* region is a finite-date version of
a coherence property logical inductors otherwise obtain only in the limit.

It is also the free case. The enforcing participant's position is worth nothing
lost in any world the region contains, so where the region admits every world
deduction has not ruled out, it never shows a loss a live world would recognise
and the market's resistance to being pumped survives untouched. Deduction has
that property by construction, which makes it the instrument the other sources
are read against rather than one instance among equals.

What a normative constraint does differently is exclude states deduction permits
— that is what it is for — and excluding a world that is still live is what makes
the enforcing participant lose. But the cost is not a wall. It is a quantity,
depending on how much ordinary trading pressure there is, how deep the exclusion
cuts, and how tightly the mechanism has promised to enforce. A source may exclude
live worlds permanently and still be safe, provided that quantity stays summable
over time. Not agreement with deduction, then; convergence on it, at a rate.

### What a constraint is, and what a market can see of it

Underneath this sits a distinction that took the work several attempts to state
correctly, and getting it right turned out to improve the picture rather than
merely repair it.

A constraint of this kind is really a restriction on **distributions** over
possible worlds, not on any single world and not on prices. Which worlds still
count as possible is then read off by asking which ones some permitted
distribution takes seriously — gives positive weight to. A constraint saying "no
more than even odds on `A`" does not make `A` impossible; it permits the
even-odds distribution, which takes `A` perfectly seriously.

What a market sees is much less than that. Prices record only the *averages* a
distribution induces on the sentences being priced. And averages do not determine
the distribution: two quite different restrictions can produce exactly the same
prices while disagreeing about which worlds are possible at all. The smallest
example needs two sentences and says that deduction has established they agree —
prices then pin `p(A) = p(B)`, and the distribution that is certain they *disagree*,
half one way and half the other, produces exactly those prices while being ruled
out entirely.

So prices are enough to push a reasoner around and not enough to say what it
believes. That is the reason this direction has two channels rather than one, and
it is a fact about information rather than an awkwardness of mechanism. The
enforcement mechanism works on the prices; what the reasoner is answerable to is
the constraint the prices only partly reveal.

It also sharpens what remains open. The mechanism's guarantee is about averages;
being resistant to a pump is about individual worlds. Bridging the two takes a
further assumption — about how far the constraint's demands sit from the world in
question, or about how much weight that world can carry — and which assumption is
right is not settled.

### What a norm has to promise in exchange for force

The question that decides whether any of this is usable is not whether prices can
be pushed exactly onto a demand. It is whether pushing them destroys the property
that made the reasoner worth having: that nobody can pump it indefinitely.

Splitting the demand helps. The part that merely records what has been settled
costs nothing to enforce — no still-possible world disagrees with it, so the
participant enforcing it never loses to anyone. The part where a norm genuinely
outruns the record is where the cost lives, and the cost is governed by one
quantity: how far the norm's demand exceeds what the least favourable
still-possible world delivers. Notably it does *not* depend on how hard the norm
is enforced.

Settlement pushes that quantity down and never back up, which helps and is not
enough on its own. What is missing is an account: the practice has to be willing
to say in advance how much its norms are allowed to cost while they run ahead of
what has been established, and to stop when that is spent. The line's existing
work already imposes exactly that discipline on a different object, for the same
reason — a claim can survive any number of tests if someone keeps quietly paying
for its losses.

So the shape is: one clause says what force a norm gets, and another says how much
damage granting it may do.

### Force, and what force costs

Two things about this mechanism are worth separating from the idea that motivated
it.

It leaves the reasoner's own price-setting alone. That matters more than it
sounds: the alternative way to make a region operative is to constrain the
price-setting directly, and a price-setter required to respect a region can be
handed demands it cannot jointly meet. Adding a participant instead changes only
what the existing machinery is responding to, and everything already known about
that machinery keeps applying.

And there is a trade the mechanism cannot presently escape. A participant whose
position shrinks as the violation does is safe — it never loses where the region
is right — but it can be neutralised by ordinary traders near the boundary, so
what it delivers is conformance to a declared tolerance rather than exact
membership. A participant that holds a floor outside the region can deliver exact
membership, and pays for it by holding positions where nothing is wrong, which is
where its losses come from. Whether one participant can do both is open.

Where exactness is available turns on geometry, and not in the way one might
guess. A constraint that pins a sentence to certainty — the shape a settled fact
takes — is the **easy** case: it sits on a face of the space of possible prices,
and a participant pushing outward from that face costs nothing to leave in place.
The hard case is a constraint sitting strictly inside, of the kind a relation
between sentences produces, where the participant must change direction as the
price crosses it and continuity leaves a band it cannot hold. The general
characterisation is not settled, and tolerance is what the surrounding machinery
was built to consume anyway.

### Where it sits

This is a layer *beneath* the statics rather than a rival to them, and it is one
layer among several. Which sources may define admissible regions is a question of
constitution and legitimacy; whether a requested region is coherent and non-empty
is feasibility; who may write, revise, object or be held to account is
answerability; and how an agent improves among the responses it is permitted is
learning. Force is only the question of how a region, once validated, reaches
behaviour at all — and keeping the five apart is most of what this direction has
so far established.

The [response-learning interface](Normative-Response-Learning) governs how an
agent learns among responses; force governs which credal states it may display.
The arrow between a normative record and a region in price space is the
proof-carrying compiler of the [Normative Inductor](Normative-Inductor): it takes
legitimately incurred obligations to one joint convex region per service date, and
the force mechanism here enforces that region. The compiler's soundness and
completeness are stated as realization obligations, not proved, so the general reading
is a specified interface with deduction as its only kernel-checked instance. For
[Deference](Deference) the direction is downstream, not a solution — a trusted
process's constraint can be made operative this way while authorization, corrective
control and futurity remain exactly as open as before.

Force also turns out to be **bought rather than granted**. Giving a constraint
operative force means running an externally funded trader against violations, and
an externally funded trader is exactly what Logical Induction's no-exploitation
guarantee is not built to survive. What rescues it is a finite cumulative account:
each date's force costs `(slack + ordinary volume) × exclusion depth ÷ tolerance`,
charged before the trade is emitted, and the remaining account is what determines
how tightly the reasoner may be forced. Two things the account is *not* is worth
saying, because both look sufficient and neither is: capping each endorsement
separately fails, since finitely many caps need not sum, and capping how many
constraints are live per date fails, since nothing bounds the number of dates.

What a date of force costs is a product of three quantities — how much ordinary
market pressure it must push against, how far its demand outruns what the record
supports, and how much error it tolerates — and the account holds whenever that
product is summable. None of the three has to shrink on its own. A demand can stay
exactly as far from the record as it ever was, forever, and remain affordable if
the market pressure it faces decays; only when pressure and distance are both
pinned and the tolerance is capped does the account necessarily run out.

An earlier reading of this said the normative distance itself had to close. It
does not, and the difference matters for what the picture claims: safety does not
require that disagreement be settled, nor that it narrow — only that resisting it
get cheaper by some route.

The motivating statics do produce a demand that is never vindicated and stays
affordable indefinitely, though not from every kind of demand: a constraint on a
single sentence holds its distance and then closes it in one step, while a graded
demand sitting at the value the record approaches can be enforced forever.

Evidence: [the traderized-enforcement round](https://github.com/A-M-Berns/alignment-workspace/tree/46032abe26be325218cec51f857b86be377108ab/projects/normativity/rounds/2026-08-16-traderized-enforcement).

## Evidence and deeper reading

- [Normativity foundation ledger](https://github.com/A-M-Berns/alignment-workspace/blob/76b65e5cc327ca2f334e829a76548514813ab4b0/projects/normativity/consolidation-aug9/LEDGER.md)
- [Foundation verification classes](https://github.com/A-M-Berns/alignment-workspace/blob/76b65e5cc327ca2f334e829a76548514813ab4b0/projects/normativity/consolidation-aug9/VERIFICATION.md)
- [Current interface note](https://github.com/A-M-Berns/alignment-workspace/blob/76b65e5cc327ca2f334e829a76548514813ab4b0/projects/normativity/notes/NORMATIVE_LEARNING_INTERFACE.md)
- [Current structured state](https://github.com/A-M-Berns/alignment-workspace/blob/76b65e5cc327ca2f334e829a76548514813ab4b0/state/theorem_interface.json)

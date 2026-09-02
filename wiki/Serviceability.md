# Serviceability

**Status: open / unregistered.** The results below are paper-derived with exact
rational fixtures, from a research round that is merged but registers no claim.
They are current research, not Established.

The program treats this layer as **closed for research sequencing** — settled enough
to build on unless a contradiction appears. That is a statement about where effort
should go, **not** an evidence class: almost none of it is formally verified, and the
repository's status ledger is what governs any claim about how strongly a particular
result is established.

A reason that has been raised and not answered is owed something. Serviceability
asks the boring, indispensable question underneath that: *can the owing actually
be discharged?* Not whether the reason is correct, and not whether the answer is
good — whether a bounded reasoner with finite room to manoeuvre can get to it at
all, and get to it in time.

## Claims and service

Two measures, and almost everything here is about keeping them apart.

The **obligation measure** records what is owed and when it was incurred. If a reason
`r` accumulates exposure `c_t` at each date, the obligation measure weights dates by
that exposure. This is Answerability's object; it is fixed by history and no
scheduler touches it.

The **service measure** records what was actually delivered. The learner allocates
some quantity of corrective authority at each date, and the service measure weights
dates by that allocation. This is the scheduler's object.

A learner that drives its *service-weighted* error to zero has done something, but
possibly not the thing that was asked. It may have been servicing the dates where
nothing was owed. The gap between the two measures is where a great deal of bad
behaviour can hide, and one of the round's more useful findings is that a natural
fairness condition — service is spread evenly across the surfaces that need it —
does **not** close it. A two-surface rotation can satisfy that condition, have
service-weighted error exactly zero at every horizon, and have obligation-weighted error
tending to one half.

## Why the measures need transport, not matching

The naive repair is to insist that service happen at the date the claim arose. That
is too strong, and obviously so: answering a challenge next week is not a failure of
answerability. What is needed is a **transport plan** — a bookkeeping of which
obligation mass, owed when, was discharged when — together with three conditions: the
plan is feasible against the authority actually available; it does not spend
wildly more service than there was claim; and the reason does not change too much
between being owed and being answered.

That last condition is the interesting one, and it is the one the mathematics
cannot yet supply for itself. See *What is still missing*.

There is an exact characterization of when transport with a fixed deadline is
possible at all — for every window, the claim arriving in it must fit inside the
authority available over that window extended by the deadline — and serving the
oldest outstanding claim first turns out to be optimal.

Neither is new. The feasibility criterion is a specialization of a classical
network-flow theorem, and the repository's proof **cites** that theorem rather than
proving it; the serve-oldest-first argument is the classical exchange argument,
independently written out here. The [prior-art ledger](Prior-Art) records which is
which, because the distinction between *using* a result and *resembling* one is
exactly what such a ledger is for.

## Three different questions that look like one

The round's most quotable result is a separation.

- **Persistence** — the reasoner keeps spending authority on this reason forever.
- **Eventual full service** — every claim is eventually discharged, with no
  deadline.
- **Uniform bounded delay** — every claim is discharged within some fixed time.

The first two turn out to be *the same question*. If a reasoner can afford to keep
spending, it can afford to eventually answer everything — by a diagonal argument
that gives each claim its own cheap moment rather than batching claims together.
The third is strictly stronger, and no amount of "cheap moments happen often
enough" substitutes for the exact criterion.

> Unlimited deferral makes "eventually answer every persistent claim" no harder
> than maintaining divergent effort. The substantive constraint enters only when
> **delay itself matters**.

That is worth sitting with. It means that if a practice's answerability demands are
satisfiable at all by a reasoner willing to keep working, then the whole content of
timeliness is in the deadlines — and a theory of answerability that does not say
when an answer is *late* has not yet said anything a scheduler can fail.

## The endpoint

Putting the pieces together: if the claims can be transported onto enforcement
dates that are both **timely** and **affordable in a specific sharp sense**, then
the same liability budget that keeps the learner from being exploited also drives
the settlement-friction residual to zero — and the only error left is the semantic change
the reason underwent while it waited to be answered.

This is the strongest statement the fixed-era theory makes. It is also
conditional in a way worth being precise about: it assumes a bound on that
semantic change, and nothing in the program yet supplies one.

## When answering is impossible, and how you would know

Two kinds of impossibility, and only one of them is certifiable.

If the claims already on the books cannot be answered by their deadlines, that is a
**finite** fact about a bounded stretch of dates, and there is an exact certificate
for it: the minimum cost of serving those claims on time, against the reasoner's
remaining budget. Every field of it is settled record.

If a reason can *never* be persistently afforded, that is a claim about the
infinite future, and no finite observation establishes it. Watching the cost stay
high for a long time is not a certificate. The honest response to that situation is
deferral and inquiry, not a record that the reason is unanswerable.

The asymmetry has a practical edge: a scheduler that can only bound its costs from
*above* — which is the safe direction for acting — is in the useless direction for
certifying impossibility.

## One warning the mathematics makes sharp

There are two entirely different reasons a moment can be cheap to enforce at. The
norm may be nearly satisfied already, or nobody may be pushing back against it.

The first is the good case: cheap because there is little left to correct. The
second is not, and a reasoner that persists only on such moments has bought the
appearance of sustained normative pressure without buying any conformance at all.

> **Cheap enforcement is not always conforming enforcement.**

## What is still missing

The endpoint theorem ends in a single term — how much the reason changed while
waiting — and nothing certifies that term. Within a single era it is a technical
gap. Across a self-revision it is the entire problem, because "how much of a reason
survives a revision" *is* that constant. This is the program's highest-value open
problem and it is where [Diachronic Answerability](Diachronic-Answerability) picks
up.

Also missing: whether a schedule can be timely and sharply affordable *at the same
time*; whether any of this survives when the cost of enforcing responds to the
enforcement; and whether the settlement-friction residual is ever actually zero for a norm a
real practice produces.

---

**Evidence.** The round is
[`2026-08-31-normative-affordability`](https://github.com/A-M-Berns/alignment-workspace/tree/939c459974fd1a7365f2c050e883eb1a630123cc/projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability),
with the endpoint theorem in
[`SHARP_TIMELY_SERVICE.md`](https://github.com/A-M-Berns/alignment-workspace/blob/939c459974fd1a7365f2c050e883eb1a630123cc/projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability/SHARP_TIMELY_SERVICE.md)
and a list of everything the round withdrew in
[`CONSISTENCY_AUDIT.md`](https://github.com/A-M-Berns/alignment-workspace/blob/939c459974fd1a7365f2c050e883eb1a630123cc/projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability/CONSISTENCY_AUDIT.md).
The dry canonical statement is the
[September checkpoint](https://github.com/A-M-Berns/alignment-workspace/tree/939c459974fd1a7365f2c050e883eb1a630123cc/projects/normativity/legitimacy/checkpoint-2026-09-01).

# Progress

**Status: open / unregistered.** Paper-derived research, not Established.

## The word does real work

"Progress" here does not mean the reasoner gets better at some task. It means
something narrower and harder to fake:

> A reason that stays live, is not answered, and recommends a specific available
> repair cannot be persistently ignored.

The failure mode it rules out is not error. It is *behavioral inertness*: the
reasoner keeps the criticism on the books, keeps servicing it, keeps producing
responses, and never actually changes what it does. Everything is recorded, the
score is kept, and nothing moves.

## What produces it

Three inputs, and Progress is what happens when they compose.

**Attention that does not run out.** From the answerability side: a case that stays
live receives unbounded cumulative attention. [Diachronic
Answerability](Diachronic-Answerability) delivers this and stops there, correctly
observing that unbounded attention is not by itself improvement.

**A reason-to-response structure.** From [Actionability](Actionability-and-Normative-Force):
a live reason favours some available repair over recognizable non-response, and
allocating enforcement intensity against a defect does a quantifiable amount of
work.

**Uptake.** Something that prevents the pressure from being absorbed without
effect. In the concrete construction this is the market maker's cumulative cap.

Put together: enforcement intensity allocated against a defect that persists must
accumulate work, the cap bounds how much work can be accumulated, and therefore the
defect goes to zero — at a rate that reads off the inverse square root of cumulative
enforcement intensity.

Where Uptake comes from is a correction worth recording. The program believed for a
while that it fell out of the underlying learning criterion for free. It does not:
the enforcement position sits inside the price-setting aggregate and is not
required to be efficiently computable, so the criterion never quantifies over it at
all. Uptake comes from the market maker's cap, and the earlier claim was withdrawn.

## Two forms, and which one gets the name

There are two forms of the statement and they are genuinely different:

    service-weighted Progress  --Service Transport-->  obligation-weighted Progress

the first being the learner-side mechanism theorem and the second the
Answerability-facing endpoint.

**"Progress" means the second.** The learner-side theorem keeps its qualifier and is
always *service-weighted Progress*, never the bare word.

**Service-weighted** Progress says the defect vanishes *on the dates the reasoner
worked*. That is what the learner delivers, and it has a complete derivation with a
rate — though like almost everything in this program that derivation is on paper and
not in a proof assistant.

**Obligation-weighted** Progress says the defect vanishes *on the dates something was
owed*. That is what answerability actually asks for.

The second does not follow from the first. A reasoner can drive its service-
weighted defect to exactly zero at every horizon while its obligation-weighted defect
tends to one half, simply by servicing the dates where nothing was wrong. Closing
the gap requires [Service Transport](Serviceability) — an explicit accounting of
which obligation, owed when, was discharged when.

The name went to the obligation-weighted form, and the tradeoff was taken knowingly:
the transport interface and its residual are now inside the settled statement, so a
Progress claim always carries a transport hypothesis. The alternative would have kept
a cleaner theorem about a quantity answerability never actually asks for — which is
the wrong thing to have a clean theorem about.

## The fairness condition that does not work

The obvious repair is a fairness requirement: over any long stretch, a decent
fraction of service exposes a surface where this reason can actually be answered.

It is not enough, and the countermodel is embarrassingly simple. Two surfaces, one
of which always has the defect and one of which never does, serviced in strict
alternation. The fairness condition holds. Service-weighted defect is exactly zero
at every horizon. Obligation-weighted defect tends to one half.

Of the four candidate interfaces the program considered for this, exactly one
transfers: exposing a *registered* surface on every service date, with confidence
bounded below. That gives a pointwise comparison between the two measures and the
conclusion follows immediately. The others give the fairness condition and nothing
more — and the countermodel *is* an instance of one of them.

## What Progress is not

It is not correctness. A reason may be wrong and the reasoner may respond to it
perfectly.

It is not closure. Progress is about the trajectory, not about issues eventually
being resolved.

It is not diachronic. Everything here is within one settled semantics, one
evaluator, no ontology revision. Progress *through* a self-revision would need the
content of a reason to be transportable across the revision, and nothing supplies
that yet.

---

**Evidence.** The schematic is
[`FINAL_SCHEMATIC.md`](https://github.com/A-M-Berns/alignment-workspace/blob/939c459974fd1a7365f2c050e883eb1a630123cc/projects/normativity/legitimacy/rounds/2026-08-30-progress-consolidation/FINAL_SCHEMATIC.md);
the countermodel and the interface audit are in
[`SERVICE_TRANSFER.md`](https://github.com/A-M-Berns/alignment-workspace/blob/939c459974fd1a7365f2c050e883eb1a630123cc/projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability/SERVICE_TRANSFER.md)
§3; the composition with rates is
[`FIXED_ERA_THEOREM.md`](https://github.com/A-M-Berns/alignment-workspace/blob/939c459974fd1a7365f2c050e883eb1a630123cc/projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability/FIXED_ERA_THEOREM.md).

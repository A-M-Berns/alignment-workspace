# Actionability and normative force

**Status:** the enforcement construction's three narrow results are **Established —
`lean-proved`**. The action theory built on them is open / unregistered.

## What it means for a reason to have force

A reason that changes nothing is not exerting normative pressure; it is being
recorded. So the program needs an account of how a constraint on what a reasoner
ought to believe becomes something that actually moves what it does believe —
without that account being either "we hard-code the constraint" or "we hope the
reasoner cooperates".

The construction is this. The reasoner's beliefs are prices in a market. A
constraint becomes a **trader**: a position that buys against the constraint's
violation, added to the aggregate the market maker prices against. It is an
ordinary participant, playing by the ordinary rules. Because the market maker
itself is untouched, every guarantee about the market maker survives intact.

What you get is a per-moment conformance bound: at any price the market maker will
accept, the constraint is violated by no more than a declared tolerance. Turn up
the intensity and the tolerance tightens.

Notice the shape of that. The underlying construction guarantees only that
exploitation vanishes *eventually*; this gives a bound *at a date*. That is a
finite-time strengthening of a well-known asymptotic guarantee, and it engages a
standing criticism of the original — that asymptotic inexploitability leaves finite
behaviour almost unconstrained.

## The thing force does not give you

Force is not a semantics: it operates on a region in price space, and whether that
region correctly expresses a normative demand is a separate lift.

Force is not a legitimacy certificate: nothing about compiling a constraint says
the constraint should have been there.

Force is not free. What it emits alongside the conformance guarantee is a
[liability obligation](Liability-and-Affordability) that some other layer has to
discharge.

## Actionability: what a unit of enforcement accomplishes

Given that pressure can be applied, how much correction does applying it buy?

The general form is: some amount of intensity, spent against some defect, yields
work; and if the work per unit of intensity tends to zero while the total intensity
diverges, the defect must be vanishing. The precise condition is exactly what you
would want it to be and nothing more:

> Correction converges **if and only if** the work a defect generates is bounded
> away from zero whenever the defect is bounded away from zero.

Convexity is not needed. It buys the *rate*, and only that. The projection
enforcement used in the concrete construction has a quadratic modulus and gets the
square-root rate; an older linear form gets a different one. One theorem covers
both, and the rate reads off the modulus.

This is a small result with a useful moral: several earlier statements in the
program carried convexity as a hypothesis, and it turned out to be doing no work at
the level of convergence.

## Several reasons at once

Does a certificate that enforcement helps reason `A`, and a certificate that it
helps reason `B`, give one that it helps both?

**Not if each reason is scored against its own region.** There is an exhibited pair
whose demands are jointly satisfiable and whose per-reason gain after aggregation
is negative — each reason's correction, evaluated in that reason's own terms, is
made worse by the other's.

**Yes if both are scored against the region they share**, with no convexity and no
separability assumption.

In the concrete construction this turns out to be true and *unused*: the compiled
position responds to the actual prices rather than being assembled from per-reason
commitments, so there is no aggregation step at which a per-reason certificate
could be invalidated. The failure mode is real for a different architecture, and
knowing which architecture has it is the point.

## What gets scheduled, and what merely happens

One typing decision, because getting it wrong inverts the sign of everything
downstream.

The natural reading of "how much did we serve this reason" is *how hard did the
enforcement position push*. That reading is wrong three times over. The push is
decided at the market's fixed point, so no scheduler can choose it. It is zero
exactly when the reason is perfectly satisfied, so the measure is undefined in the
best case. And it counts a moment as *better served* precisely because the reasoner
behaved worse.

Three things need keeping apart, and only the middle one is chosen:

- **service** — the broad relation this program cares about: an obligation receives
  the answering work it is owed. This is Answerability-facing and says nothing about
  markets;
- **enforcement intensity** — the scalar a scheduler fixes *in advance*, before any
  price is set. In this realization it is the resource by which service is supplied,
  and it is predictable and freely schedulable, which is what makes scheduling a
  well-posed question at all;
- **realized force** — the corrective position that actually materializes at the
  fixed point. Endogenous, and not anybody's to choose.

Service is not *identical* to enforcement intensity. Intensity is how a
market-embedded reasoner happens to pay for service; a different realization could
pay for it some other way.

> Under the wrong reading, **successful learning looks like starvation**: a
> reasoner whose defect decays geometrically under constant intensity has total
> realized force that converges, and appears to be receiving less and less service
> the better it does.

## Where this sits

Actionability is not downstream of scheduling and it is not upstream of it — it
sits *beside* it. Answerability fixes what is owed; Actionability fixes what a unit
of enforcement accomplishes; the scheduler fixes how much intensity goes where.
[Progress](Progress) needs all three and derives none of them from the others.

---

**Evidence.** The kernel-checked results are in
[`2026-08-16-traderized-enforcement`](https://github.com/A-M-Berns/alignment-workspace/tree/939c459974fd1a7365f2c050e883eb1a630123cc/projects/normativity/rounds/2026-08-16-traderized-enforcement),
with the caller-facing summary in
[`TRADERIZED_FORCE_INTERFACE.md`](https://github.com/A-M-Berns/alignment-workspace/blob/939c459974fd1a7365f2c050e883eb1a630123cc/projects/normativity/notes/TRADERIZED_FORCE_INTERFACE.md).
The action theory is
[`FIXED_ERA_THEOREM.md`](https://github.com/A-M-Berns/alignment-workspace/blob/939c459974fd1a7365f2c050e883eb1a630123cc/projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability/FIXED_ERA_THEOREM.md)
§1 and the typing argument is
[`SERVICE_FORCE_TYPING.md`](https://github.com/A-M-Berns/alignment-workspace/blob/939c459974fd1a7365f2c050e883eb1a630123cc/projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability/SERVICE_FORCE_TYPING.md).

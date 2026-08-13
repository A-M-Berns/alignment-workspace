# Trying to say "it took away my ability to fix this"

**Status:** `ci-only`; human register for
`prompts/2026-08-12-time-indexed-corrective-capability/`. The precise version is
`TIME_INDEXED_CORRECTIVE_CAPABILITY.md` beside this file.

## The problem this round attacked

The deference line has been stuck on something that sounds simple. We want to be able to
say: *the AI did something now, and because of it the human later cannot correct it.*
Not "the human is less likely to want to correct it" — cannot.

That sentence has been unsayable in our formalism. Two candidate structures were on the
table and each was missing what the other had. Cartesian frames can express whether
someone's choices still move the world, but they have no clock in them — calling one
frame "later" was us saying so. The source corpus has a construction with a real clock:
counterfactual continuations indexed by *when* the advisor's channel was cut, sharing
everything before the cut. But it has no notion of anyone's ability to act.

This round built the smallest thing that puts them together, then had an independent
reviewer try to break it.

## It broke

The reviewer found the flaw in the first thing it checked, and it is the kind of flaw
that is obvious once stated.

In the model, "cutting the advisor off" was implemented as *the advisor stops acting*. But
the state has no dynamics of its own — nothing happens unless the advisor acts. So cutting
the advisor off doesn't produce a continuation where the human carries on unadvised. It
produces a **freeze**. The world stops.

Which means the "family of counterfactual siblings" is not a family of counterfactuals at
all. Every state in it is a state the actual run already passed through. The reviewer
proved this:

> the continuation cut at time `n`, looked at at time `k`, is just the actual run at time
> `min n k`.

So the cut index isn't a second, counterfactual coordinate. It's the time coordinate
wearing a hat. And the foreclosure definition, which I had described as a statement about
a whole family of continuations, collapses to a statement about two adjacent moments on
one timeline: *coupled here, severed one step later*. True, well-formed, not vacuous — and
not about counterfactuals at all.

That is a real failure of the thing the round was for.

## The other two breaks

**The "it's not just a label" argument was circular.** I had argued that the capability
coordinate wasn't a meaningless flag, because the outcome function reads it. The reviewer
pointed out that this is trivially arrangeable: I had deliberately put a do-nothing field
in the model as a control, and they built the same frame around *that* field and got the
same certificate. Any boolean is "read by the outcome function" once you build a function
to read it. What actually distinguishes the real coordinate from the fake one is that the
transition rule reads and writes it — a fact about the dynamics, not about frames. My
control tested the wrong property.

**The simulation defence was a stipulation dressed as a result.** The point it was meant
to preserve is a good one: an AI predicting perfectly what a human would do does not
thereby gain the ability to do it. I encoded this as a gate that lets the principal's
choice through and blocks the advisor's. The reviewer observed that the gate is not
connected to anything — no run, no step, no part of the foreclosure definition consults
it — and that the theorem "prediction does not confer the effect" is proved by the
advisor's branch being the constant *false*, with the hypothetical predictor never even
applied. So the model asserts the conclusion rather than showing it, and the "actor" tag
is precisely the authorization flag the round set out not to need.

## What survived

One result, and it is worth having.

**Preserving someone's conclusions and preserving their ability to act are independent.**
There is a case where the advisor leaves the human's eventual view exactly where it would
have been and takes away their ability to correct; and a case where it moves their view
and leaves the ability intact. Neither notion implies the other. Both are exact finite
witnesses.

That matters because the source corpus's proposal is that legitimate influence is
influence that changes how fast someone's thinking converges but not where it lands. Our
line is about who retains the ability to intervene. Those are different targets, and this
is the first concrete demonstration rather than an argument. The caveat is honest: the
"endpoint" here is a single bit with no real deliberative dynamics, and one of the two
witnesses is true for a slightly degenerate reason — the endpoint never moves in either
run, rather than moving and coming back.

Also surviving: the shared-history machinery is genuinely proved rather than stipulated
(the reviewer attacked it and failed), and the foreclosure predicate does correctly pin
blame — if it holds, the advisor really did perform a severing act, at a unique time.

## What I'd say about the round

The verdict is `Mixed`, and it is closer to a negative than the earlier draft of this
document suggested. I wrote that draft before the review, with the verdict
`Representation-positive`, and it was wrong in the specific way this project keeps
catching: a real observation stated a notch past its evidence. The reviewer's findings
are folded into the Lean file as theorems, not answered in prose, so the refutations are
machine-checked alongside the results they refute.

The round did not close the representation gap. What it did was convert a vague sense that
"we need something with time in it" into one precise, checkable requirement.

## What should we work on next?

**One thing, and it is small.** Give the state dynamics that run *without* the advisor —
an environment that ticks, a principal who acts, a deliberation that continues. Everything
that failed here traces to the state standing still when the advisor stops. Once it
doesn't, cutting the advisor off produces a genuine alternative history instead of a
pause, and the questions this round answered negatively become live again.

Two smaller repairs go with it: make the corrective capability actually *do* something in
the model — at present exercising it flips a bit nothing reads, so "corrective" is a name
rather than a role — and either prove the simulation separation or state it plainly as an
assumption in the hypotheses where it is used, instead of encoding it as a gate nothing
consults.

I would not reach for new machinery. Nothing in the failure suggests the approach is
wrong; it suggests the model was too small in one identifiable place.

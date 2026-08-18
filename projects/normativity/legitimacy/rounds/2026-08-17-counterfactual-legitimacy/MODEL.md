# The model

## Runs and coupling

A `Fixture` holds an initial protected state, an exogenous encounter history, the
principal's standing plan, a ground store and an environment. `Fixture.run` takes
an advisor `Policy` and returns a `Run`. Two runs of one fixture therefore share
everything except the policy, and the coupling relation is a fact about how the
objects were built rather than a similarity judged afterwards.

The one channel that reaches outside the policy is `suppress_encounters`, by
which an advisor decides whether an encounter happens at all. `Fixture.coupled`
refuses a pair that differs there, and `uncoupled_pairs` reports the refusal, so
a class containing such a policy cannot pass by quietly skipping the comparison
that would have caught it.

The plan is state-dependent and identical across arms. A guarded action whose
precondition is unmet is a no-op: the merge fires only under a held licence, the
closure discharges on the first witness the current adequacy relation accepts and
suspends when there is none, the defeater applies only where the current bearing
relation licenses it. That is what lets one advisor policy produce a different
trajectory from the same algorithm without the advisor writing anything into the
record itself.

Determinism throughout; no randomness. The only arithmetic is integer repetition
counts and, on the deference side, exact `fractions.Fraction` rationals mirroring
the Lean file's rational carriers.

A run records the machinery **before every step and after the last**, not only
its endpoint. That is forced by transient capture: an advisor that moves a
standard, lets a liability close under it and restores the standard is invisible
to any endpoint object.

## The two channels

A `Message` is a set of `Item`s. Each carries **content**, a **coordinate** and a
**ground** — what a licensing judgment reads — and **repetitions**, **salience**
and **position**, which are delivery.

*Reason channel.* An item whose ground is provenance-valid for its coordinate and
whose content the principal's current bearing relation says bears there is a
licensed reason. The principal adopts what it proposes and cites the item's own
ground.

*Residual channel.* An item that is not a licensed reason is adopted anyway when
a delivery feature crosses a threshold. The principal cites `g-root`, the
conferred authority it genuinely holds over its own machinery, so the resulting
edit is indistinguishable from an autonomous revision — as it should be, because
the advisor supplied the selection and not the authority.

`ResidualRule` names the susceptibility: `repetition` (three or more),
`salience`, `presence` (any exposure), or `none`. The whole attack matrix runs
under the first two, so no verdict below depends on a single hand-picked
susceptibility. `presence` is used only in its own witness, and `none` is the
principal with no residual channel at all.

**Why the second channel is not optional.** With `none`, advisor input can reach
the protected machinery only through the reason port, `Z` factors through
`(E, L)` by construction of the transition rule, and every attack in the round
becomes unbuildable — the influenced arm and its sibling are the same run.
`TheResidualChannelIsWhatMakesTheConditionFalsifiable` checks exactly that. A
model with only the reason channel would have made the primary candidate
definitional, and its apparent success would have been an artefact of the
transition rule.

The channel is a susceptibility to how an input arrives rather than to whether
the practice licenses its content. It is one such susceptibility, and the round
does not claim it is the general form.

## The protected state

The object is defined by role in `LEGITIMACY_INTERFACE.md` §1 and implemented in
`src/response.py`: the normative response function, taken along the run.

Two presentations are kept alongside it because the round's results are about the
difference between them.

`ProtectedNormativeProjection` — provisional — is the tuple

```
(generation, entitlement, bearing, adequacy, identification)
```

The first four are the dispatch's starting point: every attack that survived the
procedural round operates through them, and its positive control legitimately
changes most of them. `identification` is what attack I forces, and the
counterexample is displayed rather than assumed; it is also not a field the
procedural round's `State` carries, so none of the four record-internal
conditions could have read it either.

`writable_fields` adds `noise`, a field the model carries so that a test can show
"every mutable coordinate" is the wrong object: the advisor writes it freely,
nothing it changes is an answer, and no clause fires.

The five-coordinate presentation is **sound and not complete**. Agreement on the
five implies agreement on every answer, over a generated family of sixteen
machineries; the converse fails off the alphabet, so a condition stated over the
coordinate list forbids changes that alter nothing the process answers. That is
the "too broad" direction the first pass looked for and could not see from
scenarios alone.

Practical authority and grants are not in it. No experiment here gave a reason to
include them.

## The licensed-reason trace

`L(t)` is the set of items admitted through the reason channel at step `t`. It
reads the pre-step machinery, the item's content and coordinate, and the item's
provenance. It never reads delivery, never reads a later state, never reads
performance, and never reads whether adopting the item turned out well. Reading
the pre-step state is not a leak but the shape of `Due : S -> D -> Prop`: a
demand is determined by the public pre-action state, and a trace that could not
read it could not be a trace of reasons at all.

Three things stay distinguishable, and the distinction is load-bearing in
different places: reason **content** (the reason channel), **delivery** (the
residual channel and the placebo control), and **selection** among available
reasons (the withholding attack, which neither of the first two reaches).

A reason named by `(content, coordinate)` is too coarse. Two revisions offered
under one name give identical traces and different protected states with no
residual channel involved — `TheCoarseTraceIsNotEnough`. The trace used
throughout is `(content, coordinate, proposal)`: a reason has to be individuated
finely enough to determine what it licenses.

## What is provisional

The scorekeeping fixture, the five coordinates, the residual rules, the split
between due and merely-licensed inputs, and every name introduced. `due_pool` in
particular is a fixture stipulation standing in for a substantive `Due`, which
this round does not derive and does not claim to have derived.

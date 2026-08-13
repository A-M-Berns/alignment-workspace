# Coverage interface

What has to be true for the theorem to say anything, stated as weakly as it can be.

## Four candidate shapes

| shape | condition | verdict |
|---|---|---|
| **density** | `M_T(g) >= rho_g T` | sufficient, and **stronger than needed** |
| **learning-rate** | `B_T(g) = o(M_T(g))` | **sufficient and weakest** of the four |
| **persistent-defect service** | a persisting latent defect is exposed within a bounded or sublinear delay | sufficient *if* it implies the second; not formulated here |
| **creditor coverage** | a party with standing can make a challenge due often enough | conceptually best motivated; reduces to the second once "often enough" is made precise |

They are not equivalent. Density implies learning-rate coverage; the converse
fails. With `B_T = O(sqrt(T |A| log K))` the learning-rate condition is
`M_T(g) >> sqrt(T)`, which permits the reason to be exposed on a vanishing
fraction of dates.

**This is the round's most useful structural gain.** Coverage need only dominate
the learning rate, not occupy positive density.

## Why the denominator is not optional

Under a schedule exposing the reason on perfect squares, `M_T = Theta(sqrt(T))`.
A learner that mishandles **every single selected occasion** still has
`Q_T/T -> 0`. The unconditional rate certifies nothing; the conditional rate is
what carries content. Tested at `T = 16, 64, 256, 1024`.

At the exact boundary `M_T = Theta(sqrt(T)) = Theta(B_T)`, the ratio `B_T/M_T` is
constant and the conditional rate is **not** driven to zero. The condition is
sharp in the fixture's arithmetic.

## Where coverage is not

Not inside the regret algorithm. The learner must not be responsible for
generating its own reasons — a learner that could would be marking its own paper,
and the exposure gate exists because charging unraised consequences is a
logical-omniscience norm.

So coverage is a hypothesis of the crown-jewel theorem, and the honest reading of
the theorem is **conditional on being asked**.

## The corrigibility composition

The dispatch asks whether this is where the two arcs meet. Answering its six
questions from what the merged corrigibility work actually established:

1. **What would corrigibility have to guarantee?** That the principal's ability to
   make a challenge *due* cannot be foreclosed — i.e. that the exposure-generating
   move stays available under every advisor policy.
2. **Is reachability enough?** No. The merged result is that a corrective
   capability survives every advisor run. That is a statement about the capability
   persisting, not about it being *exercised* at any rate. Coverage needs
   occasions, not the standing possibility of one.
3. **Is a service guarantee needed?** Yes, or a rate. Something of the form: the
   principal exercises the channel on at least `M_T` occasions, or the environment
   does. Neither arc currently supplies it.
4. **Universal over advisor policies?** Yes for the capability half, which the
   merged round has. The rate half is not a quantifier question; it is an extra
   assumption about the principal's behaviour.
5. **Which form of coverage?** Learning-rate. The composition would need the
   protected channel to be exercised `>> sqrt(T)` times, which is a very weak
   demand and is the reason this composition looks promising.
6. **Genuine interface or analogy?** **Genuine in shape, unproved in substance.**
   The corrigibility arc's object is "the principal can still raise it"; the
   learning arc's hypothesis is "it gets raised often enough". These are the same
   variable at two different strengths, and closing the gap is one assumption —
   an exercise rate — rather than a new formalism.

That is the most this round can say. The composition is stated as a target, not
claimed as a theorem, and nothing here proves that a protected channel is
exercised at any rate at all.

## What coverage does not fix

Coordinated standards drift. If the two scorekeepers jointly revise the practice
so that a reason ceases to be a reason, the burden disappears and the learning
theorem has nothing to say — correctly, since there is then no live reason to
respond to. That is a limit of the normative substrate, not of the regret
theorem, and adding a world-responsive oracle to defeat it is refused here.

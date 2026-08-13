# Learning dynamics

Whether the construction learns, or complies immediately with the repair graph.

## The transience condition, exactly

Theorem 18 plays `p^t`, the stationary distribution of the chain whose row `i`
mixes the active rules' images of `i`. A stationary distribution is supported on
the **recurrent** states. So:

```
p^t(b) = 0   whenever b is transient in the date-t rule graph
```

for any strictly positive weights, whatever has been observed.

**The graph.** Edge `i -> j` when some active rule sends `i` to `j`. The identity
is always in the class, so every action has a self-loop — and a self-loop does not
rescue a state from transience.

**The condition.** `b` is transient exactly when some action reachable from `b`
cannot reach `b` back. Tested directly:

| class | zero-mass actions |
|---|---|
| `hold -> acknowledge`, `disavow -> query` | `{hold, disavow}` |
| the same, plus `acknowledge -> hold` | `{disavow}` |
| the 3-cycle `hold -> acknowledge -> suspend -> hold` | `{}` |

So it is not that repairs make things transient; it is the **absence of a return
route** that does.

## Why a coherent repair class always hits it

A repair fires exactly when its selector fires — which is exactly the set of dates
`M_T(g)` counts. So at every selected date, `b_g` has an outgoing edge to
`r_g`. Its mass is zero at those dates unless the class supplies a route back to
`b_g` **active at that same date**.

A return route active at a selected date is a rule sending a repair target back
toward the bad response *while the reason is due*: "there is an exposed burden, so
having acknowledged, stop acknowledging". That is not a repair.

Hence for a normatively coherent class, `Q_T(g) = 0` at every date, and the
theorem's conclusion is reached without the learner ever making the mistake.

## Measured

Two classes on the same evolving fixture, driven by the repository's Theorem 18
learner.

| class | `Q_T` at `T=64` | early mass | late mass |
|---|---|---|---|
| one-way (`hold -> acknowledge`) | `0` | `0` | `0` |
| cyclic (adds `acknowledge -> hold`) | `7.98` | `0.1249` | `0.1247` |
| cyclic, loss carries no information | — | `0.1250` | `0.1250` |

Two things are visible in the cyclic row and both matter.

**Feedback does move the distribution.** Within the recurrent class `{hold,
acknowledge}` the share on `hold` falls — `0.500000, 0.499649, 0.499298` over the
first three dates — and then **freezes exactly when the margin goes to zero**,
which happens at date 8 when the fixture's environment stops producing exposed
burdens. Under the no-information control the share does not move at all. So the
adaptation is feedback-driven, not a predetermined decay.

**But the class's total mass is pinned.** It sits at `0.25` throughout. With most
actions absorbing, the chain is reducible, the stationary distribution is not
unique, and the implementation resolves the ambiguity from the initial uniform
distribution. The weights redistribute *within* a recurrent class and never
between classes.

## The pre-registered criterion

Fixed before looking, per the dispatch:

| clause | one-way class | cyclic class |
|---|---|---|
| (1) initial mass on the target `> 0` | **fails** — it is `0` | passes, `1/8` |
| (2) the pattern recurs | passes | passes |
| (3) updates depend on observed loss | passes | passes |
| (4) cumulative bad mass sublinear | passes trivially | passes |
| (5) late mass below early mass | vacuous | passes, narrowly |
| (6) no adaptation without information | passes | passes — flat under the control |

The coherent class **fails at clause (1)**: there is nothing to shed. The cyclic
class passes, and the cyclic class is normatively incoherent.

## What this settles

**The engine is capable of feedback-driven adaptation** — clause (6) is passed,
and the freeze at zero margin shows the movement tracks the signal.

**A normatively coherent repair class removes the occasion for it.** The better
the repair grammar, the more completely the construction complies immediately.

That is not a defect in the theorem, and it is arguably the outcome one wants: a
system that never persistently mishandles a reason is better than one that learns
not to. But it is not a learning curve, and the project's own prose promises one.

## What would be needed for the diachronic version

A no-regret learner against the same surgical class whose action distribution is
**not** the fixed point of the current rule mixture. That is a real constraint: the
fixed point is what makes swap-type regret self-consistent, and the internal-regret
algorithms surveyed in the primary source all compute one. Whether an
internal-regret minimiser exists that does not, and would still admit the surgical
lower bound, is **open** and is the concrete question a dynamics round should ask.

Two things that would **not** count, and the criterion rules them out: uniform
exploration, which manufactures a decay curve with no dependence on feedback
(clause 6); and warm-starting the weights, which moves the starting point without
making the movement informative.

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

## What survives, and what is withdrawn

**Survives — the graph theorem.** A repair fires exactly when its selector fires,
which is exactly the set of dates `M_T(g)` counts. So at every selected date
`b_g` has an outgoing edge to `r_g`, and its mass is zero at those dates unless
the class supplies a route back to `b_g` active at the same date.

**Withdrawn — the coherence inference.** The first pass went on to claim that a
*normatively coherent* class can never supply such a route, on the ground that it
would have to say "there is an exposed burden, so having acknowledged, stop
acknowledging". That inference was invalid, and this pass constructs the
counterexample.

A return route does not have to be licensed by the **same** reason. It can be
licensed by a different consideration that happens to be active simultaneously.
The `COMPETING` class uses two certificates that already existed in the merged
model and were not invented for this purpose:

```
exposed_consequential_burden   a raised consequence is unanswered
                               -> answer it rather than sit still

defeated_applicability         a commitment is precluded and unsuspended
                               -> do not take on further commitments while an
                                  incoherence is outstanding; sit still
```

The second is ordinary normative caution, not an anti-repair. Both hold in one
public state — an exposed burden together with a precluded commitment — and there
the graph has a cycle through `hold`, which becomes recurrent.

| class at that state | `hold` transient? | zero-mass set |
|---|---|---|
| `ONE_WAY` | yes | `{hold}` |
| `INCOHERENT` (same certificate licenses the undoing) | no | `{}` |
| `COMPETING` (different certificates) | **no** | `{}` |

`INCOHERENT` and `COMPETING` behave identically, which is the point: **recurrence
is no evidence of incoherence**, so the first pass's inference from one to the
other cannot be run in either direction.

**What replaces it.** Only the graph condition:

```
b_g transient in the active repair graph  ->  p_t(b_g) = 0
```

Whether a realistic normative grammar produces transient or recurrent targets is
now an open structural question about grammars, not something settled by
coherence. The construction above shows recurrent is reachable coherently.

## Measured

Three classes on the same evolving fixture, driven by the repository's Theorem 18
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

## The pre-registered criterion, on the coherent competing class

Clause (1) is now **passed by a coherent class**, which the first pass said was
impossible. Measured on `COMPETING` at `T = 48`, with the reason recurring:

| clause | verdict |
|---|---|
| (1) initial mass on the target `> 0` | **passes** — `p_1(hold) = 1/8`, under a class every edge of which is independently certified |
| (2) the pattern recurs | passes — the selector fires throughout |
| (3) updates depend on observed loss | passes |
| (4) cumulative bad mass sublinear | **not demonstrated** — see below |
| (5) late mass below early mass | **fails** — mass *rises*, `0.146 -> 0.250` |
| (6) no adaptation without information | passes — exactly flat at `0.125` under the uninformative control |

Clause (5) fails for a reason that is not about the learner. The margin is
positive on only 4–5 of the 48 dates: the fixture's vocabulary is finite, so the
supply of fresh exposable contents runs out and the reason stops recurring *with
a positive gap*. Once the gap is zero there is nothing to learn from, and mass
drifts back as the targeted action stops being transient.

**So the fixture cannot decide the dynamics question**, and this is a limitation
of the fixture rather than a finding about the engine: a finite content set cannot
sustain coverage. What the run does establish is clause (1) — a coherent class can
leave the learner holding mass on the targeted response — and clause (6), that
what movement there is tracks the signal.

## The regenerating fixture, and the decisive result

Every earlier fixture exhausted: a finite content set runs out of things to raise,
so the reason stopped recurring with a positive margin. `src/regenerating.py`
removes that defect and nothing else.

One demand type, regenerating each date. Two responses, so the active chain is
**irreducible** — which also removes the second confound, the reducible chain
whose stationary distribution the implementation had to disambiguate from the
initial uniform. `answer` discharges the demand, `hold` leaves it; the loss is `w`
if a demand is left outstanding, so the margin is exactly `w` at every date and
the loss stays bounded. The return edge is `hold` licensed against a *standing
incoherence* demand — a different reason, independently certified.

| `T` | `p_1(hold)` | early share | late share | `Q_T` | `Q_T/M_T` | control early → late |
|---|---|---|---|---|---|---|
| 16 | 1/2 | 0.469 | 0.011 | 2.74 | 0.171 | 0.500 → 0.500 |
| 64 | 1/2 | 0.394 | 0.000 | 5.23 | 0.082 | 0.500 → 0.500 |
| 256 | 1/2 | 0.281 | 0.000 | 10.17 | 0.040 | 0.500 → 0.500 |
| 1024 | 1/2 | 0.156 | 0.000 | 20.06 | 0.020 | 0.500 → 0.500 |

Mass on the inferior response, sampled every 32 dates at `T = 256`:

```
0.5000, 0.0948, 0.0060, 0.00031, 0.00002, 0, 0, 0
```

Every clause of the pre-registered criterion is met. `p_1 = 1/2` is substantial;
the reason recurs at every date (`M_T = T`); the margin is uniformly `1`; `Q_T`
roughly doubles as `T` quadruples, the `sqrt(T)` shape; the conditional rate falls
monotonically; and **the matched uninformative control does not move at all** —
exactly `1/2` at both ends, at every horizon. No exploration schedule, no warm
start, no graph change over time. The surgical bound holds with equality
(`regret = delta * Q_T = 10.1727` at `T = 256`).

## What the witness licenses, and what it does not

Licensed:

> There exist coherent recurrent answerability processes with sustained
> positive-margin feedback on which the Blum–Mansour construction begins with
> substantial mass on an inferior response and adaptively sheds it because of
> informative feedback.

**Not** licensed: `p_t(b) -> 0` as a theorem. The observed decay is a measurement
on one process at four horizons, and no proof of convergence falls out of it.

## What this settles

**The graph theorem stands.** Transience decides zero mass, and the identity
self-loop does not rescue a state.

**The coherence inference does not.** A coherent class *can* leave its target
recurrent, via an independently certified competing reason. So "immediate
compliance" is a property of one-way repair graphs, not of good repair grammars.

**The engine is capable of feedback-driven adaptation** — the no-information
control is exactly flat, and where movement occurs it freezes when the margin
does.

**The dynamics question is answered, positively.** The earlier fixture could not
sustain a recurring reason with a positive margin; the regenerating one can, and
on it the learner sheds mass under feedback while the control stays flat. The
obstruction was the fixture, exactly as the refinement pass predicted, and not the
engine.

## The alternative-learner question is closed for now

The refinement pass asked whether a no-regret learner is needed whose
distribution is not the fixed point of the current rule mixture. On this evidence
**no**: the fixed point does not block the dynamics. Both apparent obstructions
were artefacts — one-way graphs, and reducible chains with pinned class mass — and
neither survives a coherent irreducible graph with sustained coverage.

What remains genuinely open is a *proof*: the witness is four horizons on one
process, not a convergence theorem.

Two things that would **not** count, and the criterion rules them out: uniform
exploration, which manufactures a decay curve with no dependence on feedback
(clause 6); and warm-starting the weights, which moves the starting point without
making the movement informative.

# The crown-jewel theorem

The strongest statement this programme should presently aim to prove, with what it
assumes, what it concludes, and what it refuses to say.

---

## Definitions

An **answerability process** is a tuple `(S, A, G, T)`:

- `S` a set of public pre-action normative states;
- `A` a finite response set, fixed and horizon-independent;
- `G : S -> [0, L]^A` a bounded prospective loss generator;
- `T : S x A x E -> S` a transition, so the process may be endogenous.

At date `t` the state `S_t` is fixed before the learner acts, the learner plays a
distribution `p^t`, an action is drawn, and `S_{t+1} = T(S_t, a_t, e_t)`. When
`ell_t` becomes available is a separate question, settled under *Information
order* below.

The theorem consumes three separate interfaces — `INTERFACES.md` has the
architecture:

```
Due      : S -> D -> Prop        a public reason presently calls for an answer
Licensed : S -> D -> A -> Prop   this response is admissible to that reason
Loss     : S -> A -> [0, L]      answerability performance in the practice
```

A **compiled surgical repair** `g = (d_g, b_g, r_g)` is what the compiler
produces from the first two, together with a target source response:

```
E_g(S)  =  Due(S, d_g)                       the selector
licence :  Licensed(S, d_g, r_g)             admission to the class
F_g^t(b_g) = r_g  where E_g(S_t),  F_g^t(a) = a otherwise
```

**A repair is not the primitive normative object.** It is the theorem-facing
object handed to the online-learning engine after normative compilation, and the
compiler consults `Due` and `Licensed` and never the loss.

**Register.** Let `H_t` be the strict history before date `t`. Then `S_t`, `p^t`
and `E_g(S_t)` are `H_t`-measurable, and the action `a_t ~ p^t` is drawn after
`p^t` is committed. Under genuine sampling the state depends on `a_t`, so **all
the counters below are random variables**:

```
M_T(g) = sum_{t <= T} 1[E_g(S_t)]                     occasions the reason was due
Q_T(g) = sum_{t <= T} 1[E_g(S_t)] * p^t(b_g)          mixed mass on the bad response
N_T(g) = sum_{t <= T} 1[E_g(S_t)] * 1[a_t = b_g]      drawn bad responses
R_T(g) = sum_t <p^t, ell_t> - sum_t <F_g^t(p^t), ell_t>
```

`R_T(g)` scores the transformed distribution against **the same date's loss
vector**. No comparator trajectory appears.

**Information order.** Determination and observability are different, and the
theorem needs both stated:

```
history H_t  ->  state S_t  ->  learner commits p^t
                                      |
                     ell_t = G(S_t) enters the update, not the choice
                                      |
                               draw a_t ~ p^t  ->  S_{t+1}
```

`ell_t` is *determined* when the date opens — that is what "prospective" means —
but the learner does not read it when choosing `p^t`. It enters at the weight
update. Checked directly against the implementation.

---

## Hypotheses

**H1 Boundedness.** `ell_t in [0, L]^A`.

**H2 Prospectivity.** `ell_t` is determined by `S_t` before the date's action is
drawn. Adaptivity in the strict past is permitted and does not need to be
restricted.

**H3 Full information.** The whole vector `ell_t` is observed.

**H4 Certified class.** A finite class `Gcal` of `K` repairs compiled from a
`Licensed` relation satisfying the interface discipline of `INTERFACES.md`
(protocol-legal, causal, loss-blind, non-laundering), fixed before play.

The theorem quantifies over `Licensed`; it does not construct one. **Substantive
soundness** — that a particular `Licensed` is reason-connected, scope-correct and
defeater-respecting — is a property of an instantiation, and is what a relational
answerability model would have to prove about its own implementation.

**H5 Margin.** For each `g`, a `delta_g > 0` with
`ell_t(b_g) - ell_t(r_g(S_t)) >= delta_g` at selected dates. Derivable rather than
assumed for a subclass — see below.

**H6 Coverage.** `M_T(g)` outgrows the learning scale
`L sqrt(T |A| log (M K_eff))`. Stated against the scale rather than against
`B_T(g)`, so the hypothesis does not mention the learner's own output — which
makes the absence of circularity checkable by inspection.

**H4 and H6 are interfaces, not results**, and this is the round's final
structural claim: they are *typed sockets*, not gaps in the proof. The abstract
theorem is a genuine conditional result about any process supplying them; a
substantive instantiation theorem is separate work on `Due`, `Licensed` and
performance.

---

## Learner construction

Blum–Mansour Theorem 18 over `A` with the `K` maps `F_g^t` and one time selector.
Regret is a **conclusion** of the construction, not an assumption:

```
R_T(g) <= B_T(g) = O( L * sqrt( T * |A| * log (M K_eff) ) )     for every g in Gcal
```

with the counts stated exactly rather than asymptotically: `|A|` is the response
count; `M = 1` time selector, since the selectors are folded into the rules;
and **`K_eff = K + 1`** — the `K` repairs *plus the identity*, which the source's
own internal-regret family includes and which the implementation passes as its
first map. Writing `log K` would undercount by one rule.

The bound holds for every `g` simultaneously, from one learner. Nothing in its
proof requires the loss sequence to be oblivious, frozen, or exogenous; the proof
is a weight-potential argument on the realized `(p^t, ell_t)` pairs, so it holds
on every realized history.

---

## Finite-horizon guarantee

**Lemma (surgical lower bound).** For each `g`,

```
R_T(g) = sum_{t : E_g(S_t)} p^t(b_g) * ( ell_t(b_g) - ell_t(r_g(S_t)) )
      >= delta_g * Q_T(g)
```

Because `F_g^t` is the identity off `b_g`, the per-date difference has exactly one
term and nothing cancels.

**Theorem (conditional bad-response rate).** For every `g in Gcal` with
`M_T(g) > 0`,

```
Q_T(g) / M_T(g)  <=  B_T(g) / ( delta_g * M_T(g) )
```

---

## Asymptotic corollary

Stated against the learning scale rather than against the learner's own output, so
the hypothesis does not mention the conclusion's machinery:

```
M_T(g) / ( L * sqrt( T * |A| * log (M K_eff) ) )  ->  infinity
```

Whenever that holds — equivalently `B_T(g) = o(M_T(g))` —

```
Q_T(g) / M_T(g)  ->  0.
```

With the class and response set fixed this is `M_T(g) >> sqrt(T)` — **weaker than
positive density.** A reason exposed on a vanishing fraction of dates still gets
the conclusion, provided it is exposed often enough to outgrow the learning rate.
The `sqrt(T)` form is the simplified reading; the exact condition is the displayed
ratio, which carries `|A|` and `K_eff`.

---

## Where the margin comes from

H5 can be discharged for a class rather than assumed. For the acknowledge schema:

```
repair          answer the exposed burden
discharges      one exposed unacknowledged consequential commitment
weight          w
side condition  taking it up adds no further exposed unacknowledged content
                and precludes nothing
```

Under that side condition — itself a public predicate reading no loss —
`delta_g = w` exactly. Verified on the fixture: the certificate's weight is `1/2`
and the observed margin is `1/2`.

**Margin-certified repairs** are those whose improvement follows from the loss
construction under a public side condition. The rest keep H5 as a hypothesis, and
the fixture carries a lawful repair with margin `-2` to keep the distinction
visible.

---

## Normative interpretation

What the numerator counts is mass on **one response to one kind of reason**. What
the denominator counts is **occasions of that kind of reason**. The theorem says
the ratio vanishes.

So the reasons do not go away. Challenges keep arriving; disagreement persists;
the learner may rebut rather than revise. What disappears is *a recurrently
inferior way of responding to a kind of reason that the practice itself certifies
a better response to*.

"Moved by reasons" cashes out as: the comparator is admitted to the class by a
public certificate, evaluated without reference to what it earns. "Improves"
cashes out as: sublinear regret forces the conditional rate to zero on
sufficiently recurrent occasions.

---

## Non-claims

- Not convergence to moral truth, to a unique norm, or to any fixed target.
- Not elimination of disagreement.
- Not a human veto.
- Not counterfactual trajectory optimality — replay is a strictly stronger and
  separate claim, and remains blocked.
- Not protection against reasons never being raised. That is H6, and it is an
  assumption.
- The **primary statement is pathwise**: the surgical inequality and Theorem 18's
  bound both hold on every realized history, so `Q_T(g) <= B_T(g)/delta_g` is a
  statement about each trajectory, not an average over them.
- The sampled-action register is separate and weaker. `E[N_T] = E[Q_T]` — **not**
  `E[N_T] = Q_T`, which is ill-typed because `Q_T` is itself random. Structurally
  `N_T - Q_T` is a sum of martingale differences with conditional mean zero.
  Almost-sure or high-probability control of `N_T/M_T` needs a concentration
  argument not supplied here, and `M_T` random means `E[N_T]/M_T` is not a
  well-formed quantity either.
- Not an anytime guarantee: `beta` is horizon-tuned.

---

## Remaining open hypotheses

**H4, repair-language adequacy.** A finite hand-built class is a legitimate
hypothesis and an inadequate theory. What a paper needs is a generated grammar
with a complexity model, plus the recurrence constraint below.

**H6, coverage.** Stated, not proved. Nothing in the learner generates its own
reasons, and it should not.

**The construction does learn where the graph permits it.** Where the targeted
response is transient in the active graph, the stationary construction gives
`Q_T(g) = 0` identically and the theorem is satisfied by immediate compliance.
Where a return route is active — which a coherent class supplies via an
independently certified competing reason — the learner starts with mass on the
target and sheds it under feedback. On a regenerating fixture with sustained
coverage and a uniform margin, mass on the inferior response falls from `1/2` to
below `10^-4`, while a matched uninformative control stays exactly at `1/2`. That
is a **witness**, not a general convergence theorem. See `LEARNING_DYNAMICS.md`.

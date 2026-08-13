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

At date `t` the state `S_t` is fixed before the learner acts, `ell_t = G(S_t)` is
available in full, the learner plays a distribution `p^t`, an action is drawn, and
`S_{t+1} = T(S_t, a_t, e_t)`.

A **certified surgical repair** `g` is `(E_g, b_g, r_g, c_g)`:

- `E_g : S -> {0,1}` a public selector, a predicate of the state;
- `b_g in A` one source response;
- `r_g : S -> A` a replacement;
- `c_g` a normative certificate, evaluated against public status and never given a
  loss;

inducing `F_g^t(b_g) = r_g(S_t)` where `E_g(S_t)`, and `F_g^t(a) = a` otherwise.

**Counters.**

```
M_T(g) = |{ t <= T : E_g(S_t) }|              occasions the reason was due
Q_T(g) = sum_{t <= T : E_g(S_t)} p^t(b_g)     mass on the bad response there
R_T(g) = sum_t <p^t, ell_t> - sum_t <F_g^t(p^t), ell_t>
```

`R_T(g)` scores the transformed distribution against **the same date's loss
vector**. No comparator trajectory appears.

---

## Hypotheses

**H1 Boundedness.** `ell_t in [0, L]^A`.

**H2 Prospectivity.** `ell_t` is determined by `S_t` before the date's action is
drawn. Adaptivity in the strict past is permitted and does not need to be
restricted.

**H3 Full information.** The whole vector `ell_t` is observed.

**H4 Certified class.** A finite class `Gcal` of `K` certified surgical repairs,
fixed before play.

**H5 Margin.** For each `g`, a `delta_g > 0` with
`ell_t(b_g) - ell_t(r_g(S_t)) >= delta_g` at selected dates. Derivable rather than
assumed for a subclass — see below.

**H6 Coverage.** `B_T(g) = o(M_T(g))`, where `B_T(g)` is the regret guarantee.

**H4 and H6 are interfaces, not results.** They are where repair-language
adequacy and inquiry enter, and the theorem states them rather than hiding them.

---

## Learner construction

Blum–Mansour Theorem 18 over `A` with the `K` maps `F_g^t` and one time selector.
Regret is a **conclusion** of the construction, not an assumption:

```
R_T(g) <= B_T(g) = O( L * sqrt( T * |A| * log K ) )       for every g in Gcal
```

simultaneously, from one learner. Nothing in its proof requires the loss sequence
to be oblivious, frozen, or exogenous; the proof is a weight-potential argument on
the realized `(p^t, ell_t)` pairs.

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

Whenever `B_T(g) = o(M_T(g))`,

```
Q_T(g) / M_T(g)  ->  0.
```

With `B_T = O(sqrt(T |A| log K))` this is `M_T(g) >> sqrt(T)` — **weaker than
positive density.** A reason exposed on a vanishing fraction of dates still gets
the conclusion, provided it is exposed often enough to outgrow the learning rate.

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
- Not a pathwise statement. `Q_T` is mixed mass; `E[N_T] = Q_T`; almost-sure
  frequency needs concentration not supplied here.
- Not an anytime guarantee: `beta` is horizon-tuned.

---

## Remaining open hypotheses

**H4, repair-language adequacy.** A finite hand-built class is a legitimate
hypothesis and an inadequate theory. What a paper needs is a generated grammar
with a complexity model, plus the recurrence constraint below.

**H6, coverage.** Stated, not proved. Nothing in the learner generates its own
reasons, and it should not.

**The construction is not a learning curve.** For any repair class whose rules
point away from mistakes, the targeted response is transient in the rule-mixture
chain at exactly the dates the repair fires, so the stationary construction gives
`Q_T(g) = 0` identically. The theorem is satisfied by immediate compliance. See
`LEARNING_DYNAMICS.md`.

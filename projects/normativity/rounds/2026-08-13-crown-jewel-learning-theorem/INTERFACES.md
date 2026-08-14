# The three interfaces

The abstraction boundary of the crown-jewel theorem, frozen.

```
        relational answerability substrate
                      |
        +-------------+-------------+
        |             |             |
        v             v             v
       Due        Licensed      Performance
   (reason is    (response is   (bounded loss,
    presently     admissible)    and margin)
    owed)             |
        |             |
        +------+------+
               |
               v
      compiled surgical repairs
               |
               v
        Blum-Mansour engine
               |
               v
   conditional bad-response rate -> 0
```

`CertifiedSurgicalRepair` is what comes **out** of the compiler, not the
fundamental normative object. That was the packaging error the final pass fixed.

## I. Demand

```
Due : S -> D -> Prop
```

`Due(S, d)` — the public reason `d` presently calls for an answer.

What the abstract theorem needs from it:

- determined by the public pre-action state;
- causal and non-anticipating;
- **not** defined by current loss advantage;
- rich enough to generate the comparator's selector;
- exposes the quantity whose recurrence `M_T` counts.

**Coverage is a quantitative property of this interface**, not a further normative
primitive. The theorem's H6 says the occasions `Due` generates outgrow the
learning scale; it says nothing about what makes a reason due.

Deriving `Due` from scorekeeping, standing, challenge and inquiry is the next
programme and is deliberately not attempted here.

## II. Certified response

```
Licensed : S -> D -> A -> Prop
```

`Licensed(S, d, r)` — `r` is an admissible response to `d` in state `S`,
**independently of what loss `r` receives**.

The seven clauses from the previous pass split cleanly along the abstract /
substantive line:

| clause | belongs to |
|---|---|
| protocol-legal | **interface discipline** — a requirement on any admitted implementation |
| causal | interface discipline |
| loss-blind | interface discipline |
| non-laundering | interface discipline |
| reason-connected | **substantive soundness** — a property of a particular `Licensed` |
| scope-correct | substantive soundness |
| defeater-respecting | substantive soundness |

## III. Performance

```
Loss : S -> A -> [0, L]
```

Answerability performance **within the public practice**. Not normative truth, and
the theorem is not stronger if read that way.

Margin is a separate question about this interface:

```
Loss(S, b) - Loss(S, r) >= delta > 0
```

The division of labour, stated once:

```
Licensed   is r an admissible answer?
margin     does r perform uniformly better than b?
regret     can the learner keep putting mass on b?
```

A residual-burden factorization

```
Loss(S, a) = sum over due d of  w(d) * rho(d, S, a)
```

is a natural way to *build* such a loss and is **not** required by the proof.

## Why the separation is load-bearing

If `Licensed` collapsed into "has lower loss", admission to the comparator class
would be a function of what a repair earns, the normative reading would be gone,
and the learner could game the criterion by optimising. Two witnesses keep the
collapse visible in both directions:

- a **licensed response with negative margin** — `hold`, admissible against a
  standing incoherence, strictly worse than `answer` when a demand is due;
- an **unlicensed response with lower loss** — `answer`, which lowers the loss but
  is not an admissible answer to the incoherence demand.

`test_final.T2LicenceIsNotPerformance` carries both.

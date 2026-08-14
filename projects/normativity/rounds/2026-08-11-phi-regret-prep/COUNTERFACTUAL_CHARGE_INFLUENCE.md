# How far one local edit reaches

The question: under the conservative replay semantics, does one lawful local edit
have bounded influence on future charge accounting?

**The verdict is sharply conditional, and fencing alone is not the condition.**

## The measurements

One history, one edit, four accounting configurations. The edit withdraws the
disposition at date 0 from a merits ruling to a decline on a ripeness ground, and
is admitted; every other occasion of the run is left alone. The actual run rules
on the merits throughout and is charged nothing, so every number below is the
whole of the divergence the edit caused.

| configuration | horizon 12 | horizon 24 | grows with `T` |
|---|---|---|---|
| `E9` fenced, the edit's account contains only the edited occasion | 2 | 2 | no |
| `E10c` fenced, solvency coupling switched off | 2 | 2 | no |
| `E10b` fenced, one account for the whole run | 24 | 48 | **yes** |
| `E10` pooled, one shared reserve | 24 | 48 | **yes** |

`E10b` and `E10` are the same number for the same reason, which is the finding: a
fence containing the whole run is a pool.

## A — the fenced accounting lemma

**Statement.** Let `φ` fire only at occasions belonging to accounts `S`. Then

```
| L_T(H^φ) − L_T(H) |  ≤  Σ_{s ∈ S} Λ_s ,    Λ_s = Σ_{t ∈ s} ℓ_max(t)
```

where `Λ_s` is the account's admitted lifetime liability: the sum, over the
occasions that land in `s`, of the maximum charge their bound schedules permit.

**Proof.** Two parts. Outside `S` the two runs agree occasion by occasion:
arrivals, intervals and schedules are frozen; guards read the actual prefix, so
the fire set is the same object in both runs; an account's suspension depends
only on its own balance, and no occasion outside `S` has a charge the edit can
move. Inside `S`, both runs' charges lie in `[0, Λ_s]` by the definition of
`ℓ_max`. The difference of two numbers in one interval is at most its width. □

**This is an accounting lemma and nothing more.** It says the edit cannot reach
outside the fence; it says nothing about how far it reaches inside one. The
`untouched_identical` field of `LocalityCheck` records the first half separately
from the bound so that a reader can see which half is doing work.

**The bound is attained.** `E10b` is one fenced account containing the whole run:
divergence 24 at horizon 12 against a bound of 24, and 48 against 48. So the
lemma is tight and, at that granularity, useless — `Λ_s` is `Θ(T)`.

## B — pooled solvency: the divergence witness

`E10`. One shared account with reserve 1. The edit raises the date-0 charge from
0 to 2, which exhausts the reserve at date 0. Service is withdrawn from every
later occasion, each of which is then declined at 2 rather than ruled on at 0.

```
divergence(T) = 2T
```

24 at horizon 12, 48 at horizon 24, from a **single** local edit at a single
occasion. The prediction the round set out to test — that a pooled solvency
coupling makes counterfactual divergence grow with the horizon — holds, exactly,
with an exhibited witness.

## C — what the condition actually is

Fencing is not what bounds the influence. Two things are, and they are separable:

**The coupling.** With `suspends=False` — reserves accounted, service never
withdrawn — the divergence is exactly the sum of the per-occasion charge
differences at the occasions where `φ` fired:

```
| L_T(H^φ) − L_T(H) |  ≤  |fire set| · ℓ_max
```

`E10c` attains this at 2 for a one-firing comparator at every horizon. This is
the bound an online-learning reduction needs, and it is horizon-free.

**Fence granularity.** With the coupling on, the bound is `Σ_{s∈S} Λ_s`, and
`Λ_s` is horizon-sized unless the fence is small. Per-occasion fences recover the
horizon-free bound; a fence per stream gives a bound proportional to the stream's
lifetime liability; one fence gives nothing.

**So:** *bounded counterfactual influence holds under the solvency coupling only
to the extent that the fence containing the edit is short-lived, and holds
unconditionally without the coupling.* Neither half is a fact about fencing as
such, and a round that reported "fencing gives locality" would have reported the
`E9` configuration and not looked at `E10b`.

## D — what this costs the next round

The clean reduction to ordinary Φ-regret is available in the v1 environment, and
its price is declaring `suspends=False`. That is a real assumption: `CS-N1` is a
necessity witness for the solvency coupling in the demand results, so switching
it off is switching off a hypothesis the line elsewhere shows is load-bearing.

`PHI_REGRET_TEST_SPEC.md` §1 declares it, and `OPEN_PROBLEMS.md` §2 carries the
question of whether a φ-regret statement survives its reinstatement — which is
the first place this preparation could turn out to have prepared the wrong thing.

## E — what did not happen

Nothing failed to reproduce. The pooled witness was predicted and constructed;
the fenced bound was predicted and is tight; the horizon-sized fenced case was
**not** predicted by the dispatch, which expected fencing to be the dividing
line, and it is the round's one unforced correction.

# The theorem target

## Three claims, kept apart

**Claim A — local response learning.** On the actual trajectory, when a public
normative pattern occurs, the mixed mass the learner puts on a particular bad
response to it vanishes in density.

**Claim B — A plus coverage.** A, together with a condition ensuring relevant
latent reasons keep becoming publicly due.

**Claim C — counterfactual trajectory improvement.** The actual run compared
against the run that would have occurred had the repair been applied throughout.

The merged round established that **C is blocked** for the additive reduction, and
recorded that as blocking the learning arc. That reading is what this round
revises: C was never what the source theorem delivers, and A does not need it.

---

## Actual-Trajectory Repair Lemma

*Provisional name.* Stated abstractly; nothing in it mentions scorekeeping.

**Setting.** A finite action set `A`. At each date `t = 1 … T` a learner produces a
distribution `p^t` over `A`; a loss vector `ell_t : A → [0, L]` is determined
before the date's action is drawn, and may depend arbitrarily on everything
strictly earlier, including the learner's realized past actions.

**The rule.** A modification rule `g` with date-`t` map `F^t : A → A` satisfying,
for a distinguished source action `b`, a public selector `E_t` determined by the
strict history, and a replacement `r_t`:

```
F^t(b) = r_t   if E_t
F^t(a) = a     otherwise, and for all a != b
```

**The gap.** There is `delta > 0` with `ell_t(b) - ell_t(r_t) >= delta` whenever
`E_t` holds.

**The quantities.**

```
R_T(g) = sum_t < p^t, ell_t >  -  sum_t < F^t(p^t), ell_t >
Q_T    = sum_{t : E_t} p^t(b)
```

**Conclusion.**

```
R_T(g) >= delta * Q_T
```

and therefore, if the learner guarantees `R_T(g) = o(T)`,

```
Q_T / T -> 0.
```

**Proof.** `F^t(p^t)` differs from `p^t` only by moving `p^t(b)` from `b` to
`r_t`, and only at selected dates. So the per-date difference is

```
< p^t, ell_t > - < F^t(p^t), ell_t >  =  p^t(b) * ( ell_t(b) - ell_t(r_t) )
```

at selected dates and `0` elsewhere. Summing and applying the gap gives the
inequality. ∎

**What the proof does not use.** No trajectory other than the actual one. No
assumption that `ell` is oblivious, frozen, or additive across dates. No claim
about `S_t^g`, the state the comparator would have produced — that object never
appears. This is the content of the round: **the lemma is replay-free by
construction, not by assumption.**

**Where the surgical shape is load-bearing.** If `F^t` rewrites any action other
than `b`, the per-date difference acquires terms
`p^t(a)(ell_t(a) - ell_t(F^t(a)))` of either sign, and no lower bound in terms of
`Q_T` survives. `test_a_broad_comparator_cancels_and_loses_the_bound` displays a
comparator whose total regret is strictly below the surgical rule's on the same
run.

---

## Instantiation, and the exact numbers

Fixture: the merged round's scorekeeping model, three agents, eleven contents. The
environment replenishes — it raises a fresh burden or a fresh entitled challenge
every date — so the pattern recurs rather than saturating.

Target pattern and repair:

```
selector     an exposed consequential burden exists
source       hold
replacement  acknowledge
certificate  exposed_consequential_burden
```

Against the constant policy that always plays `hold`:

| `T` | selected dates | `Q_T` | `delta` | `R_T(g)` | `delta · Q_T` |
|---|---|---|---|---|---|
| 4 | 4 | 4 | 1/2 | 2 | 2 |
| 8 | 8 | 8 | 1/2 | 4 | 4 |
| 16 | 16 | 16 | 1/2 | 8 | 8 |
| 32 | 32 | 32 | 1/2 | 16 | 16 |

Equality throughout, as the proof predicts for a surgical rule with a constant
gap. Exact rationals.

Read as the contrapositive: a policy that keeps full mass on the pattern accrues
regret `T/2`, which is linear, so no learner with an `o(T)` guarantee can do it.

---

## The replay control, on the same run

The quantity the previous round measured, computed on the identical trajectory:

| `T` | actual total | comparator-trajectory total | difference |
|---|---|---|---|
| 4 | 23/2 | 13/2 | 5 |
| 8 | 63/2 | 37/2 | 13 |
| 16 | 143/2 | 85/2 | 29 |
| 32 | 303/2 | 181/2 | 61 |

These are different numbers from the local column, they grow at a different rate,
and their ratio to the local regret is increasing. **Both facts hold on one run.**
The replay divergence is real and it leaves the lemma's hypotheses and conclusion
untouched, because the lemma never reads the transformed trajectory.

---

## Which registers the conclusion lives in

Three quantities, and only the first is bounded here.

```
Q_T        cumulative mixed mass on (selector, b)          <- Theorem 18 bounds this
E[N_T]     expected count of sampled bad responses         <- equals Q_T under ordinary sampling
N_T / T    realized frequency, almost surely               <- NOT established
```

`E[N_T] = Q_T` by taking expectations date by date, since the action is drawn from
`p^t`. The step to an almost-sure statement needs a martingale concentration
argument that is not in the source and is not attempted here.

Separately: the source tunes `β` from `T`. The asymptotic gloss `Q_T/T → 0` is
read across a family of horizon-tuned runs, not from one anytime learner. A
doubling construction would be needed for the latter and is not supplied.

---

## What is proved, and at what strength

| statement | strength |
|---|---|
| the lemma's algebra | derivation, written out above; exact finite checks at four horizons |
| the surgical shape is necessary for it | fixture witness — a broad comparator with strictly lower regret |
| the source theorem applies to an endogenous loss process | source reading, §9 and §11 of `SOURCE_AUDIT.md` |
| replay divergence does not touch the local claim | fixture witness, both quantities on one run |
| `R_T(g) = O(√(T N log K))` for this class | derived instantiation of the cited theorem, not reproved here |
| `E[N_T] = Q_T` | one line, stated above |
| pathwise frequency | **not established** |
| anytime guarantee | **not established** |

Nothing here is registered and nothing is kernel-checked. The lemma's arithmetic
is a clean Lean port target; the existing `recurrentFailure_lowerBound` takes the
lower bound as a *hypothesis*, so what it would add is the derivation of that
hypothesis from the surgical shape.

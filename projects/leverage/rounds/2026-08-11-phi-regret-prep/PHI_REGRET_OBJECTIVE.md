# The objective

## 1. One charge, not a scalarization

The loss is the **docket liability** of the practical-demand layer: default
tariffs and refusal tariffs, exact rationals, derived from the record by
`CD-J8` and `CD-J9` rather than supplied. It was chosen because it is the one
quantity in the line that already prices a disposition, already has a
non-supplied derivation, and already carries necessity witnesses.

Nothing else enters it. Not incoherence, not movement, not reserve use, not the
core coefficient. A first test that scalarized those would be measuring an
exchange rate nobody has derived.

## 2. Per-occasion loss

For an occasion with bound schedule `(τ_def, τ_ref, w)` and response `b`:

```
ℓ(occasion, b) = 0                        b = merits(v)
               = τ_def                    b = default
               = (w − tolled(b))⁺ · τ_ref b = decline
               = 0                        b strikes the occasion's own obligation
```

The last line is not a licensed response. It is there because burden laundering
has to be **profitable** for the check that refuses it to be a check;
`E8` asserts both the saving and the refusal.

`w` is the declared service window, and it is what makes the loss bounded:
`ℓ ≤ max(τ_def, w·τ_ref) =: ℓ_max`, uniformly over occasions of that schedule.
The accrual rule is `CD-J8` with the horizon set to admission plus the window.
Without a window, refusal accrues to the run's horizon and per-occasion loss
grows with `T`, which no online-learning bound tolerates. **This is an assumption
about the environment, not a fact about the theory**, and it is the assumption
`PHI_REGRET_TEST_SPEC.md` §1 declares.

In the suite `τ_def = 1`, `τ_ref = 1/2`, `w = 4`; so a decline costs 2, a default
1, a merits ruling nothing, and `ℓ_max = 2`.

## 3. Cumulative loss and regret

```
L_T(H)   = Σ_t ℓ(occasion_t, a_t)
L_T(H^φ) = Σ_t ℓ(occasion_t, φ_t)
R_T(φ)   = L_T(H) − L_T(H^φ)
```

**Positive regret means the learner paid more than the lawful comparator would
have.** A comparator worse than the learner has negative regret; `E9`, `E10`,
`E10b` and `E10c` all report negative numbers, and that is what they should
report — they are locality witnesses, not advantage witnesses. A test asserts the
convention on a case where the comparator is known to be better.

Normalized regret is `sup_{φ ∈ Φ_law} R_T(φ) / T` over occasions. `E4` holds it
at `2/3` across horizons 12, 24 and 48; `E5` sends it to `8/T`.

## 4. Positive-rate outperformance

`φ` outperforms at positive rate when `liminf_T R_T(φ)/T > 0`. In the suite this
is exhibited rather than proved: `E4` has `R_T(φ)/T = 2/3` exactly at three
horizons, because the recognised occasions are a fixed fraction of the stream and
the saving per firing is uniform. A rate statement about an infinite family is
not something a finite suite establishes, and `THEOREM_LEDGER.md` records it as
an executable finite witness.

## 5. Resources stay out of the loss

Declared service work is accounted in its own units and never converted to
charge. A comparator whose replay overruns the per-date work is **not
affordable**, and:

- it is excluded from the supremum;
- its charge advantage is still computed and reported.

`E13`: three occasions on one date, per-date work 2, a merits ruling costing 1.
The comparator that rules on all three has regret 6 and is not affordable. The
one that rules on two has regret 4 and is. `sup R_T` over the affordable
comparators is 4, and the test asserts that the larger number does not enter it.

Reporting the unaffordable comparator's advantage rather than suppressing it is
deliberate: it is the quantity a reader needs in order to see what the resource
constraint cost, and hiding it would make the constraint look free.

**Solvency is not in the loss either.** Exhausting a reserve withdraws service,
which changes later dispositions, which changes later charges. The effect on
charge is therefore real and is measured; the reserve itself is never added to or
subtracted from the loss, and no exchange rate between a reserve and a tariff is
invented anywhere in this round.

## 6. Boundedness, for the next round

What an online-learning bound will want, and where it is:

| requirement | status here |
|---|---|
| per-occasion loss in a bounded range | `[0, ℓ_max]`, `ℓ_max = max(τ_def, w·τ_ref)` |
| losses exogenous given the response | true in v1 — intervals and arrivals are frozen |
| comparator loss computable from the actual history | true in v1 — guards on the actual prefix |
| finite comparator class | declared as a list, not generated |
| one edit's influence bounded independent of `T` | **conditional** — see `COUNTERFACTUAL_CHARGE_INFLUENCE.md` |

The last row is the one that is not free, and it is the round's main finding.

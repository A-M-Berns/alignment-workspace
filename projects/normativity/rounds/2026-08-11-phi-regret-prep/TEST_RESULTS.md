# Test results

`python3 tests/run.py` from this folder. 25 tests, all passing. Exact rationals;
nothing sampled. The tables below are the runner's own output, not a
transcription.

## The experiment table

| experiment | comparator | fired | first obstruction | actual | replay | regret | affordable |
|---|---|---|---|---|---|---|---|
| E1 | `phi:e1` | 0 | `certificate.replacement_unsupported` | 8 | 8 | 0 | yes |
| E2 | `phi:e2-later` | 0 | `certificate.not_historically_available` | 8 | 8 | 0 | yes |
| E2 | `phi:e2-endorsed` | 0 | `certificate.successor_ratification` | 8 | 8 | 0 | yes |
| E3 | `phi:e3` | 1 | — | 8 | 6 | 2 | yes |
| E4 | `phi:e4` | 8 | — | 48 | 32 | 16 | yes |
| E5 | `phi:e5` | 4 | — | 48 | 40 | 8 | yes |
| E6 | `phi:e6-within` | 1 | — | 6 | 5 | 1 | yes |
| E6 | `phi:e6-beyond` | 0 | `certificate.magnitude_unresolved` | 6 | 6 | 0 | yes |
| E7 | `phi:e7` | 1 | `certificate.defeated_ground` | 4 | 3 | 1 | yes |
| E8 | `phi:e8-erase` | 0 | `burden.dropped` | 6 | 6 | 0 | yes |
| E8 | `phi:e8-annex` | 0 | `burden.foreign_closure` | 6 | 6 | 0 | yes |
| E9 | `phi:withdraw` | 1 | — | 0 | 2 | −2 | yes |
| E10 | `phi:withdraw` | 1 | — | 0 | 24 | −24 | yes |
| E10b | `phi:withdraw` | 1 | — | 0 | 24 | −24 | yes |
| E10c | `phi:withdraw` | 1 | — | 0 | 2 | −2 | yes |
| E11 | `phi:e11-actual` | 3 | — | 6 | 0 | 6 | yes |
| E11 | `phi:e11-replay` | 2 | — | 6 | 2 | 4 | yes |
| E12 | `phi:e12` | 1 | — | 8 | 6 | 2 | yes |
| E13 | `phi:e13-all` | 3 | — | 6 | 0 | 6 | **no** |
| E13 | `phi:e13-two` | 2 | — | 6 | 2 | 4 | yes |

Negative regret is a comparator that did worse; E9 through E10c are locality
witnesses and are supposed to show it. "Affordable" is resource feasibility and
is not membership in Φ_law: a rule that never fires is trivially affordable, and
`E13`'s unaffordable rule is fully licensed at every occasion it fired at.

## The locality table

| configuration | horizon | divergence | fenced bound | bound holds |
|---|---|---|---|---|
| E9 fenced, edited account alone | 12 | 2 | 2 | yes |
| E9 fenced, edited account alone | 24 | 2 | 2 | yes |
| E10b fenced, one account for the run | 12 | 24 | 24 | yes |
| E10b fenced, one account for the run | 24 | 48 | 48 | yes |
| E10c fenced, no solvency coupling | 12 | 2 | 2 | yes |
| E10c fenced, no solvency coupling | 24 | 2 | 2 | yes |
| E10 pooled | 12 | 24 | — | not applicable |
| E10 pooled | 24 | 48 | — | not applicable |

## Numbers not in the tables

Asserted by the suite and worth having in one place.

- `E4` normalized regret is `2/3` at horizons 12, 24 and 48. The pattern is
  recognised on every third occasion, fires at every one of them, and saves 2
  each: `uniform_saving = 2`, `rate = 1`, `total_saving = 16` at `T = 24`.
- `E5` regret is 8 at horizons 12, 24 and 48; normalized regret at `T = 48` is
  `8/48`.
- `E12` under endogenous filings: actual 8, replay 0, regret 8, against 2 under
  the freeze. The actual charge is the same either way, so the whole difference
  is in what the freeze charges the comparator for.
- `E8` laundering saving, computed directly: an honest decline at `o:1` charges
  2, the same decline with the obligation struck charges 0.
- `E13` `sup R_T` over affordable comparators is 4, not 6.

## What the suite checks that the tables do not show

**Substrate.** Every fixture is well formed. Identity replay reproduces the
recorded responses of every fixture. Replaying any comparator twice gives
identical outcome tuples and totals. The sign convention holds on a case where
the comparator is known to be better.

**The footprint, twice.** The charge table is absent from the certifier's
declaration, and asking a certifier's reader for it raises. A comparator whose
guard reaches for the charge table makes the whole replay raise rather than
returning a run — the case is a guard written to do exactly that.

**Magnitude is unresolved, not rejected.** A direct certificate check on the
four-date tolling proposal returns `unresolved`; the test asserts the status
rather than the absence of a firing, because a rejection would have looked the
same from outside.

## What passing this suite is evidence for

The displayed finite instances, and nothing else. No general theorem is supported
by the runner; `THEOREM_LEDGER.md` says which claims have a derivation and which
have only a witness. The two general statements this round makes — the fenced
accounting lemma and its sharpness — are derived in
`COUNTERFACTUAL_CHARGE_INFLUENCE.md` and exercised here, in that order.

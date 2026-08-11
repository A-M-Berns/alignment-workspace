# Replay semantics

Given an actual run `H` and a comparator `φ`, what `H^φ` is. `src/replay.py`.

The actual run is produced by the same function, with the identity comparator.
That is not a convenience: it is what makes `L_T(H)` and `L_T(H^φ)` the same
function of the same objects, so their difference means something. A test asserts
that replaying the identity reproduces the recorded responses of every fixture,
and a history for which it fails is malformed rather than interesting.

## The field table

| field or event | frozen from the actual history | recomputed | ignored in v1 | why |
|---|---|---|---|---|
| occasion arrival, date, target, account | ✓ | | | exogenous; identity preservation needs it |
| the bound schedule — threshold, verdict labels, tariffs, service window | ✓ | | | procedure is prospective and frozen at arrival (`CD-J4`) |
| credal intervals | ✓ | | | a comparator may not edit the book, so the interval is not downstream of the edit |
| impediment, ripeness, authority records, and their defeat dates | ✓ | | | the reason state is what the edit answers to, not what it produces |
| ratification records | ✓ | | | present so that citing one can be refused |
| inherited obligations | ✓ | | | the burden an edit may not launder |
| occasions arising from a contingent filing | ✓ (default) | optional | | the freeze, and its cost, are both measured — `E12` |
| the response at a fired occasion | | ✓ | | this is the edit |
| the response at an unfired occasion | ✓ | | | carried unchanged |
| the ledger effect of a response | | ✓ | | derived from the basis |
| per-occasion charge | | ✓ | | derived from the response and the frozen schedule |
| per-account balance | | ✓ | | the sum of its occasions' charges |
| account suspension date | | ✓ | | the coupling; this is where locality is decided |
| declared service work used per date | | ✓ | | feasibility, kept apart from charge |
| whether the guard fires | ✓ (evaluated on the actual prefix) | | | see below |
| the learner's algorithm | | | ✓ | v1 replays a transcript, not an agent |
| anything the diachronic-identity layer treats — migration, ontology, language | | | ✓ | out of scope, and untouched |

There is no field of the substrate whose treatment is left implicit; the table is
exhaustive over `src/model.py`'s record types.

## Guards on the actual prefix

Whether `φ` fires at occasion `t` is decided from the actual prefix and the
actual response at `t`. Not from the counterfactual prefix.

This is what makes the comparator's loss computable from the realised history
alone. `E11` displays the difference on one three-occasion history: a rule that
fires at the first occasion and afterwards wherever the prefix still shows a
decline fires at all three occasions on the actual prefix and at the first and
third on the replayed one — the first edit removes the decline the guard reads at
the second occasion, and the unedited second occasion restores it by the third.
Regret 6 against 4, from the same rule.

## Local endogenous recomputation

Recomputed: the response at a fired occasion, its ledger effect, its charge, the
balance of the account it lands in, that account's suspension date, and the
service work used at its date. Not recomputed: anything belonging to another
account under a declared fence, and nothing at all about arrivals.

**Suspension is where this stops being trivial.** An account whose reserve is
exhausted has merits service withdrawn, so its later occasions are forced to
decline. One local edit can therefore change the disposition of occasions it
never touched — within its own account under a fence, and everywhere under
pooling. `COUNTERFACTUAL_CHARGE_INFLUENCE.md` is about exactly that.

## No counterfactual authority laundering

The replay generates no reason records. The only objects it creates are
responses, charges and balances, none of which is citable by a certificate: the
certifier's footprint contains reasons and not charges, and the reason table is
frozen. So an edit cannot manufacture the ground that licenses it, and the
failure has no representation rather than being refused by a rule.

## Identity preservation

A replayed occasion keeps its identifier, date, target, account and bound
schedule. Charges pair occasion by occasion, and `src/regret.py` uses that
pairing to report which occasions moved — `E3` asserts that exactly one did.

Under endogenous filings the pairing is no longer automatic, because an occasion
may exist in one run and not the other. `E12` is computed by total rather than by
pairing for that reason, and that is a second cost of lifting the freeze, beyond
the one the number shows.

## Determinism

One forward pass over dates; every branch is a function of frozen data and the
responses already decided. A test replays each comparator of each experiment
twice and compares outcome tuples and totals.

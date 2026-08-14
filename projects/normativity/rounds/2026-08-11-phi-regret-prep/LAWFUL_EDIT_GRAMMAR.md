# The v1 comparator class

## The shape

A comparator is a guarded local edit rule:

```
φ(h_t, occasion, a_t) = b_t   if guard(h_t, occasion, a_t) and check(...) admits
                        a_t   otherwise
```

Membership in Φ_law is decided **per firing**, not per rule. A rule whose guard
fires where no certificate exists simply leaves the response alone at that
occasion; it is not thereby excluded from the class. This is why `E7` is a single
comparator that is admitted at one date and refused at another rather than two
comparators.

## What the pieces may do

| question | v1 answer |
|---|---|
| what may a guard read? | `GUARD_FOOTPRINT` — occasions, responses, reasons, obligations. Not charges. |
| which prefix is the guard evaluated on? | the **actual** prefix, plus the actual response at the occasion |
| what may a replacement change? | `basis`, `verdict`, `tolled`, and the ledger effect the basis derives |
| is occurrence identity preserved? | yes — the replayed occasion keeps its identifier, date, target and account, so losses pair occasion by occasion |
| may a comparator fire more than once? | yes; `once=True` restricts a rule to its first firing |
| how do overlapping rules compose? | they do not — each comparator is evaluated against the actual history separately, and Φ_law is a set of rules, not a lattice |
| what if two edits conflict? | unrepresentable in v1: one rule edits one occasion at a time and rules are never composed |
| what granularity? | **local response**: one occasion's disposition. Not schema-local, not case-local. |

The response set is three bases with two dependent coordinates:
`merits(verdict)`, `default`, `decline(tolled)`. Every comparator in the suite is
a map within that set.

## What v1 excludes, and why

These are methodological scaffolding for a first theorem, not claims about the
final theory. Each is listed with what would have to change to lift it.

**Guards on the replayed prefix.** Excluded because comparator loss must be a
function of the actual history for the comparison to be well defined without
simulating the learner. `E11` shows the conventions differ: the same cascade rule
fires three times on the actual prefix and twice on the replayed one, for regrets
of 6 and 4. *To lift:* the object stops being Φ-regret and becomes policy regret;
see `ONLINE_LEARNING_MAP.md` §6.

**Endogenous filings.** Occasions that an earlier disposition caused to arrive
are frozen to what the actual run produced. `E12` measures the cost exactly: the
comparator's advantage is 2 under the freeze and 8 without it, because in the
actual history the decline it repairs generated three further occasions and the
freeze keeps charging for them in both runs. *To lift:* the counterfactual
occasion set becomes a fixpoint, and identity-preserving pairing of occasions
across the two runs stops being automatic.

**Book edits.** A comparator may not change an endorsement, so the credal
interval at each date is exogenous. *To lift:* intervals must be recomputed under
the edited book, which means running the interval computer inside the replay, and
`CD-J2`'s strictness stops being a fact about frozen input.

**Ontology creation, language migration, retroactive rewriting.** Excluded
outright. The diachronic-identity layer already treats these and nothing here
touches it.

**Capacity and funding changes.** A comparator may not alter declared service
work or reserves. It may propose responses the declared work cannot afford, and
that is a separate verdict — see `PHI_REGRET_OBJECTIVE.md` §5.

**Comparators whose applicability depends on their own consequences.** Excluded
structurally: the guard footprint has no charge table, so a rule cannot condition
on what it would save. The test suite exercises a guard written to try.

## Witnesses

The four separations the class has to make, each with an executable instance.

### profitable ⇏ lawful — `E1`

Four declined occasions, charge 8. The interval at `o:1` is `[2/5, 3/5]` and the
threshold is `1/2`, so it separates in no direction and no merits ruling is
available. The comparator proposes one anyway; ruling would save 2. Refused as
`certificate.replacement_unsupported`, regret 0.

### successor-endorsed ⇏ lawful — `E2`

Two rules on the same occasion. One cites an interval filed at date 3 for an edit
at date 1: refused as `certificate.not_historically_available`, because the
reader at date 1 cannot see it. One cites an endorsement of the disposition that
is already on the record at date 0: refused as
`certificate.successor_ratification`, because an endorsement is not a ground.

### reason exists ⇏ arbitrary edit lawful — `E6`, `E8`

`E6`: an impediment declaring two dates is on the record. Tolling two dates is
admitted and saves 1. Tolling four is directionally supported by the same ground
and left `unresolved`. `E8`: a ripeness ground licensing a withdrawal does not
license striking the obligation, and an interval licensing a merits ruling does
not license discharging an inherited obligation alongside it — `burden.dropped`
and `burden.foreign_closure`.

### a nontrivial edit that is certified lawful — `E3`, `E4`, `E6`, `E7`

`E3`: one certified repair, charge 8 → 6. `E4`: the same repair on every third
occasion of a horizon, 8 firings, regret 16. `E7`: the same tolling edit admitted
at date 3 and refused at date 9 because its ground stops being live at date 6.

## Enumerability

Φ_law for the test spec is a finite explicit list, not a generated set. A guard
is an arbitrary predicate over the declared footprint, so the class of *rules* is
not finite; the class of *comparators the next round evaluates* is whatever list
that round declares. `PHI_REGRET_TEST_SPEC.md` §1 fixes one.

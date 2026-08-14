# The reasons-responsiveness interface

The weakest interface that decides whether a proposed edit belongs to the
comparator class. It is not a theory of reasons and does not become one by being
used. What is substantively normative is a named parameter; what is mechanical is
checked.

## The signature

```
check : (prefix h_t, actual response a_t, replacement b_t, grounds, authority)
      -> admitted | rejected(code) | unresolved(code)
```

`src/certificates.py`. The prefix is not a value passed in but a `PrefixReader`
constructed at date `t` under a declared footprint. Three consequences follow
from that choice and are the reason for it.

**A ground filed after `t` is invisible, not merely inadmissible.** `reader.reason`
returns nothing for a record whose `filed_at` exceeds the prefix date. Historical
availability is therefore a property of the view rather than a rule a checker
could forget to apply, and the failure mode it prevents — importing a later fact
as though it had been there — has no representation in which to occur.

**The charge table is not in the declaration.** `CERTIFIER_FOOTPRINT` is
`("occasions", "responses", "reasons", "obligations")`. Asking the reader for
`"charges"` raises. A check that consulted what an edit saves would fail loudly.

**Every read is logged before its value is returned.** This is the enforcement
discipline of `GR-J1` reused for a different purpose: there it keeps a judge
inside its declared footprint, here it keeps legitimacy out of reach of
profitability.

## The certificate

```python
LawfulEditCertificate(edit_id, occasion_id, at_date, replaced, replacement,
                      grounds, authority)
```

There is no field for saving, advantage, or cost, and adding one would not help.

## The nine checks

Ordered by which obstruction a reader is told about first. Each is independent.

### A — historical availability · mechanical

Every cited ground is on the record at `at_date`. Enforced by the reader, as
above. Code `certificate.not_historically_available`.

### B — reason connection · **parametric**, `BearsOn(reason, coordinate, occasion)`

For each substantive coordinate the edit moves, some cited ground bears on that
coordinate of that occasion. The supplied default is deliberately weak: the
ground declares the coordinate in its `licenses` and names either the occasion or
its target. A stronger relation is a normative commitment and belongs to whoever
will make it. Code `certificate.no_reason_connection`.

### C — defeater discipline · mechanical

No cited ground carries a `defeated_at` or `suspended_at` at or before
`at_date`. Code `certificate.defeated_ground`.

### D — scope discipline · mechanical, given the declaration

The coordinates the edit moves are contained in the union of what its cited
grounds declare they license. `verdict` moves with `basis` and carries no licence
of its own; a verdict changed at a fixed basis is substantive and is checked as
one; `ledger` is derived and is checked separately under F. Code
`edit.out_of_scope`.

### E — magnitude · **parametric**, `MagnitudeOK(grounds, old, new)`

The one magnitude coordinate of this substrate is `tolled`, the number of dates a
response claims are excluded from the refusal clock (`CD-J9`). A recorded
impediment supports tolling in the direction of *some* exclusion without thereby
supporting a particular amount.

The supplied default admits an increase up to the summed declared allowance of
the cited impediments and returns **`unresolved`** beyond it — not `rejected`.
The distinction is the whole point of exposing the predicate: whether directional
support ever licenses an unbacked endpoint is the question the parameter stands
in for, and a round that answered it by rejecting would have answered it. Code
`certificate.magnitude_unresolved`.

### F — burden and history preservation · mechanical

An edit may close its own occasion's decision obligation, under the closure kind
its basis derives and no other, and may do nothing else to the record. Three
codes, because three failures are different: `burden.dropped` (an obligation
struck out), `burden.foreign_closure` (someone else's obligation discharged),
`burden.retargeted` (an inherited obligation renamed onto another carrier).

The charge rule is built so that laundering pays: an occasion whose own decision
obligation has been struck shows nothing owed and accrues nothing. A substrate in
which erasure were free of consequence would make this check untestable, and the
test asserts the saving the check refuses.

### G — no successor ratification · mechanical

A ground of kind `ratification` is not a ground, whenever it was filed.
Availability already refuses the ordinary case, in which the endorsement comes
later; this refuses the residue, in which an endorsement is already on the record
at `t`. Code `certificate.successor_ratification`.

Stating it separately is the point. Availability alone would leave a reader able
to think that an endorsement contemporaneous with the edit licenses it.

### H — no cost laundering · structural

Not a check. The footprint.

### I — replacement support · **parametric**, `AddressOK(grounds, old, new, occasion)`

Where a replacement claims a merits ruling, some cited interval must separate the
bound threshold in the direction claimed (`CD-J2`). This is where reason
connection stops being generic and says something about this response family.
Code `certificate.replacement_unsupported`.

Two further parameters are declared and lightly used: `AuthorityOK(authority,
grounds, occasion)`, which requires a named authorization and, where an authority
ground is cited, that it cover the occasion; and
`ReasonCompatible(grounds)`, which refuses grounds declared incompatible with
each other.

## What is mechanical and what is supplied

| check | mechanically decided | supplied policy relation |
|---|---|---|
| A availability | yes | — |
| B reason connection | the `licenses` declaration | `BearsOn` |
| C defeaters | yes | — |
| D scope | yes, given `licenses` | — |
| E magnitude | no | `MagnitudeOK` |
| F burden | yes | — |
| G ratification | yes | — |
| H cost | structural, by footprint | — |
| I replacement support | the threshold comparison | `AddressOK` |

Five checks are mechanical, three rest on a supplied relation, one is a
declaration about the reader. `PolicySuite` gathers the parameters in one place
so that a later round's normative commitment appears as a diff to a named
function rather than as a changed sentence in a document.

## What this interface does not decide

Whether the `licenses` declaration attached to a record is the right one. Whether
the record kinds — interval, impediment, ripeness, authority, ratification — are
the right ones or are complete; this is the same shape as the consolidation's
open registry-completeness problem, and inherits its standing. Whether a
substantively adequate `BearsOn` exists. Whether `unresolved` is the right verdict
for an unbacked endpoint or merely the honest one.

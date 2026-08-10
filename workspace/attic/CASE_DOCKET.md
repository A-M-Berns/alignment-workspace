# The case docket and adjudication protocol

## 0. What this layer is

The **answerability ledger** records what the learner owes an answer to.  The
**case docket** records the practical questions it must dispose of.  The
**adjudication protocol** decides whether the active credal book supports a
merits ruling, or only a scheduled default, or nothing at all — in which case the
learner declines and the obligation stays open at a cost.

Five things stay separate:

\[
\text{case demand}\neq\text{answer generation}\neq\text{merits certification}
\neq\text{practical ruling}\neq\text{operative force}.
\]

A ruling is not a belief settlement.  A default is not a normative belief.
Neither enters the settled empirical or logical record.  Nothing here generates
responses, models parties, or optimizes: **tariffs are accounted liabilities,
not incentives**, and no result below claims a tariff changes behavior.

## 1. Definitions

A **procedure schedule** is versioned, revisable, prospective procedural
content — not a constitution.  It carries a claim-type identifier, a target
rule, a rational threshold `tau` with `0 < tau < 1`, positive, negative, and
fallback verdict labels, a default tariff, a refusal tariff, and a basis.

A **query** is thin: `(query id, case id, claim-type id, bound schedule version,
target instance)`.  Filing a well-formed query creates an identified **decision
obligation** in the ledger.  Several queries may concern one case; the same facts
can support different questions with different thresholds and fallbacks.

The active book supplies an exact rational **credal interval**
`I(q) = [p_lower, p_upper]`.  For a threshold `tau`:

- positive merits is available iff `p_lower >= tau`;
- negative merits is available iff `p_upper < tau`;
- otherwise no merits verdict is certified.

A **ruling** records `(ruling id, query id, verdict, basis tag, certificate ids,
book version, bound schedule version)` with basis tag `merits` or `default`.  A
ruling is not a ledger `Discharge`: the ledger event closes an obligation, the
ruling issues a practical verdict, and each needs its own record.

**Decline** is the absence of a ruling.  The decision obligation stays open and
accrues the scheduled refusal liability over explicitly represented steps.

## 2. The four results

**Empty-substantive-book accounting.** {#CD-J1}
**Status: PROVED (single derivation).** With a nonempty schedule, `0 < tau < 1`,
and a genuinely unsettled query `I(q) = [0,1]`, neither `0 >= tau` nor `1 < tau`
holds, so no merits verdict is available.  Exactly two accountable options
remain: a **scheduled default**, which closes the decision obligation
procedurally and adds the default tariff, or **decline**, which leaves it open
and adds the refusal tariff per represented step.

**Proof.** Immediate from the two inequalities and `0 < tau < 1`.  That the two
options are exhaustive is the disjunction "a ruling is recorded or it is not",
and a recorded ruling on an empty book cannot be tagged `merits` by `CD-J2`. `square`

Emptiness does **not** become a substantive normative position.  It becomes an
accounted liability, which is a different thing.

**Unsupported-merits rejection.** {#CD-J2}
**Status: PROVED (single derivation).** A ruling tagged `merits` is accepted only
if it cites a certificate that exists, names this query and this target, cites
the book version and interval actually supplied, cites the threshold of the
schedule bound to this query, recomputes to the same direction, and carries the
verdict label that direction implies.  Every mutation of these is rejected with a
structured obstruction.

**Proof.** Each conjunct is checked directly against the supplied records, and
the direction is recomputed from the interval rather than read from the
certificate. `square`

**Default non-laundering.** {#CD-J3}
**Status: PROVED (single derivation).** A default ruling creates no coverage
edge, alters no interval, and enters no settled record.  A later query citing a
prior default as substantive support is rejected: the recomputation step of
`CD-J2` has no interval to appeal to, and `default_is_not_evidence` rejects a
certificate whose identifier names a default ruling.

Historical consistency or precedent might later cite a ruling as a prior
institutional disposition.  That is a different reason type and is out of scope.

**Prospective procedure.** {#CD-J4}
**Status: PROVED (single derivation).** A query is governed by the schedule
version bound when it arrived.  Changing threshold, fallback, or tariffs
afterwards does not touch it unless a **retrospective amendment** names the
query, names the old and new versions, carries authorization, and records the
consequence.  An unauthorized change is rejected even when the new schedule would
make a desired merits ruling available.

## 3. The adjudication transaction

An **adjudication transaction** binds one attempted disposition to everything
that authorizes it: the query, the frozen schedule, the decision-obligation
identifier, the basis, the refusal clock, and — where they exist — the ruling,
the merits certificate, the credal interval, the named ledger event identifiers,
the boundary record, and the liability entries.

It is not a convenient bundle.  `verify_transaction` establishes each identity
and each relation: claim type against schedule, bound schedule version against
both the schedule and the ruling, target rule against the query, obligation
identifier against the query, every named ledger event's existence and ownership,
the certificate's query, target, threshold, book version, and interval, the
recomputed threshold direction, the verdict label implied by that direction, the
ledger closure kind implied by the basis, the boundary outcome implied by the
basis, and the liability entries implied by the schedule and the clock.

**Transaction completeness.** {#CD-J5}
**Status: PROVED (single derivation).** This is a **verifier-safety** result, not
a representation theorem about all possible adjudications.  An accepted
transaction exhibits exactly one live query, the unique decision obligation
`d:<query id>` for it, and — when a ruling exists — a ruling for that same query
under the schedule version the query is bound to.  Every named ledger record is
checked to exist and to concern that obligation.

**Basis coherence.** {#CD-J6}
**Status: PROVED (single derivation).** For an accepted transaction the ruling
basis, the supporting certificate or frozen fallback, the ledger closure kind,
the boundary outcome, and the liability treatment agree:

| basis | closure kind | boundary outcome | liability | certificate |
|---|---|---|---|---|
| merits | `discharge` | `discharge` | none | required, recomputed |
| default | `procedural` | `procedural` | default tariff | forbidden |
| decline | none; still open | none | refusal per elapsed step | forbidden |

Every cross-basis pairing is rejected locally: merits with a procedural closure,
merits with a substantive withdrawal, default with a merits discharge, default
citing a certificate, and a default verdict other than the frozen fallback.

**Boundary faithfulness.** {#CD-J7}
**Status: PROVED (single derivation).** Every named boundary subrecord must
exist, concern the same obligation, occur at the declared version, have the
claimed type, and justify the declared outcome; `continue-suspended` must end
suspended, a discharge boundary must name a discharge whose coverage edge was
accepted, a terminal boundary must name a substantive withdrawal or loss, and a
procedural boundary must name a `ProceduralClosure`.  No record may be reused to
dispose of two obligations.

**Automatic refusal accounting.** {#CD-J8}
**Status: PROVED (single derivation) — an accounting identity.** At a declared
horizon an unresolved decision obligation carries exactly
`(horizon - filed) * refusal_tariff`, derived from the clock and the frozen
tariff.  An instantaneous snapshot has `horizon == filed` and therefore costs
nothing; a longitudinal evaluation is costly in proportion to elapsed open time.
A caller cannot omit an unruled query from the accounting, because the charge is
generated for every unruled query rather than supplied.

This is an accounting identity, not an incentive claim.

## 4. The procedural closure type

A scheduled default closes its obligation through `ProceduralClosure`, a type
distinct from `Dispose`.  `Dispose` now carries only the substantive kinds
`withdrawal` and `loss`.  A procedural closure says: this decision obligation was
disposed of by schedule; a practical verdict issued under the frozen fallback; no
substantive claim was endorsed, withdrawn, settled, or made true; no merits
coverage was created; and the underlying material remains challengeable.  The
ledger refuses a procedural closure on an obligation that has merits coverage.

**Intrinsic default non-laundering.** {#CD-J9}
**Status: PROVED (single derivation).** A default cannot enter the merits
channel.  `MeritsCertificate` is constructible only by `certify_merits` from an
actual credal interval; there is no field a ruling identifier could populate; and
`verify_transaction` recomputes the threshold direction from the interval the
book supplied rather than reading the certificate's claim.  A procedural closure
creates no coverage edge, so nothing in the ledger can be reused as evidence.
This replaces the earlier string-matching helper, which has been removed.

## 5. The three paths

| path | ledger | ruling | liability |
|---|---|---|---|
| **merits** | response filed, coverage edge from the credal certificate, discharge, boundary outcome `discharge` | `merits` with certificate | none |
| **default** | authorized procedural closure, boundary outcome `procedural`, **no coverage edge** | `default` with the bound fallback | default tariff |
| **decline** | obligation stays open | none | refusal tariff per step |

A default closes through a typed procedural disposition whose witness names the
default; the boundary outcome is `procedural`, so an audit can never read it as
merits.  It is not abused as withdrawal-for-cause or as loss.

A later undercutter may reopen a justificatory obligation without erasing the
historical ruling; the practical action the ruling caused is not undone.

## 6. Worked example: three queries, one set of facts

One case, one schedule (`tau = 3/4`, fallback `not-liable`, default tariff
`1/10`, refusal tariff `1/20`), one book version.  `q:1` has interval
`[4/5, 9/10]`; `q:2` and `q:3` are unsettled.

| transaction | basis | ruling | ledger closure | status | liability |
|---|---|---|---|---|---|
| `tx:1` (`q:1`) | merits | `liable`, cites `cert:q:1` | `discharge` with coverage | closed | `0` |
| `tx:2` (`q:2`) | default | `not-liable` (frozen fallback) | `procedural`, no coverage | closed | `1/10` |
| `tx:3` (`q:3`) | decline | none | none | **open** | `1/5` at horizon `4` |

Stream output: default total `1/10`, refusal total `1/5`, total `3/10`, open
decisions `("q:3",)`.  Every figure is recomputed from the schedule and the clock.

## 7. Machine-checked examples

**Adversarial suite.** {#CD-E1}
**Status: MACHINE-CHECKED (stated finite scope).** Empty book with default and
with two-step decline; positive, negative, and indeterminate intervals;
unsupported merits under eight mutations; a default reused as evidence; a
schedule changed prospectively and retroactively; two claim types on one case
yielding opposite verdicts from one interval; a ruling without a ledger
disposition; a ledger closed without a ruling; a migration retargeting the
obligation while the query identity and its bound schedule are untouched;
conflicting boundary dispositions; duplicate identifiers and out-of-order
versions.  All verdicts are computed from raw inputs.

## 8. Composition assumptions

`compose_segments` now reports four separate clauses and `accepted` is their
conjunction: the first segment is accepted; the seam is compatible; the second
segment's events are accepted on the state the first produced; and the composite
is accepted.  The third clause is exactly the composite fold restricted to the
second segment's events — that is the only sense in which the second segment is
"verified under the resulting state", and no more is claimed.

## 9. Status boundaries

`CD-J1`–`CD-J4` are **accounting and verifier-safety** results.  None is an
incentive claim and none is a learning claim.  In particular:

- no result depends on optimization; every quantity is an exact rational sum;
- tariffs are accounted, and nothing here shows they change what a learner does;
- the adequacy oracle is the credal interval, supplied as input; this layer does
  not rebuild the book, the market, or the leverage machinery;
- everything assumes a single actor and a linear history.

## 10. Canonical-key design note

**Proposed, not established.** {#CD-C1}
**Status: PROPOSED (interface revision).** A liability key should include exactly
the coordinates along which an admissible challenge or disposition can vary
independently.  Tentatively: schema endorsement and global schema objections are
keyed by schema identifier; application-specific premise and applicability
obligations are keyed by `(rho, query id, grounds binding)`; and the
applicability obligation is fresh per case when its truth or challengeability can
vary by case.  The schema-rate theorem this would support is **not** implemented
and is not claimed.

## 11. Next conjecture

> Under bounded answerability capacity and a live case-arrival process,
> persistent substantive silence cannot remain cost-free: it must appear as
> accumulating refusal liability, default load, or both.

This is **not** proved here.  Turning it into a theorem needs: a bounded capacity
hypothesis saying how many merits certifications the learner can produce per
step; an arrival process with a positive rate of well-formed queries; a solvency
or budget constraint making accumulated liability bite; and a link from the
liability stream to the existing bounded-force machinery, for which
`CaseStreamLiabilities` is the typed interface.  None of these exists yet, and
the current results are accounting and verifier-safety results that say nothing
about behavior.

## 12. Deliberately not implemented

Response generation, adversarial parties, several actors, general act spaces,
discretionary balancing, aggregate default-rate objections, liveness theory,
similarity or precedent, schema amortization, arrival asymptotics, utility
maximization, and any behavioral claim from tariffs.  The case docket supplies
demand; it does not explain how good responses are generated.

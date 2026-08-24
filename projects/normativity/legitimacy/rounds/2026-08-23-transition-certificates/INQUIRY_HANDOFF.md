# Left-consumer contract: inquiry and coverage over the frozen waist

Status: **handoff note; unregistered**. This specifies what an
inquiry/coverage layer may consume and produce against the frozen
reason-state interface. It does not develop inquiry theory.

The pipeline the waist must support, and does
(`test_handoff.TestLeftHandoff`):

```text
world → L → case/docket → investigation → new reason occurrences → pressure on B
```

Pressure on `B` is visible pressure: new bearing, new conflict, new basis
loss — read off the queries. It is never a stance edit performed by inquiry.

## Inquiry may inspect

Transcript receipts and arrivals; cases, docket items, and staged views;
the current stance (read-only); `Reasons`, `Conflict`, `LostBasis`,
`Dependents`, `Explain`, `ExistedBefore`; the record's due tokens, coverage
debts, and review liabilities.

## Inquiry may produce

New receipts appended to `L` with their procedural provenance `T`; new
reason occurrences minted into `𝓡` (interpretation is a minting act:
a receipt bears on an issue only through an occurrence that cites it);
docket and record events in `N` — investigations, reviews, accruals — under
the record's own machinery.

## Inquiry must not

Rewrite or delete occurrences; modify an occurrence's sources, target, or
schema-use provenance; store a "defeated", "stale", or any status on a
reason; adopt, withdraw, or revise stance members. The reference
implementation refuses the first two structurally (append-only ledger,
frozen occurrences, no status fields — tested); the last is an architectural
rule this note makes explicit.

## Docketable conditions are query-level

The conditions worth docketing — an uninterpreted receipt tied to a case, a
live conflict, a reliance whose basis is lost — are all readable from `T`
minus citing occurrences, `Conflict`/`joint_conflicts`, and `LostBasis`
respectively. None is a stored mark; the docket is record machinery fed by
queries.

## What stays open on the left

The genuinely open left-side program, none of it representational:

```text
exposure → interpretation → docketing → service → uptake
```

- which receipts a practice owes itself exposure to (coverage);
- which interpretations it owes minting (interpretation norms);
- when a query-level condition must become a docket item (docketing);
- scheduling and certified service (the afoundational round's territory);
- **uptake**: when the stance must register a minted defeater so that
  `LostBasis` sees it.

Recorded explicitly: **defeater-uptake completeness is not a
reason-representation problem.** Once uptake occurs, the waist represents
the defeater and every downstream detection works; what a practice owes by
way of uptake is inquiry/record theory above the frozen interface.

---
id: undescribed-failure
kind: cases
children: [undescribed-failure.partition, uf-disutility-max, uf-high-conflict, uf-no-interesting-life, uf-earth-gone-aliens-remain]
rows:
  - {picture: uf-disutility-max, class: disutility-max, observable: never}
  - {picture: uf-high-conflict, class: high-conflict, observable: never}
  - {picture: uf-no-interesting-life, class: no-interesting-life, observable: never, residual: true}
  - {picture: uf-earth-gone-aliens-remain, class: earth-gone-aliens-remain, observable: never}
provisional: true
author: "@smithy-verity"
size: S
size_reason: four rows, one per outcome class below utopia, and one ruling to read
version: 1
---
## Statement
A failure of a plan that no filed story describes lands in one of the named
outcome classes below utopia.

## Source
The maintainer's ruling of 2026-10-02, logged as the `rule` event
`maintainer-002` and to be recorded in `DECISIONS.md`: "Failure nobody
describes should be somewhat worse, excluding the 1.0 option, since it is
failure after all." The classes are the frame's.

## Notes
The valuation node for the residual row of every table (the row for a failure
nobody has yet described): each row is one outcome class below utopia, its
weight the probability that such a failure lands there. The node's value is the
weighted mean, -0.25 at the ruled equal weights, so an undescribed failure
reads a little worse than the default trajectory. A row of a table may name a
class of its own instead, through its `class` field or a `classify` judgment.
The residual row is the class-0 row only because the table format derives one
row's weight as the remainder. Provisional in the sense of the classes.

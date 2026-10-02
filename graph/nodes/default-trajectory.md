---
id: default-trajectory
kind: cases
children: [default-trajectory.partition, dt-disutility-max, dt-high-conflict, dt-no-interesting-life, dt-earth-gone-aliens-remain, dt-utopia]
rows:
  - {picture: dt-disutility-max, class: disutility-max, observable: never}
  - {picture: dt-high-conflict, class: high-conflict, observable: never}
  - {picture: dt-no-interesting-life, class: no-interesting-life, observable: never, residual: true}
  - {picture: dt-earth-gone-aliens-remain, class: earth-gone-aliens-remain, observable: never}
  - {picture: dt-utopia, class: utopia, observable: never}
provisional: true
author: "@smithy-verity"
size: S
size_reason: five rows, one per outcome class, and one ruling to read
version: 1
---
## Statement
Default-trajectory AI development, with no additional safety work beyond what
the developing organizations do on their own, lands in one of the named
outcome classes of the frame.

## Source
The maintainer's ruling of 2026-10-02, logged as the `rule` event
`maintainer-001` and to be recorded in `DECISIONS.md`: "please calculate the
default-trajectory utility by putting a case node with equal probability on
each of the current named utility levels." The classes are the frame's, which
the same maintainer placed as provisional.

## Notes
The valuation node for the outside option (committing to no plan): each row is
one outcome class, its weight the probability that the default trajectory
lands there, its conditional the probability that the row's class is where it
lands given the picture. The node's value is the weighted mean of the classes'
utilities, 0 at the ruled equal weights. The weights are judgments like any
row's: a contributor who holds that the default trajectory is more likely to
end in one class than another argues that row's weight, and every plan's
comparison moves with it. The residual row is the class-0 row only because the
table format derives one row's weight as the remainder; it carries no other
meaning here. Provisional in the sense of the classes themselves.

---
id: item-q3
kind: leaf
leaf_kind: question
item: "Q3"
title: "How is foreclosure expressible?"
section: "Where ingenuity is the bottleneck"
maintainer_order: 3
project: deference
dispatchable: false
item_status: open
work:
  - {kind: decision, ref: 2026-08-24--queue-triaged-rulings-rounds-recommended}
  - {kind: decision, ref: 2026-09-01--progress-claim-weighted}
  - {kind: decision, ref: open--whether-q3-graduates-what-succeeds-item}
author: "@smithy-verity"
size: L
size_reason: "one item entry of 442 words"
version: 1
---
## Statement
How is foreclosure expressible? (An entry of the ingenuity section: the program knows what it wants here and not what kind of statement would supply it.)

## Source
PRIORITIES.md, item Q3 (How is foreclosure expressible?).

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
The residue of the skeleton's `FU[g]` hole after items 27 and 28 took the rest.
Two holes: no operation reassigns the authorization relation at a later index,
which is what the movement's own statement is about; and the interface is one
decision index deep, so **foreclosure — an advisor removing the principal's
*later* ability to correct — is not expressible at all**, which is arguably the
failure mode corrigibility most needs to rule out.

**Three candidates, and what each one killed.**

*Cartesian frames* represent the future principal's corrective situation as a
frame and separate two ways of losing it — restriction as `Commit` with proper
additive subagency, transfer as `External^{/}` with a multiplicative one — by
whether the reachable worlds shrink. That is an object for **what is lost**. It
supplies no operation at a later index and no authorization relation, a frame has
no time coordinate, and the round's own red team found the transfer arm cannot say
anything holds the transferred coordinate.
`projects/deference/notes/CARTESIAN_FRAMES_DEFERENCE_BRIDGE.md`.

*Sealed deliberations* — the source corpus's family indexed by the day the
advisor's channel is cut, measuring influence as the gap at a fixed horizon
between the advised run and the sealed one on a shared past. The time coordinate
is real rather than stipulated, and irreversibility has the right shape: influence
admitted before the cut sits inside the baseline and no later measurement sees it.
It carries no authorization relation at all, and measures where deliberation
*lands* rather than where the principal can still *reach*.
`projects/deference/note-dump-2026-08-11/notes/legitimacy-theory-v1.md` §§2.1, 7.1,
adjudicated at
`projects/deference/rounds/2026-08-12-corpus-reconciliation/RECONCILIATION.md` §3.

*A multi-source transition system* — twelve states, reachability as the closure of
a step relation — expresses foreclosure without a field named for authority, and
**repairs the depth hole at the representation level**. Its protection claims were
then refuted in its own Lean: there is no protected coordinate, both capability
predicates quantify the advisor existentially, and an isomorphic system with the
gating field renamed `authorized` passes every test the round ran to show its
field was not a label. Registered as `corrective.*` in
`projects/deference/CLAIMS.md`; item 60 carries the result.

**What a good answer must carry**, which is more than any candidate said alone:
temporal depth and explicit authorization or capability structure at once, plus
the two requirements the third candidate machine-checked as unmet — the principal
must have at least one effect no advisor action can produce, and reachable
corrective capability must quantify the advisor's future actions *universally*.
No combined object has been built and nothing establishes that none exists.
Whether the pair is enough for this entry to graduate is in `DECISIONS.md`'s
queue, which is the live statement of what that turns on.

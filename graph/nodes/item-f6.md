---
id: item-f6
kind: leaf
leaf_kind: task
action: "Execute item F6 once the maintainers have specified it: The name lint cannot see a citation — *closed*."
who: either
item: "F6"
title: "The name lint cannot see a citation — *closed*"
section: "Workspace friction"
maintainer_order: 127
project: none
dispatchable: false
item_status: closed
work:
  - {kind: decision, ref: 2026-08-25--citation-may-written-backticks-where-name}
  - {kind: decision, ref: 2026-09-07--bibliography-exempt-name-lint}
  - {kind: decision, ref: 2026-09-29--people-named-role-name-lint-retired}
author: "@smithy-verity"
size: M
size_reason: "one item entry of 277 words"
version: 1
---
## Statement
Item F6, The name lint cannot see a citation — *closed*, is answered as its entry specifies.

## Source
PRIORITIES.md, item F6 (The name lint cannot see a citation — *closed*).

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
<!--historical-->`tests/name_lint.py`<!--/historical--> matches maintainer surnames anywhere in tracked prose
outside `prompts/`, the consolidated trees and `DECISIONS.md`. It cannot
distinguish naming the program after a person — the failure it exists to prevent
— from citing a third party's published work in a bibliography. A maintainer of
this repository is also an external author whose work the normativity line needs
to cite, so the collision is not hypothetical and will recur every time that work
is referenced.

`projects/normativity/notes/PRIOR_ART.md` ships with the surname in backticks,
which the gate allows and which reads as a citation key. That is a workaround and
is recorded as one: it costs a reader nothing here and would cost more in a
denser bibliography.

The fix is a matching rule that exempts a citation context — a bibliography
bullet, or a name adjacent to a title in quotes and a link. It changes a gate's
logic, which is specification layer and retroactive over every document the gate
has already passed, so it was not taken by the round that hit it.

*2026-09-07, partial fix by maintainer direction:* `wiki/Sources.md`, the bibliography,
is exempt from the lint as a single allowed file (`ALLOWED_FILES`), pinned in the
lint's self-test. Citations elsewhere in tracked prose still need the backtick form;
the citation-context matching rule above remains the general fix and is not taken.

*2026-09-29, closed by maintainer ruling (`DECISIONS.md`, 2026-09-29):* the lint is
retired and the rule it approximated is stated in `AGENTS.md` — people are named by
role, and an author is cited by name.  Kept for the lesson: a lint on surnames cannot
express a distinction that is about the capacity in which a person is named.

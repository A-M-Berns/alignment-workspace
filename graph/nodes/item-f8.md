---
id: item-f8
kind: leaf
leaf_kind: task
action: "Execute item F8 once the maintainers have specified it: A stack of merged pull requests never reached `main` — *closed*."
who: either
item: "F8"
title: "A stack of merged pull requests never reached `main` — *closed*"
section: "Workspace friction"
maintainer_order: 129
project: none
dispatchable: false
item_status: closed
author: "@smithy-verity"
size: L
size_reason: "one item entry of 387 words"
version: 1
---
## Statement
Item F8, A stack of merged pull requests never reached `main` — *closed*, is answered as its entry specifies.

## Source
PRIORITIES.md, item F8 (A stack of merged pull requests never reached `main` — *closed*).

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
Three research rounds developing the diachronic-answerability mathematics —
*answerability carriers*, *anchored slices and authenticated semantic Transfer*, and
*faithful semantic preservation*, together with the CF-coverage and proper-exercise
rounds beside them — **are not on `main`.** Their pull requests are marked MERGED on
the forge, and they were: into *each other*. The stack was based on
`round/2026-08-30-liability-theory` and then on
`round/2026-08-30-answerability-carriers`, and no pull request from the top of that
stack to `main` was ever opened. The trees exist on those branches and in working
copies; the repository's history on `main` does not contain them.

**How it was found.** The September consolidation cited two of the rounds by path;
`tests/dead_pointers.py` failed in CI and passed locally, because the local checkout
had the directories as untracked files left by another session. The gate did exactly
its job, and the local pass was the misleading signal.

**Why it matters beyond the citations.** Those rounds' exact fixtures do not run in
this repository's CI, so results attributed to them are paper-derived only from
`main`'s point of view. The consolidation now cites the underlying note by section
and theorem number instead, and its `STATUS_LEDGER.md` marks the affected rows.

**Resolved on 2026-09-01.** The maintainer asked for the fix, and the stack was
landed: current `main` was merged into `round/2026-08-30-liability-theory` on a new
branch and opened as one pull request. Three files conflicted and all three were
additive on both sides — `state/rounds.json` resolved as the union of the two record
sets, `PROVENANCE.md` keeping both sides' rows, and the generated views regenerated.
No round document was edited. The repository's runner count went from thirty-five
projects to forty-one, which is the six recovered rounds' fixtures now running.
`DECISIONS.md` carries the account, and the September checkpoint's path citations are
restored.

**The lesson outlives the fix, and is why this entry stays.** A MERGED badge names the
base the pull request had, not `main`. Nothing in the current gates checks that a round
directory referenced anywhere actually reached the default branch, and a stacked round
is exactly the shape that slips through — it was caught here only because a citation
happened to point at one. A gate comparing `state/rounds.json` against what the default
branch actually contains would have caught it directly; whether that is worth building
is a maintainer call and is not filed as an item.

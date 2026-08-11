# ADMIN CLEANUP ROUND

Extends the governance architecture; AGENTS.md rules apply. Read from the public
repo at `b7207e9`, plus the unmerged `patch/priorities-and-slop`. Dispatch after
that branch merges. Confirm current state yourself; pointers are not a spec.

Housekeeping only. Nothing here changes what the repository claims.

## A. Close the dispatch-provenance gaps

Three round directories lack their dispatch: `2026-08-11-scrub-round-2`,
`2026-08-11-contributor-checkers`, and — check — `2026-08-11-public-flip-and-scrub`,
whose dispatch was reconstructed from inline instructions. The maintainer holds the
originals and will supply what he has. For each supplied prompt, replace the
recorded gap with the verbatim dispatch and drop the not-recoverable note; where
nothing is supplied, leave the gap as recorded. Do not paraphrase a dispatch into
existence.

## B. Delete merged branches

Five branches remain on the remote — `feat/contributor-checkers`,
`patch/attribution-provenance-names`, `rename/alignment-workspace`,
`scrub/round-2`, and `patch/priorities-and-slop` once merged. Confirm each is
merged into `main`, then delete it on the remote. Do not delete anything unmerged;
list any that is.

## C. Settle the ledger's mutability

`DECISIONS.md` says settled decisions "are not re-litigated," but the rename round
edited a settled entry in place, as *no negative ontologies* required. The ledger
is therefore neither append-only nor freely editable, and the previous round's
report recorded both readings without picking one. Settle it in the header:

> Settled entries are append-only in substance. Identifiers within them —
> a renamed path, file, or namespace — are updated in place so the record keeps
> resolving; anything else that changes lands as a new dated entry.

State it in the terms above unless you find a case it mishandles, in which case
say so and propose the fix rather than improvising the wording. Record the
clarification as its own dated entry.

## D. A failure case for every gate

Two gates have now shipped and passed while checking nothing: the DCO gate counted
GitHub's synthetic merge commit and would have failed every pull request, and the
attribution gate's first parse accepted the pristine template. Both were caught,
and the attribution gate now carries a self-test.

Make it general. In AGENTS.md, under the checker and gate rules: **every gate
ships a case proving it fails on the null input** — the untouched template, the
absent field, the empty match — wired into the same self-test the gate already
runs, not performed once at review. Then audit the existing gates against it:
`path_gate`, `dco`, `attribution`, `name_lint`, `contrib_hygiene`,
`conservativity`, `check_frozen`, `audit_axioms`, and the registry checker. For
each, either point at the existing null-input case or add one. Report the table:
gate, null case, where it lives.

This is the most valuable item in this round. A gate that reports green while
matching nothing is indistinguishable from a gate that works, and this repository
has produced two in a week.

## E. Stubs awaiting the author

`DECISIONS.md` lists three. Do not decide them; make them decidable. For each,
state in one or two lines what the choice actually costs now — what changes, what
breaks, what it forecloses:

1. Whether further leverage frozen trees are registered now or later.
2. The name of the leverage forward tree (`forward/`).
3. Which deference documents are canonical.

Report these as a short list the maintainer can answer in a sitting.

## F. Consistency sweep

After the priorities round, confirm: no live document, script, or config outside
`prompts/` and `frozen/` refers to `OPEN_PROBLEMS.md` except the two deliberate
pointers into `frozen/consolidation_aug9/`; the eight required check names in the
protection payload still match the CI job names exactly; and `tests/run.py`
invokes every gate script present in `tests/`. Report each as checked, with the
command.

## Report

ROUND_REPORT.md per convention, with **Outstanding maintainer actions** listed
first. Section D's table is the report's substance; the rest is a list of what was
closed.

---
Prompt author: Claude Fable 5 (Anthropic), 2026-08-11, in a maintainer-directed
session. Dispatched by the maintainer.

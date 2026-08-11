# Public flip, runbook retirement, and the first scrub of the note dumps

*Directory created 2026-08-11, after the round. The round was dispatched as short
inline instructions during the branch-protection session rather than as a written
prompt, so there is no document to keep verbatim. What follows is the maintainer's
instructions as recorded, and nothing more — no reconstruction of intent.*

The work in this round landed as PR #1, merged at `b67ff8d`.

## The instructions, as given

Mid-session, following the branch-protection round
(`prompts/2026-08-11-branch-protection/`), whose dispatch **is** kept verbatim and
which staged protection behind a runbook for the maintainer to apply:

> wait sorry just make it public and delete the runbook once the repo is set up

Then:

> scrub the note dumps

Then, on the release gate that the flip left undischarged:

> and i'm going to do the read through after it's public which is fine

## What is not here

No further specification was given. The scope of "scrub" — what counts as
personal, whose names, how to record a judgment call — was decided by the
executing round and reported in `SCRUB_REPORT.md`, not set by the dispatch. The
maintainer's standing instruction on personal material arrived with the round
that followed, which is part of why a second scrub round was needed.

The DCO-gate fix in this pull request was not dispatched at all: the gate failed
the first pull request through it, and the fix was made in the same branch.

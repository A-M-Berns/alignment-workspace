# Public flip, runbook retirement, first scrub — report

> **Reconstructed after the fact on 2026-08-11**, from the pull-request body,
> the three commit messages, and the artifacts the round left in the tree. It is
> not the report the round wrote — the round wrote none, which is the gap this
> directory exists to close. Nothing here is asserted beyond what those sources
> support, and where the round's own reasoning is not recoverable, this says so.

Landed as PR #1, merged at `b67ff8d`. Three commits.

## What was done

**The repository went public and branch protection was applied**, in the same
sitting, at the maintainer's direction. Verified by read-back rather than by
trusting the write: eight required checks, zero required approvals, code-owner
reviews off, enforce-for-admins on, force-pushes and branch deletion blocked.
Direct pushes to `main` are refused for everyone, maintainers included. The
reasoning is in `DECISIONS.md` under *2026-08-11 — public, and branch protection
live*, which is contemporaneous.

**`FLIP_RUNBOOK.md` was retired.** It sequenced a flip that had happened, so
under *no negative ontologies* it goes rather than becoming a historical note.

**The deference note dump was scrubbed** — two cuts, both candid assessments of a
named colleague's abilities, marked `[scrubbed]` inline. The dose-response bundle
needed none. Frozen digests were recomputed and `frozen/MANIFEST.md` annotated in
the same change, which is the sanctioned way frozen content moves. Four judgment
calls went the other way and were recorded with reasons so they could be
reversed; two of them were in fact reversed by the round that followed.

**The DCO gate was fixed.** It counted GitHub's synthetic pull-request merge
commit, which has no author who could sign it, so it failed the first pull
request through it and would have failed every one after. The fix is
`--no-merges`.

## What the round said it could not do

From `SCRUB_REPORT.md` and the commit messages, both contemporaneous: the bundles
were public before the scrub ran, and removal at `HEAD` is not erasure from
history. A mechanical scan for emails, phone numbers, API keys and home paths came
back clean across all 51 files, and that scan cannot see the two categories only a
person can judge — personal-life passages, and candid remarks about named third
parties. The release gate was undischarged at the flip, by the maintainer's
explicit decision.

One error is recorded in the round's own commit message: an image was deleted on
the strength of its filename before its contents were checked, and restored when
it turned out to be a rendered-LaTeX theorem rather than an email screenshot.

## Attribution

| | |
|---|---|
| prompt author | the maintainer, inline; see `PROMPT.md` |
| executor | Claude Opus 5 (Anthropic) |
| dates | 2026-08-11 |
| this reconstruction | Claude Opus 5 (Anthropic), 2026-08-11, in the round recorded at `prompts/2026-08-11-attribution-provenance-names/` |

## What is not recoverable

The round's own account of its deviations and of what it left undone. Reports
under this convention state what was *not* shown; a reconstruction from a merged
pull request can only report what was. Anything the round decided and did not
write down is gone, and this document does not guess at it.

# Report — maintenance sweep of 2026-11-22

| | |
|---|---|
| Prompt author | the maintainer's standing dispatch (`prompts/2026-11-05-standing-maintenance/PROMPT.md`, amended 2026-11-08); the launcher's message kept verbatim in `PROMPT.md` |
| Executor | Claude Fable 5.2 (Anthropic), in Claude Code |
| Date | 2026-11-22 |
| Base | `main` at `69fe09af` |

**Digests.** The freshness audit reported #145 without a digest and the round
`2026-11-10-legitimacy-definition-prosecution` carried by none. `state/prs.json` gains the
digest of #145, drawn from the round's `CURRENT.md`, the fourteenth follow-up's section of
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`, the pull request's
description, the final commit `623605bc`, and `projects/normativity/CLAIMS.md`. This sweep's
pull request carries its own.

**Seed scores.** The audit's other thirty-nine findings were unscored axes: three each on
thirteen concepts of the legitimacy line (`appraisal`, `estimation-and-action-mistakes`,
`evaluation-and-true-utility`, `f-neutral-policy`, `honest-conduct`, `legitimate-and-sound`,
`manipulation-as-induced-mistake`, `options-condition`, `presumed-check-in`, `three-ratings`,
`trajectory`, `warranted-self-trust`, `way-of-valuing`). `graph/events/claude-fable-5-2.jsonl`
is new and holds one `assessment` for each, with its reasoning in `gloss`. Reliability runs
from 2 to 4, with 4 only on `estimation-and-action-mistakes` and `trajectory`; importance 5
on `manipulation-as-induced-mistake`, `evaluation-and-true-utility` and
`legitimate-and-sound`.

**Friction.** The launcher reported *Workspace friction* unchanged, and it is: F1 stays as
filed, F3, F7 and F10 are in the queue unanswered, and the rest are closed. Nothing was
taken.

## Corrections and deviations

- **Seeds are not named in the dispatch.** The sweep wrote them on its own reading, recorded
  as agent-decided in `DECISIONS.md` (2026-11-22).
- **Two blurbs of `state/concepts.json` corrected**, outside both digests and friction:
  `estimation-and-action-mistakes` and `f-neutral-policy` called three results unregistered
  that #145's final commit registered. Same entry.
- **The digest of #145 departs from the pull request's description in three places**, each
  because the description predates the final commit: the fifteen results are registered, not
  proposed; items 139–147 are filed; and one queue entry on the line stands, not three (the
  handle is mapped and the wiki question was decided on 2026-11-18).
- **The merged date is 2026-11-18**, the date of the merge commit in the maintainer's time
  zone and of the ledger's entries; the forge's timestamp is 2026-11-19 UTC.
- **The `Co-Authored-By` trailer names Claude Fable 5.1**, as the launcher's message fixes
  it. The executor is Claude Fable 5.2, as the `Model:` trailer says.
- **The first commit was pushed before the local gates ran**, the machine being on 3%
  battery; the pull request opened after them.

## What this does not establish

- That the digest of #145 is accurate beyond its sources. Of the report's 5179 lines the
  sweep read the fourteenth follow-up's section and `CURRENT.md`; passes one to thirteen
  enter the digest only through those two summaries. It is model-written and unread.
- That any seed score is right. Each is one model's reading of a blurb and of
  `CURRENT.md`; the documents a gloss cites by path were not opened beyond what those two
  quote of them. The scores reorder `/priorities/`.
- That the thirteen blurbs are otherwise current. Two stale phrases were found by reading;
  nothing checks a blurb's registration claims against the registry.

## Verification

See the pull request's description for the gates' results on the pushed head.

## Outstanding maintainer actions

1. **Merge or decline this pull request.** Auto-merge is off by the launcher's instruction.

## Attribution

Prompt-author: the maintainer, via the standing dispatch and its launcher. Executor:
Claude Fable 5.2 (Anthropic). 2026-11-22.

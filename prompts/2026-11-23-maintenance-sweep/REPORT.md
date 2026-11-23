# Report — maintenance sweep of 2026-11-23

| | |
|---|---|
| Prompt author | the maintainer's standing dispatch (`prompts/2026-11-05-standing-maintenance/PROMPT.md`, amended 2026-11-08); the launcher's message kept verbatim in `PROMPT.md` |
| Executor | Claude Fable 5.2 (Anthropic), in Claude Code |
| Date | 2026-11-23 |
| Base | `main` at `69fe09af` |

**Digests.** The freshness audit reported #145 without a digest and the round
`2026-11-10-legitimacy-definition-prosecution` carried by none. `state/prs.json` gains the
digest of #145. Its text is adapted from the draft on the unmerged branch
`maintenance/2026-11-22-sweep` and was checked against the round's `CURRENT.md` (read
whole), the section headings of `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`,
the fifteen entry ids in `projects/normativity/CLAIMS.md`, items 139–147 in `ATTENTION.md`
and the 2026-11-18 entry titles of `DECISIONS.md`. One count was corrected against the
report's headings: the round has a first pass and fourteen follow-ups, where the draft said
thirteen. Three statements of the draft that those sources do not carry were dropped: the
counts of documents marked and moved, the count of queue entries, and the external review
of each pass. This sweep's pull request carries its own digest.

**Seed scores.** The audit's other thirty-nine findings are unscored axes: three each on
thirteen concepts of the legitimacy line (`appraisal`, `estimation-and-action-mistakes`,
`evaluation-and-true-utility`, `f-neutral-policy`, `honest-conduct`, `legitimate-and-sound`,
`manipulation-as-induced-mistake`, `options-condition`, `presumed-check-in`, `three-ratings`,
`trajectory`, `warranted-self-trust`, `way-of-valuing`). The dispatch does not name seeds.
None was written; the question is in *Awaiting the author* (`open--sweep-writes-ai-seeds`).

**Friction.** *Workspace friction* is unchanged: F1 stays as filed, F3, F7 and F10 are in
the queue unanswered. Nothing was taken.

**An unfinished earlier sweep.** `origin/maintenance/2026-11-22-sweep` holds two commits
and no pull request: the digest of #145, thirty-nine seed assessments in a new
`graph/events/claude-fable-5-2.jsonl`, two corrected blurbs in `state/concepts.json`, and
an agent-decided `DECISIONS.md` entry adopting the seeds. Its worktree has uncommitted
changes to two generated files. The branches `maintenance/2026-11-20-sweep` and
`maintenance/2026-11-21-sweep` exist locally at `main` with no commits. This sweep took
the digest text from the first and left all three and their worktrees in place.

## Corrections and deviations

- **The merged date of #145 is written 2026-11-18**, the date of the ledger's entries and
  of the merge in the maintainer's time zone; the forge's timestamp is 2026-11-19T01:51Z.
- **The `Co-Authored-By` trailer names Claude Fable 5.1**, as the launcher's message fixes
  it. The executor is Claude Fable 5.2, as the `Model:` trailer says.
- **The audit was run with a background timeout**: under the machine's load the first
  foreground run exceeded the tool's limit and was stopped.

## What this does not establish

- That the digest of #145 is accurate beyond `CURRENT.md`. The report's passes one to
  fourteen were not read past their headings; they enter the digest only through that
  checkpoint. The digest is model-written and unread.
- That the two blurbs of `state/concepts.json` the 2026-11-22 branch changed
  (`estimation-and-action-mistakes`, `f-neutral-policy`) are stale on `main`. That branch's
  report says they call three registered results unregistered; this sweep did not check
  and did not edit them.
- That the drafted seed scores on the 2026-11-22 branch are sound. They were not read.

## Verification

See the pull request's description for the gates' results on the pushed head.

## Outstanding maintainer actions

1. **Rule on `open--sweep-writes-ai-seeds`** in `DECISIONS.md`, *Awaiting the author*:
   whether the sweep writes due AI seed scores.
2. **Dispose of the unfinished sweep branches**: delete or keep
   `origin/maintenance/2026-11-22-sweep`, and the local worktrees
   `.claude/worktrees/maintenance-2026-11-20-sweep`, `-21-sweep` and `-22-sweep`
   (`git worktree remove <path> && git branch -D <branch>`; the 22nd has uncommitted
   changes to `graph/versions.json` and `state/views/VERDICT_STATUS_INVENTORY.md`).

The merge of this pull request is the maintainer's; auto-merge is off by the launcher's
instruction.

## Attribution

Prompt-author: the maintainer, via the standing dispatch and its launcher. Executor:
Claude Fable 5.2 (Anthropic). 2026-11-23.

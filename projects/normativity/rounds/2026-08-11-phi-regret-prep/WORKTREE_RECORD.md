# Worktree record

| field | value |
|---|---|
| source checkout | `/Users/anson/Desktop/alignment-workspace` |
| source branch at dispatch | `claude/for-ais-refinement` |
| source commit | `9e37c4ff32b343c4f54e31a9edd28826542330c3` |
| source working tree | clean; `git status --short` empty |
| task branch | `research/phi-regret-prep-20260811` |
| task worktree | `/Users/anson/Desktop/alignment-workspace-phi-regret-prep-20260811` |
| base of the task branch | the same commit, exactly |

## Concurrent work

One other linked worktree was present at dispatch and was not touched:
`/Users/anson/Desktop/alignment-workspace-stage-v` on `round/2026-08-11-stage-v`
at `20fd5b6`, which is the parent of the source commit. Nothing in this round
reads or writes it.

The source checkout was on `claude/for-ais-refinement` rather than on `main`,
and `main` is four commits behind it. The task branch is based on the source
checkout's `HEAD` as dispatched, so the pull request opens against the branch
state a reader of the repository currently sees rather than against `main`.

## Files this round touches

Added, all new paths:

- `projects/leverage/rounds/2026-08-11-phi-regret-prep/**` — the environment, its
  documents, its source and its tests.
- `projects/leverage/deck-2026-08-10/**` — the line's first author-written
  artifact, with its intake receipt.
- `prompts/2026-08-11-phi-regret-prep/**` — the dispatch and the report.

Modified:

- `PRIORITIES.md` — three items filed within this round's scope, and one
  workspace-friction entry.
- `DECISIONS.md` — three entries appended to *Awaiting the author*.
- `PROVENANCE.md` — rows for everything added.
- `RESEARCH_STATE.md` — the leverage section's construction and next question.

Nothing under `projects/leverage/consolidation-aug9/` is modified. Nothing under
`projects/deference/` is modified. No frozen artifact moves.

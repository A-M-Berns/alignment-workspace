# Report — digests #133–#140, and maintenance daily

| | |
|---|---|
| Prompt author | the maintainer, in conversation (`PROMPT.md`, verbatim) |
| Executor | Claude Fable 5.1 (Anthropic), in Claude Code |
| Date | 2026-11-08 |
| Base | `main` at `fca35075` |

**Digests.** `state/prs.json` gains the digests of the six merged pull requests the
freshness audit reported without one — #133, #134, #136, #137, #138, #140 — in the file's
shape (number, title, merged date, rounds, topic tags, summary, supersession note,
`state_after`), each drawn from its pull request's description, its round report and the
registry. The pull request for this round carries its own.

**Digests are maintenance.** The standing dispatch
(`prompts/2026-11-05-standing-maintenance/PROMPT.md`) is amended, with the directive
quoted: a sweep first runs the freshness audit and writes every digest it reports
missing, and its own pull request carries its own digest. `AGENTS.md` (§14's
standing-maintenance paragraph) and `site/README.md` say the same.

**Daily.** The sweep runs daily, from the maintainer's machine; this settles the
*Awaiting the author* entry on the sweep's cadence, which is retired.
`.github/workflows/freshness.yml` runs the audit daily instead of weekly, and its
reporter comments on the standing issue only when the findings differ from its last
report there. The dated `DECISIONS.md` entry of 2026-11-08 records the ruling, the
workflow change and four agent-decided details with their rejected alternatives.

## Corrections and deviations

- "digests 133-140" is six pull requests: #135 is not a pull request, and #139 is open.
- The reporter's deduplication was not asked for. A daily audit without it would repeat
  an unchanged finding every day until a merge; it is a change to a write-scope job's
  script, recorded in the dated entry.
- The daily trigger is not in this pull request. It is a `launchd` job and a launcher
  script on the maintainer's machine, because CI holds no credential and cannot run an
  agent. Nothing in the repository depends on it.
- The full `tests/run.py` sweep was not run locally; the gates this change can reach
  were run one by one (below), and CI runs the sweep.

## What this does not establish

- That the digests are accurate. They are model-written from the pull requests' own
  descriptions and reports, `ci-only`, and no maintainer has read them.
- That a daily sweep is the right load on the review queue. An empty day opens nothing
  and no sweep starts while one is open, but the cadence is a ruling to revisit, not a
  measurement.
- That the concept registry is current. `state/concepts.json` is untouched: nothing in
  `site/README.md` settles whether the 2026-11-07 round's objects warrant entries, and
  the amended dispatch routes such a finding to the maintainer as a question.
- The reporter's deduplication has no test. It compares the report with the last
  comment's body, carriage returns stripped; it is exercised the first time the workflow
  runs on `main`.

## Verification

Run on 2026-11-08 in the worktree, Python 3.12:

- `tests/freshness.py --self-test`: twelve cases `ok`. `tests/freshness.py`: no findings.
- `tests/workflow_scope.py`: `clean over 6 workflow(s); 5 enumerated write-scope job(s)`; its self-test passes.
- `checkers.graph --root .`: `OK 2494 nodes, 2603 events, 2094 ranked units`; `graph/versions.json` regenerated.
- `checkers.workspace_state --check`: `valid — 7 projects, 184 modern claims, … 132 rounds`; the handoff views regenerated.
- `checkers.attention_render --check`: `the committed file equals the render (144 items)`.
- `tests/dead_pointers.py`, `tests/untracked_pointers.py`: clean.
- `tests/site_build.py`: 116 pull-request pages, `unresolved: 0`; the DOM gate passes.

## Outstanding maintainer actions

1. **Merge or decline this pull request.** It edits a workflow, so by the ruling of
   2026-11-05 it is not auto-merged.
2. **The daily job on your machine**, `com.anson.alignment-maintenance-sweep`, is
   installed and can be stopped with
   `launchctl bootout gui/$(id -u)/com.anson.alignment-maintenance-sweep`. It starts no
   sweep while this pull request is open.

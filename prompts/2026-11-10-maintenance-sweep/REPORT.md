# Report — maintenance sweep of 2026-11-10

| | |
|---|---|
| Prompt author | the maintainer's standing dispatch (`prompts/2026-11-05-standing-maintenance/PROMPT.md`, amended 2026-11-08); the launcher's message kept verbatim in `PROMPT.md` |
| Executor | Claude Fable 5.1 (Anthropic), in Claude Code |
| Date | 2026-11-10 |
| Base | `main` at `eb98367e`, rebased onto `ed359a51` (#142) during the sweep |

**Digests.** The freshness audit reported #139 without a digest and the round
`2026-11-09-github-sign-in` carried by none. `state/prs.json` gains the digest of #139,
drawn from the two round reports it landed (`prompts/2026-11-09-github-sign-in/REPORT.md`
and the fifth and sixth follow-ups in `prompts/2026-11-05-site-priorities/REPORT.md`) and
the merge's diff. #142 merged during the sweep carrying its own digest. This sweep's pull
request carries its own.

**Friction taken.** Every entry of *Workspace friction* was read; the dispositions:

- **F9, wiki_links accepts a pin that does not resolve — closed.** `checkers/wiki_links.py`
  resolves each commit-pinned link with `git cat-file -e <sha>:<path>`, offline; its
  self-test carries the null cases — a hash differing from `HEAD` in its last four characters,
  a path `HEAD` lacks. The `checkers` job checks out the full history, which the resolver
  needs. The live wiki carried eight occurrences of seven pins the resolver refuses: four into
  the 2026-10-21 rebuttal round and one into the September checkpoint, pinned to commits older
  than the linked files, and three in `wiki/Value-Change-as-Belief-Change.md` pinned to a hash
  differing from a real branch commit in its last four characters — the F9 shape on a second
  page. All eight re-pinned to `eb98367e`. The pull request's first CI run then refused
  thirty-two more occurrences of twenty-two links in seven pages, pinned to two August
  commits no branch reaches — present as objects in older clones, where the local run had
  passed them, and unfetchable in CI. The resolver now requires reachability from some ref
  (`git rev-list --all`), with a dangling commit as its null case, and those thirty-two are
  re-pinned likewise: twenty paths byte-identical at the new pin, one differing in a line of
  register wording, one (the traderized-enforcement round directory) moving from the round's
  first commit to its completed tree. Agent-decided entry in `DECISIONS.md`.
- **F11, no gate refuses committed conflict markers — closed.** Filed by #142 while this sweep
  was running, for the defect this sweep had also found in `main` at its base (#139's merge
  of `DECISIONS.md`). `tests/conflict_markers.py` scans every tracked text file outside
  completed round records for git's opening and closing marker lines, fails on a tree with no
  tracked files, and runs under `tests/run.py`. The residue itself was removed by #142's
  merge; this sweep's own removal was dropped at rebase. Agent-decided entry.
- **F10, a research round has no node of its own on the map** — a protocol rule, so a
  question: queue entry *What a research round files for itself on the map*, with the
  recommendation that the pointers are the record.
- **F7, a dependency on an unindexed checkpoint** — the entry says the choice is
  specification layer, so a question: queue entry *Recording a dependency on an unindexed
  checkpoint*, naming the five 2026-08-30 checkpoints still unindexed and recommending
  retroactive indexing.
- **F1** stays as filed: its own text defers it to work in the same area, and both checks it
  wants need a classification or a heuristic that is a rule choice. **F3** is already in the
  queue. **F2, F4, F5, F6, F8** are closed.

## Corrections and deviations

- The launcher reported the friction section changed since the last sweep; there was no
  earlier sweep, so every entry was read as new.
- #142 merged into `main` after the sweep's worktree was cut, adding its digest, three
  `DECISIONS.md` entries, a queue entry and F11. The branch was rebased onto it; the
  conflicts (the queue, the ledger's tail, two provenance tables, four generated files) were
  resolved by keeping both sides and regenerating, and the sweep's DECISIONS entry on the
  markers was rewritten to say #142 removed them.
- The conflict-marker gate was built before F11 existed, as the §14 contained fix for a defect
  the sweep hit; F11's deliverable shape (round records excluded, `--self-test` on a planted
  marker) was adopted when the item appeared.
- The digest of #139 states one fact its reports do not: that the merge left conflict markers
  in `DECISIONS.md`. It is read off the merge commit's diff.

## What this does not establish

- That the #139 digest is accurate beyond its sources; it is model-written and unread.
- That the eight re-pinned links cite the content their sentences were written against. The
  2026-10-21 and checkpoint links were pinned to commits that predate the files, so the
  sentences never cited a resolvable version; the three in
  `wiki/Value-Change-as-Belief-Change.md` cited a branch commit (`774eb891…6b6b`, not on
  `main`) by a wrong hash, and now cite `main`'s copy of the same paths, which may differ.
- That the resolver's reading of "exists" is the right one: it accepts any commit some ref
  reaches, on `main` or not. Reachability from `main` is not checked, so a page may pin a
  branch commit that is later rewritten; the gate catches that only once the branch is gone.
- The conflict-marker gate does not see files git lists as binary, nor a marker inside a
  completed round record.

## Verification

`python3.12 tests/run.py` on 2026-11-10 in the worktree, after the rebase, exit 0: every
self-test `ok`; `CONFLICT MARKERS: clean over 8213 tracked file(s)`; `WIKI LINKS: clean over
33 page(s)`; `DEAD POINTERS: clean over 59 live document(s)`; `WORKSPACE STATE: valid — …
135 rounds, … 147 priorities`; `ATTENTION RENDER: the committed file equals the render (147
items)`; the site build and DOM gate pass; `GATE COVERAGE: 14 gate scripts, all invoked`;
`ALL GREEN (80 project(s))`; the Lean build skipped, as the sweep builds no Lean.
`checkers.wiki_links` run over `origin/main`'s `wiki/` before the re-pins reported the eight
offending occurrences and nothing else. `tests/freshness.py`: one finding, this round not yet
carried by a digest, which its pull request's digest retires.

After the pull request opened, its `checkers` and `python` jobs failed on the thirty-two
orphan-pinned links above; the local run had passed them because this clone holds the orphan
objects. With the reachability rule and the re-pins, on 2026-11-10: `checkers.wiki_links
--self-test` all `ok` including the dangling-commit case; `WIKI LINKS: clean over 33 page(s)`;
`CONFLICT MARKERS: clean over 8214 tracked file(s)`; `tests/dead_pointers.py` and
`tests/site_build.py` clean. The full `tests/run.py` was not rerun for this amendment — it
touches the checker, `wiki/`, and records only — and CI runs it.

## Outstanding maintainer actions

1. **Merge or decline this pull request.** It edits `checkers/` and a workflow, so by the ruling
   of 2026-11-05 it is not auto-merged.
2. **Rule on the two queue entries** of 2026-11-10 in *Awaiting the author* (F10, F7), or leave
   them queued.

## Attribution

Prompt-author: the maintainer, via the standing dispatch and its launcher. Executor:
Claude Fable 5.1 (Anthropic). 2026-11-10.

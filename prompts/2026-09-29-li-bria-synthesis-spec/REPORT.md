# Attribution — 2026-09-29-li-bria-synthesis-spec

| | |
|---|---|
| Prompt author | the maintainer (`PROMPT.md` and `REVISION.md`, verbatim) |
| Executor | Claude Fable 5.1 (Anthropic), in Claude Code; two literature subagents of the same model in the first pass |
| Round directory | `projects/decision-theory/rounds/2026-09-29-li-bria-synthesis-spec/` |
| Lean | none |
| Landing | its own pull request from `main` after PR #112 |

The round's report is the round directory's `REPORT.md`.  Two passes: the first
delivered the section and the specification; the second, against the review relayed in
`REVISION.md`, corrected the mathematics (the cross-subsidy witness retracted as a BRIA;
the per-round obstruction derived from the paper's definitions alone; the compatibility
derivation audited into five gaps with only a global one-sided statement established;
the interaction fixture demoted to an illustration; the lease-reading Agent Simulates
Predictor marked as a different environment) and separated the general requirements
from the continuation-BRIA specialization.  `REPORT.md` §9 lists the changes.

Deviations, in one place: the section is a new top-level line and continuation BRIA is
cross-linked rather than moved; the second pass edited the first pass's unlanded ledger
entries and priority items in place rather than appending superseding entries, the
pull request's commits being the history; one remembered attribution in the literature
did not check out and is corrected in `AUDIT.md`.

Outside the dispatch, two maintainer instructions in the same session retired the
name lint and replaced it with the rule in `AGENTS.md` that people are named by role;
that change is the first commit on the branch and is recorded in `DECISIONS.md`
(2026-09-29).  The instructions are appended to `PROMPT.md`.

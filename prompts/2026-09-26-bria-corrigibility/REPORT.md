# Attribution — 2026-09-26-bria-corrigibility

| | |
|---|---|
| Prompt author | the maintainer (`PROMPT.md`, verbatim) |
| Executor | Claude Fable 5.1 (Anthropic), in Claude Code |
| Round directory | `projects/deference/rounds/2026-09-26-bria-corrigibility/` |
| Lean | `lean/Workspace/Deference/Contrib/BRIACorrigibility.lean` |
| Landing | the second round of the decision-component pull request, on its branch; no new pull request |

**The follow-up** (`FOLLOWUP.md`, the same day) was dispatched against the pull request
as still open.  It had been merged that day under the round's own merge criteria (merge
commit `f5e6d2e`), so the follow-up landed as its own pull request from `main` — round
directory, Lean and ledger amended in place, a sibling Lean file `BRIAFollowup.lean` —
under the follow-up's merge criteria.  The prompt asked for the round to land inside the decision-component pull request.  The
executor checked that request's CI (green on every job) before starting, revised that
round's wiki text and `DECISIONS.md` entries in place as the prompt directs, and updated
only the outstanding-actions section of its report.  The prompt refers to a "Part C.11"
under ruling 4; the checks meant are Part C.10's, and the round treats them as such.

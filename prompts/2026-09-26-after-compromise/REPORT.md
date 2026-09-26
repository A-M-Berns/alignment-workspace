# Attribution — 2026-09-26-after-compromise

| | |
|---|---|
| Prompt author | the maintainer (`PROMPT.md`, verbatim) |
| Executor | Claude Fable 5.1 (Anthropic), in Claude Code |
| Round directory | `projects/deference/rounds/2026-09-26-after-compromise/` |
| Lean | `lean/Workspace/Deference/Contrib/AfterCompromise.lean` |
| Landing | its own pull request from `main` after PR #111 |

Two deviations from the dispatch's expectations, both reported in the round's
`REPORT.md`: the suppression trap (A.3(f)) closes only once the disclosure duty is
extended to known third-party compromise — the landed clause counts the agent's own
influence only, and the counterexample without the extension is exact; and the
contestability test (C.6) gives a conditional verdict — public knowledge is competed away
on the post-commission selection, private knowledge is not.  The default directive (B.3)
is an ordering by construction, proved to lie in the band and below every legitimate
outcome, not a theorem about what she would prefer.

**The follow-up** (`FOLLOWUP.md`, the same day) was dispatched against the pull request
as open and landed on its branch: `AfterCompromise.lean` §6, the report's last section,
`tests/test_followup.py`.  Part 1's third-party variant is an obstruction on the
consultation model (one influence field; third-party entries at round `0` only) and is
stated as such; the agent-side uncounted variant carries the claim.

# Provenance

| Files | Generator | Review status | Date | Originating round | Chat bundle |
|---|---|---|---|---|---|
| `README.md`, `MEMO.md`, `THEOREM_MAP.md` | Claude Fable 5 (Anthropic) | `ci-only` | 2026-08-24 | `prompts/2026-08-24-enforcement-affordability/` | — |
| `src/`, `tests/` | Claude Fable 5 (Anthropic) | `ci-only` | 2026-08-24 | `prompts/2026-08-24-enforcement-affordability/` | — |

The executor worked from live `origin/main` at
`299fbd1` (the merge of PR #49).

## Pinned inputs

- *Strengthening Logical Induction with Traderized Constraints*,
  mathematical skeleton v44, August 22, 2026 — maintainer-supplied PDF,
  treated as frozen input, sha256
  `868e5007b5c1ef3b417aa163861188005ca5e2b53ec2582dd94e663ae538a1fd`.
  Read in full (11 pages) for Definitions 2.1–2.2, 3.3, 3.5–3.6, 4.1,
  Lemmas 2.3, 3.2, Theorems 3.4, 3.8, 4.4–4.6, 5.3, Proposition 6.1,
  Remarks 4.2, 6.2, and Appendices A–D. Not vendored; cited by checksum.
- `lean/Workspace/Normativity/Contrib/AssessmentProcess.lean` and
  `AssessmentFirm.lean` at this branch's merge base — read in full for the
  G1 gate; file/line citations in `MEMO.md` §0.
- The pinned source formalization at
  `A-M-Berns/Formalized-Agent-Foundations` commit
  `c0d885bfb2f84054ada18c65acec672e04d6d380`:
  `LogicalInduction/Construction/Budgeter.lean` (the `lossCap`,
  `budgetWorldScale`, `budgetScaleFeature`, `priorBudgetBreach`,
  `BudgeterAt` definitions) and
  `LogicalInduction/Construction/TradingFirm.lean` (`tradingFirmWeight`,
  `tradingFirmCutoff`), fetched at that exact revision via the GitHub API
  for the deductive specialization check.

The affordability mechanism, the taxonomy adjudication, the set-gap
functional, and the repaired identity are this round's constructions, not
claims attributed to those sources.

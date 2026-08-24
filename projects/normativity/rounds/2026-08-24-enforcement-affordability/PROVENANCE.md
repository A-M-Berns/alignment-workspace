# Provenance

| Files | Generator | Review status | Date | Originating round | Chat bundle |
|---|---|---|---|---|---|
| `README.md`, `MEMO.md`, `THEOREM_MAP.md` | Claude Fable 5 (Anthropic) | `ci-only` | 2026-08-24 | `prompts/2026-08-24-enforcement-affordability/` | — |
| `src/`, `tests/` | Claude Fable 5 (Anthropic) | `ci-only` | 2026-08-24 | `prompts/2026-08-24-enforcement-affordability/` | — |
| `MEMO.md` continuation sections C-0/C0–C3, `THEOREM_MAP.md` continuation sections, `FOLLOWUP_STOCK.md`, `tests/test_continuation.py`, `README.md` file list | Claude Fable 5 (Anthropic) | `ci-only` | 2026-08-25 | `prompts/2026-08-25-enforcement-affordability-continuation/` | — |

The executor worked from live `origin/main` at
`299fbd1` (the merge of PR #49). The continuation executor worked from the
parent round's branch head `1042c8b`, and wrote **only** the files in its own
row: the parent round's grades, prose and fixtures are unchanged, apart from
the `README.md` fixture count, which the continuation corrects because it
became false.

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
claims attributed to those sources. The self-financing lemma, the
one-coordinate theorem's hypothesis set and its necessity witnesses, the
Appendix D packaging and the Theorem 4.6 converse are the continuation's, on
the same terms.

The continuation re-verified both pinned inputs against the branch it worked
from: the skeleton PDF's sha256 matches the digest above, and every
`Contrib` file/line citation in `MEMO.md` §0 resolves to the declaration it
names.

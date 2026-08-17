# Provenance

Every file in this directory:

- **generator** — `prompts/2026-08-16-traderized-enforcement/`, its dispatch and
  its follow-up, executed by Claude Opus 5 (Anthropic) against dispatches
  written by GPT-5.6 Sol (OpenAI)
- **review status** — `ci-only`
- **date** — 2026-08-16 (first pass), 2026-08-17 (second through sixth passes)

| path | notes |
|---|---|
| `README.md` | |
| `SOURCE_AUDIT.md` | read against the paper source and Lean of the pinned dependency at `1fffea44eece253cda1722568a3adfe34e822f03`; every paper label cited was checked to exist in that tree |
| `MODEL.md` | |
| `FORCE_INTERFACE.md` | second pass; corrected in the third |
| `PAPER_RECONCILIATION.md` | third pass; rewritten in the fourth and fifth as the semantics was corrected twice |
| `SEMANTIC_PROJECTION.md` | fifth pass; the projection obstruction and its witness |
| `src/budgeter.py`, `tests/test_budgeter.py` | sixth pass; why the generalized construction is not the ordinary one |
| `CORE_CONDITION.md` | second pass |
| `ENFORCEMENT.md` | the round's central artifact |
| `FUNDING_AND_SAFETY.md` | |
| `DEDUCTION_SPECIAL_CASE.md` | |
| `INTEGRATION_MAP.md` | |
| `THEOREM_MAP.md` | |
| `PROSECUTION.md` | |
| `src/*.py` | self-contained; imports no other round |
| `tests/*.py` | `test_regressions.py` pins the two counterexamples that retracted claims of the second pass |

`lean/Workspace/Normativity/Contrib/TraderizedEnforcement.lean` carries the same
generator and review status; it is listed in the Lean contrib provenance file.

The literature check in `SOURCE_AUDIT.md` §8 was three targeted searches, and each
item's influence on the construction is stated where it is cited. Two of the three
were read as search summaries rather than from the primary text: the
cost-function-market-maker result and the combinatorial-market-making
hardness result. The Alignment Forum post was fetched. Nothing in the round's
theorems depends on any of the three.

No originating chat bundle.

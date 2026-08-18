# Provenance

Every file in this directory:

- **generator** — `prompts/2026-08-16-traderized-enforcement/`, its dispatch and
  its follow-up, executed by Claude Opus 5 (Anthropic) against dispatches
  written by GPT-5.6 Sol (OpenAI)
- **review status** — `ci-only`
- **date** — 2026-08-16 (first pass), 2026-08-17 (second through eleventh
  passes), 2026-08-18 (proof-closing pass; its dispatch's author model is
  unrecorded)

| path | notes |
|---|---|
| `README.md` | |
| `SOURCE_AUDIT.md` | read against the paper source and Lean of the pinned dependency at `1fffea44eece253cda1722568a3adfe34e822f03`; every paper label cited was checked to exist in that tree |
| `MODEL.md` | |
| `FORCE_INTERFACE.md` | second pass; corrected in the third |
| `PAPER_RECONCILIATION.md` | third pass; rewritten in the fourth and fifth as the semantics was corrected twice |
| `SEMANTIC_PROJECTION.md` | fifth pass; the projection obstruction and its witness |
| `src/budgeter.py`, `tests/test_budgeter.py` | sixth pass; why the generalized construction is not the ordinary one |
| `src/assessment.py`, `tests/test_assessment.py` | seventh pass; the assessment process at the type the Budgeter consumes |
| `NORMATIVE_SAFETY.md`, `src/normative.py`, `tests/test_normative.py` | seventh pass; whether the motivating statics discharge safety |
| `src/outflow.py`, `tests/test_outflow.py` | eighth pass; the account. Ninth pass; the cost product, the deficit certificate, subaccounts, bounded replenishment, and the withdrawal of the depth-only theorem |
| `src/force_api.py` | sixth pass; ninth pass added the funded entry point; tenth pass added the safety-certified one and the request binding; eleventh closed the assessment identity and canonicalized row order |
| `CORE_CONDITION.md` | second pass |
| `ENFORCEMENT.md` | the round's central artifact |
| `FUNDING_AND_SAFETY.md` | |
| `DEDUCTION_SPECIAL_CASE.md` | |
| `INTEGRATION_MAP.md` | |
| `THEOREM_MAP.md` | rewritten in the proof-closing pass into settled / conditional / open / refuted |
| `PROOF_CLOSURE.md` | proof-closing pass; the arc arrow by arrow, the property-family classification, and the kill questions |
| `src/coherence.py`, `tests/test_coherence.py` | proof-closing pass; the exact dual-distance presentation, and the independent distance program it is checked against |
| `PROSECUTION.md` | |
| `src/*.py` | self-contained; imports no other round |
| `tests/*.py` | `test_regressions.py` pins the two counterexamples that retracted claims of the second pass |

`lean/Workspace/Normativity/Contrib/TraderizedEnforcement.lean` carries the same
generator and review status, as do the eight Lean files the proof-closing pass added;
all nine are listed in the Lean contrib provenance file.

The literature check in `SOURCE_AUDIT.md` §8 was three targeted searches, and each
item's influence on the construction is stated where it is cited. Two of the three
were read as search summaries rather than from the primary text: the
cost-function-market-maker result and the combinatorial-market-making
hardness result. The Alignment Forum post was fetched. Nothing in the round's
theorems depends on any of the three.

No originating chat bundle.

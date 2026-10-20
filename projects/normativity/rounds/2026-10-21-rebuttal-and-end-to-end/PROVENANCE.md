# Provenance

| artifact | generator | review status | date | originating round |
| --- | --- | --- | --- | --- |
| `README.md`, `REPORT.md`, `REBUTTAL.md`, `LANDING.md`, `WITNESS.md`, `PROVENANCE.md` | Claude Fable 5.1 (Anthropic); the prompt by the maintainer, relayed verbatim | `ci-only` | 2026-10-21 | `prompts/2026-10-21-rebuttal-and-end-to-end/` |
| `src/rebuttal.py`, `src/exhibit.py`, `tests/run.py`, `tests/test_rebuttal.py` | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-10-21 | `prompts/2026-10-21-rebuttal-and-end-to-end/` |
| `lean/Workspace/Normativity/Contrib/SeedStatics.lean` | sections 1–6, 8, 10 of the branch file by Claude Fable 5.1 (Anthropic), round `2026-09-16-seed-statics`; landed with five additions by the same model, this round | `ci-only` | 2026-10-21 | `prompts/2026-10-21-rebuttal-and-end-to-end/` (landing); `prompts/2026-09-16-seed-statics/` (origin) |
| `lean/Workspace/Normativity/Contrib/ConvergenceMeasure.lean` | sections 1–4 of the branch file by Claude Fable 5.1 (Anthropic), round `2026-09-17-convergence-measure`; landed by this round | `ci-only` | 2026-10-21 | `prompts/2026-10-21-rebuttal-and-end-to-end/` (landing); `prompts/2026-09-17-convergence-measure/` (origin) |
| `lean/Workspace/Normativity/Contrib/WarrantEntitlement.lean` (Part A; Part 0 removed) | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-10-21 | `prompts/2026-10-21-rebuttal-and-end-to-end/` |
| `lean/Workspace/Normativity/Contrib/EndToEndWitness.lean` | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-10-21 | `prompts/2026-10-21-rebuttal-and-end-to-end/` |
| `projects/normativity/seed/README.md`, the two `ORIGIN.md` files | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-10-21 | `prompts/2026-10-21-rebuttal-and-end-to-end/` |
| `projects/normativity/seed/rounds/2026-09-16-seed-statics/**` (except `ORIGIN.md`), `prompts/2026-09-16-seed-statics/**` | verbatim from branch `round/2026-09-16-seed-statics`; Claude Fable 5.1 (Anthropic), prompt by the maintainer | `ci-only` | 2026-09-16 | `prompts/2026-09-16-seed-statics/` |
| `projects/normativity/seed/rounds/2026-09-17-convergence-measure/**` (except `ORIGIN.md`), `prompts/2026-09-17-convergence-measure/**` | verbatim from branch `round/2026-09-17-convergence-measure`; Claude Fable 5.1 (Anthropic), prompt by the maintainer | `ci-only` | 2026-09-17 | `prompts/2026-09-17-convergence-measure/` |
| `wiki/Seed-Theory.md`; entries in `wiki/Normativity.md`, `wiki/Theorem-Spine.md`, `wiki/_Sidebar.md` | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-10-21 | `prompts/2026-10-21-rebuttal-and-end-to-end/` |

Lean is adjudicated by the kernel and the axiom audit. The Python is exact
`fractions.Fraction`; the two market exhibits use a one-coordinate market maker that zeroes
the aggregate and are `test-supported`.

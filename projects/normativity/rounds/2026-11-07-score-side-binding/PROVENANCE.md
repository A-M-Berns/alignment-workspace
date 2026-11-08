# Provenance

| artifact | generator | review status | date | originating round |
| --- | --- | --- | --- | --- |
| `README.md`, `REPORT.md`, `THEOREM.md`, `PROVENANCE.md` | Claude Fable 5.1 (Anthropic); the prompt by Claude Fable 5.1 (Anthropic) in conversation with the maintainer, relayed verbatim | `ci-only` | 2026-11-07 | `prompts/2026-11-07-score-side-binding/` |
| `lean/Workspace/Normativity/Contrib/WarrantInductorScoreSide.lean`, `WarrantSolvency.lean`, `RobustWarrant.lean`, `AdmissionByStanding.lean` (new; revised 2026-11-08 under `PROMPT-followup.md`) | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-11-07 | `prompts/2026-11-07-score-side-binding/` |
| `prompts/2026-11-07-score-side-binding/REVIEW-astra-2026-11-08.md` (verbatim) | GPT-6 Astra (OpenAI), via `codex`, an independent review of pull request #140 at `d3d3542e` | `maintainer-reviewed` — the maintainer checked its findings against the Lean source and fixed the dispositions in `PROMPT-followup.md` | 2026-11-08 | `prompts/2026-11-07-score-side-binding/` |
| `prompts/2026-11-07-score-side-binding/PROMPT-followup.md` (verbatim) | the maintainer, in conversation with Claude Fable 5.1 (Anthropic) | `maintainer-reviewed` | 2026-11-08 | `prompts/2026-11-07-score-side-binding/` |

Lean is adjudicated by the kernel and the axiom audit. No Python in this round is
theorem-bearing.

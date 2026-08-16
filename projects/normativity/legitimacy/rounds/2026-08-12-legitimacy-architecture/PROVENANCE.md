# Provenance

| file or glob | generator | review status | date | round | chat bundle |
|---|---|---|---|---|---|
| `README.md`, `THEOREM_MAP.md`, `PROSECUTION.md` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-08-12 | `prompts/2026-08-12-legitimacy-reorganization/`; prompt author GPT-5.6 Sol (OpenAI) | — |
| `src/**`, `tests/**` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-08-12 | same | — |

The Python results are exact finite checks and displayed witnesses, not registered
claims. Nothing in this round is in Lean; `THEOREM_MAP.md` identifies four
candidate port statements.

The latent pair in `src/scenarios.py` re-instantiates a construction proved in
`projects/deference/note-dump-2026-08-11/deference-trust-lab/run3/work/trace-nonrecoverability/`,
which is that tree's work and is cited rather than re-derived.

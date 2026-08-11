# Provenance

| file or glob | generator | review status | date | round |
|---|---|---|---|---|
| `*.md` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-08-11 | `prompts/2026-08-11-phi-regret-prep/` |
| `src/**` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-08-11 | same — exact rationals; no float appears in any theorem-bearing path |
| `tests/**` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-08-11 | same — 25 tests over fifteen fixtures; passing is evidence for the displayed finite instances and nothing else |

Prompt author: **GPT-5.6 Sol**, named in the dispatch's own provenance block.
Executor: **Claude Opus 5 (Anthropic)**. No originating chat bundle exists.

## What is not covered by any label here

`src/model.py` reimplements the obligation fields of
`projects/leverage/forward/src/answerability.py` rather than importing them,
because that tree declares itself disposable. **No cross-check against the
original was run**, and none would mean much while the original is not evidence
for anything. `THEOREM_LEDGER.md` records it as `PR-A2`, architected.

Nothing in this tree is registered in `projects/leverage/CLAIMS.md`, and nothing
here changes the status of any claim of
`projects/leverage/consolidation-aug9/`, which stays authoritative for everything
it states.

# Provenance

| File / glob | Generator | Review status | Date | Originating round |
|---|---|---|---|---|
| `README.md`, `PROBLEM_STATEMENT.md`, `TEST_SUITE.md`, `AUDIT.md`, `REPORT.md`, `PROVENANCE.md` | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-09-29 | `prompts/2026-09-29-li-bria-synthesis-spec/` |
| `src/*.py`, `tests/*.py` | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-09-29 | `prompts/2026-09-29-li-bria-synthesis-spec/` |
| `../../README.md` (the line's entry point) | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-09-29 | `prompts/2026-09-29-li-bria-synthesis-spec/` |
| `prompts/2026-09-29-li-bria-synthesis-spec/PROMPT.md` (the dispatch) | the maintainer, relayed verbatim | `ci-only` | 2026-09-29 | `prompts/2026-09-29-li-bria-synthesis-spec/` |
| `prompts/2026-09-29-li-bria-synthesis-spec/REVISION.md`, `REVISION2.md`, `REVISION3.md` (the review dispatches) | the maintainer, relayed verbatim | `ci-only` | 2026-09-29 | `prompts/2026-09-29-li-bria-synthesis-spec/` |
| `prompts/2026-09-29-li-bria-synthesis-spec/REPORT.md` | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-09-29 | `prompts/2026-09-29-li-bria-synthesis-spec/` |
| the second pass: every document above rewritten, `src/cm.py`, `src/newcomb.py`, `tests/test_cm.py`, `tests/test_newcomb.py` | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-09-29 | `prompts/2026-09-29-li-bria-synthesis-spec/` (`REVISION.md`) |
| the third pass: every document above rewritten, `tests/test_cm.py`, `tests/test_newcomb.py` | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-09-29 | `prompts/2026-09-29-li-bria-synthesis-spec/` (`REVISION2.md`) |
| the fourth pass: `README.md`, `PROBLEM_STATEMENT.md`, `TEST_SUITE.md`, `AUDIT.md`, `REPORT.md` amended | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-09-29 | `prompts/2026-09-29-li-bria-synthesis-spec/` (`REVISION3.md`) |

The literature audit in `AUDIT.md` §1 was compiled from the sources fetched on
2026-09-29 by two subagents of the executor; every citation there was checked by
fetching the named page or PDF, and the one attribution that did not check out is
marked in place.

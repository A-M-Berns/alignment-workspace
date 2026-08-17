# Provenance

| file or glob | generator | review status | date | round | chat bundle |
|---|---|---|---|---|---|
| `README.md`, `MODEL.md`, `COUNTERFACTUAL_INTERFACE.md`, `PROSECUTION.md`, `THEOREM_MAP.md`, `BOUNDARY.md` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-08-17 | `prompts/2026-08-17-counterfactual-legitimacy/`; prompt author GPT-5.6 Sol (OpenAI) | — |
| `src/**`, `tests/**` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-08-17 | same | — |

Exact finite checks and displayed witnesses, not registered claims. No Lean, and
`THEOREM_MAP.md` §7 says why none is proposed.

**Declared dependency.** `tests/run.py` puts
`rounds/2026-08-13-procedural-legitimacy/src` on the path and the round's
`Trajectory`, four conditions, disclosure and prospectivity clauses, and target
`L*` are imported from it rather than re-implemented. The runner fails with a
named error if that directory is absent.

The counterfactual instrument is ported from
`projects/deference/dose-response-note-dump-2026-07-02/dose-response.md` §2.3,
§6.3(e) and §8, cited rather than restated; `THEOREM_MAP.md` §5 records which of
its design constraints survive the transfer.

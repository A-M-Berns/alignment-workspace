# Provenance

| file or glob | generator | review status | date | round | chat bundle |
|---|---|---|---|---|---|
| `README.md`, `MODEL.md`, `COUNTERFACTUAL_INTERFACE.md`, `PROSECUTION.md`, `THEOREM_MAP.md`, `BOUNDARY.md` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-08-17 | `prompts/2026-08-17-counterfactual-legitimacy/`; prompt author GPT-5.6 Sol (OpenAI) | — |
| `src/**`, `tests/**` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-08-17 | same | — |
| `LEGITIMACY_INTERFACE.md`, `LEGITIMACY_TO_TRUST_INTERFACE.md` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-08-17 | `prompts/2026-08-17-counterfactual-legitimacy/PROMPT-CONTINUATION.md`; prompt author GPT-5.6 Sol (OpenAI) | — |
| `src/response.py`, `src/coverage.py`, `src/trust.py`, `src/legitimacy.py`, `tests/test_object.py`, `tests/test_coverage.py`, `tests/test_trust.py` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-08-17 | same continuation | — |

Exact finite checks and displayed witnesses, not registered claims. No Lean, and
`THEOREM_MAP.md` §7 says why none is proposed.

**Declared dependency.** `tests/run.py` puts
`rounds/2026-08-13-procedural-legitimacy/src` on the path and the round's
`Trajectory`, four conditions, disclosure and prospectivity clauses, and target
`L*` are imported from it rather than re-implemented. The runner fails with a
named error if that directory is absent.

`src/trust.py` recomputes the definitions of
`lean/Workspace/Deference/Contrib/DelegationBridge.lean` in exact rationals so the
composition can be checked. It is a re-typing for prosecution, not a port: the
Lean file remains the statement of record and nothing here is proposed as one.

The counterfactual instrument is ported from
`projects/deference/dose-response-note-dump-2026-07-02/dose-response.md` §2.3,
§6.3(e) and §8, cited rather than restated; `THEOREM_MAP.md` §5 records which of
its design constraints survive the transfer.

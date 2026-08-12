# Provenance

| file or glob | generator | review status | date | round | chat bundle |
|---|---|---|---|---|---|
| `TIME_INDEXED_CORRECTIVE_CAPABILITY.md`, `TIME_INDEXED_CORRECTIVE_CAPABILITY_FOR_HUMANS.md`, `REVIEW.md` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-08-12 | `prompts/2026-08-12-time-indexed-corrective-capability/`; prompt author GPT-5.6 Sol (OpenAI) | — |

The round's adversarial review ran in a **separate Claude Opus 5 context** with the Lean
file and the dispatch's attack list, and without the constructing context's reasoning. It
refuted two of the round's three headline claims. All fourteen findings were accepted;
the refutations are theorems in §10 of the Lean file rather than prose replies, and
`REVIEW.md` records the disposition.

No claim is registered. The Lean lives at
`lean/Workspace/Deference/Contrib/TimeIndexedCapability.lean` with its own provenance row
in `lean/Workspace/Deference/Contrib/PROVENANCE.md`.

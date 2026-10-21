# Provenance

| artifact | generator | review status | date | originating round |
| --- | --- | --- | --- | --- |
| `README.md`, `REPORT.md`, `HANDOFFS.md`, `THEOREM_STORY.md`, `PROVENANCE.md` | Claude Fable 5.1 (Anthropic); the prompt by the maintainer, relayed verbatim | `ci-only` | 2026-10-22 | `prompts/2026-10-22-normative-inductor-integration/` |
| `src/inductor.py`, `tests/run.py`, `tests/test_inductor.py` | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-10-22 | `prompts/2026-10-22-normative-inductor-integration/` |
| `lean/Workspace/Normativity/Contrib/OddsBankroll.lean`, `WarrantForce.lean`, `WarrantInductor.lean`, `WarrantInductorWitness.lean` | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-10-22 | `prompts/2026-10-22-normative-inductor-integration/` |
| `lean/Workspace/Normativity/Contrib/WarrantEntitlement.lean` (the grounded survivors, `SupportedOn`, the account instance), `EndToEndWitness.lean` (under the grounded rule) | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-10-22 | `prompts/2026-10-22-normative-inductor-integration/` |

Lean is adjudicated by the kernel and the axiom audit. The Python is exact
`fractions.Fraction` and recomputes the fixture's constants; it certifies nothing on its own.

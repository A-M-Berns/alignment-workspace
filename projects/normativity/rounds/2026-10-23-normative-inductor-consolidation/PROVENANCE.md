# Provenance

| artifact | generator | review status | date | originating round |
| --- | --- | --- | --- | --- |
| `README.md`, `REPORT.md`, `THEOREM.md`, `THEOREM_STORY.md`, `PROVENANCE.md` | Claude Fable 5.1 (Anthropic); the prompt by the maintainer, relayed verbatim | `ci-only` | 2026-10-23 | `prompts/2026-10-23-normative-inductor-consolidation/` |
| `src/consolidation.py`, `tests/run.py`, `tests/test_consolidation.py` | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-10-23 | `prompts/2026-10-23-normative-inductor-consolidation/` |
| `lean/Workspace/Normativity/Contrib/WarrantInductorRebuttal.lean` (new) | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-10-23 | `prompts/2026-10-23-normative-inductor-consolidation/` |
| `lean/Workspace/Normativity/Contrib/WarrantInductor.lean` (`Origin`, `Entitlement`, `Outcome`, `compileAt` on `CompileResult`, `AdapterProtocol.restrict`, the theorem's signature), `WarrantInductorWitness.lean` (`entitlement` on `state₀`, `answered_not_entitled`, `undercut_summary`, `progress_le`) | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-10-23 | `prompts/2026-10-23-normative-inductor-consolidation/` |

Lean is adjudicated by the kernel and the axiom audit. The Python is exact
`fractions.Fraction` and recomputes the two scenarios' constants; it certifies nothing on its
own.

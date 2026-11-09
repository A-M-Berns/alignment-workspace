# Provenance

| artifact | generator | review status | date | originating round |
| --- | --- | --- | --- | --- |
| `README.md`, `REPORT.md`, `THEOREM.md`, `PROVENANCE.md` | Claude Fable 5.1 (Anthropic); the prompt by Claude Fable 5.1 (Anthropic) in conversation with the maintainer, kept verbatim | `ci-only` | 2026-11-08 | `prompts/2026-11-08-content-recollection/` |
| `lean/Workspace/Normativity/Contrib/RowAlternative.lean`, `Conservativity.lean`, `IncompatibilitySemantics.lean`, `ExpressesByRole.lean`, `Recollection.lean`, `PrecedentConstraint.lean` (new) | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-11-08 | `prompts/2026-11-08-content-recollection/` |
| `prompts/2026-11-08-content-recollection/REVIEW-astra-2026-11-08.md` (verbatim) | GPT-6 Astra (OpenAI), via `codex`, an independent review of this round's pull request | `ci-only` | 2026-11-08 | `prompts/2026-11-08-content-recollection/` |

Lean is adjudicated by the kernel and the axiom audit. `RowAlternative.lean` imports
`EconCSLib.Math.LinearAlgebra.Farkas` from the pinned dependency set; its two theorems audit to
the three allowed axioms. No Python in this round is theorem-bearing.

# Provenance — `Workspace.Deference.Contrib`

| file | generator | review status | date | round | chat bundle |
|---|---|---|---|---|---|
| `InheritedAlgebra.lean` | `prompts/2026-08-11-faithful-acceleration/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-11 | `prompts/2026-08-11-faithful-acceleration/` | — |
| `FaithfulAcceleration.lean` | `prompts/2026-08-11-faithful-acceleration/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-11 | `prompts/2026-08-11-faithful-acceleration/` | — |
| `MagnitudePrediction.lean` | `prompts/2026-08-11-phase-ii-prediction/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-11 | `prompts/2026-08-11-phase-ii-prediction/` | — |
| `DelegationBridge.lean` | `prompts/2026-08-11-phase-ii-promotion/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-11 | `prompts/2026-08-11-phase-ii-promotion/` | — |
| `CertificateBounds.lean` | `prompts/2026-08-11-phase-ii-promotion/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-11 | `prompts/2026-08-11-phase-ii-promotion/` | — |
| `SubstitutionSeparation.lean` | `prompts/2026-08-11-phase-ii-promotion/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-11 | `prompts/2026-08-11-phase-ii-promotion/` | — |
| `ExposureGeometry.lean` | `prompts/2026-08-11-phase-ii-promotion/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-11 | `prompts/2026-08-11-phase-ii-promotion/` | — |

`InheritedAlgebra.lean` transcribes statements from
`projects/deference/note-dump-2026-06-27/lean/LeanDeference.lean`; per-declaration
attribution to the inherited source is in each docstring.

`FaithfulAcceleration.lean` transcribes its Layer-1 statements from
`projects/deference/note-dump-2026-06-27/lean/FaithfulAcceleration.lean`; its Layer 2 is new
in this round.

Neither file's `weight_not_divergent` is promotable to `CLAIMS.md`: it ships no term
inhabiting its full hypothesis package. See the round report, §4.

`DelegationBridge.lean`, `CertificateBounds.lean`, `SubstitutionSeparation.lean` and
`ExposureGeometry.lean` port hand proofs from four wave-1 round reports, cited by path and
section in each docstring: `prompts/2026-08-11-deference-finite-kernel/REPORT.md` §1.2,
`prompts/2026-08-11-deference-certificates/REPORT.md` §1.2–§1.3,
`prompts/2026-08-11-deference-channel/REPORT.md` §1.2–§1.3, and
`prompts/2026-08-11-deference-densification/REPORT.md` §1. Every declaration in the four is
hypothesis-complete and every ported theorem ships a typechecking term inhabiting its full
hypothesis package.

`MagnitudePrediction.lean` is new in its round. Its
`squaredError_bdd_of_sharpness_bdd` is likewise not promotable — it carries an undischarged
`EfficientlyComputable` certificate and ships no term inhabiting its full hypothesis
package. Every other declaration in that file is hypothesis-complete and ships a witness.

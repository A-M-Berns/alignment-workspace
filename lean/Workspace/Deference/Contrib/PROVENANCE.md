# Provenance — `Workspace.Deference.Contrib`

| file | generator | review status | date | round | chat bundle |
|---|---|---|---|---|---|
| `InheritedAlgebra.lean` | `prompts/2026-08-11-faithful-acceleration/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-11 | `prompts/2026-08-11-faithful-acceleration/` | — |
| `FaithfulAcceleration.lean` | `prompts/2026-08-11-faithful-acceleration/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-11 | `prompts/2026-08-11-faithful-acceleration/` | — |

`InheritedAlgebra.lean` transcribes statements from
`projects/deference/note-dump-2026-06-27/lean/LeanDeference.lean`; per-declaration
attribution to the inherited source is in each docstring.

`FaithfulAcceleration.lean` transcribes its Layer-1 statements from
`projects/deference/note-dump-2026-06-27/lean/FaithfulAcceleration.lean`; its Layer 2 is new
in this round.

Neither file's `weight_not_divergent` is promotable to `CLAIMS.md`: it ships no term
inhabiting its full hypothesis package. See the round report, §4.

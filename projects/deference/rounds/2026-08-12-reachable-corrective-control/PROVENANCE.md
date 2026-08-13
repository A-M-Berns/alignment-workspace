# Provenance

| file or glob | generator | review status | date | round | chat bundle |
|---|---|---|---|---|---|
| `REACHABLE_CORRECTIVE_CONTROL.md`, `REACHABLE_CORRECTIVE_CONTROL_FOR_HUMANS.md`, `REVIEW.md` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-08-13 | `prompts/2026-08-12-reachable-corrective-control/`; prompt author GPT-5.6 Sol (OpenAI) | — |

The Lean the three documents describe is
`lean/Workspace/Deference/Contrib/ReachableCorrectiveControl.lean`, with its own row in
`lean/Workspace/Deference/Contrib/PROVENANCE.md`. No claim is registered by this round.

`REVIEW.md` records an adversarial review run in a separate model context, given the Lean
file and the dispatch's fourteen attacks and not this round's reasoning. That context is
also Claude Opus 5 (Anthropic), which is a limit on the review's independence and is stated
rather than assumed away.

# Provenance — `Workspace.Normativity.Contrib`

| file | generator | review status | date | round | chat bundle |
|---|---|---|---|---|---|
| `PhiRegretBridge.lean` | `prompts/2026-08-11-phi-regret-bridge/` (executor: GPT-5 Codex, OpenAI; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-11 | `prompts/2026-08-11-phi-regret-bridge/` | — |
| `SurgicalRepairBound.lean` | `prompts/2026-08-13-crown-jewel-learning-theorem-refinement/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-13 | `prompts/2026-08-13-crown-jewel-learning-theorem-refinement/` | — |
| `TraderizedEnforcement.lean` | `prompts/2026-08-16-traderized-enforcement/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-16/17 | `prompts/2026-08-16-traderized-enforcement/` | — |

`PhiRegretBridge.lean` proves the eight-element cardinality, a generic
finite-horizon regret-preservation lemma, and the recurrent-failure lower bound.

`SurgicalRepairBound.lean` proves the surgical lower bound
`delta * sum q <= sum (q * d)`, the mass bound `sum q <= B / delta`, and the
conditional rate `(sum q) / M <= B / (delta * M)`, with an inhabitation witness
and a witness that the margin's positivity is load-bearing. The regret upper bound
enters as an explicit hypothesis.

`TraderizedEnforcement.lean` proves the enforcement inequality
`sum_j beta_j g_j^2 <= <zeta_E, x - p>` at any point meeting every row, its
nonnegativity reading, its slack-and-volume reading, and exact enforcement at
slack zero, with an inhabitation witness at which the inequality is an equality.
Logical Induction's market maker enters only as a hypothesis bounding the
aggregate position's value at a region point.

None of the three formalizes its round's Python model, and none formalizes an
external theorem it cites.

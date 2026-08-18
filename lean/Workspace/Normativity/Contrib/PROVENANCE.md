# Provenance — `Workspace.Normativity.Contrib`

| file | generator | review status | date | round | chat bundle |
|---|---|---|---|---|---|
| `PhiRegretBridge.lean` | `prompts/2026-08-11-phi-regret-bridge/` (executor: GPT-5 Codex, OpenAI; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-11 | `prompts/2026-08-11-phi-regret-bridge/` | — |
| `SurgicalRepairBound.lean` | `prompts/2026-08-13-crown-jewel-learning-theorem-refinement/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-13 | `prompts/2026-08-13-crown-jewel-learning-theorem-refinement/` | — |
| `TraderizedEnforcement.lean` | `prompts/2026-08-16-traderized-enforcement/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-16/17 | `prompts/2026-08-16-traderized-enforcement/` | — |
| `AssessmentProcess.lean`, `AssessmentFirm.lean`, `AssessmentProperties.lean`, `EnforcementStrategy.lean`, `EnforcementPreservation.lean`, `DeductiveEnforcement.lean`, `CoherenceModulus.lean`, `IntrinsicCoherence.lean` | `prompts/2026-08-16-traderized-enforcement/` (executor: Claude Opus 5, Anthropic; prompt author: unrecorded) | `ci-only` | 2026-08-18 | `prompts/2026-08-16-traderized-enforcement/` | — |

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

None of these formalizes its round's Python model, and none formalizes an
external theorem it cites.

`AssessmentProcess.lean` and `AssessmentFirm.lean` lift the pinned dependency's
`Budgeter`, `TradingFirm` and exploitation criterion from a `DeductiveProcess` to
an `Assessment` — a family of world sets exposing a finite sound-and-complete
enumeration of the payout tables its worlds realise on a finite sentence support,
with support-local temporal nesting. They prove the analogues of `lem:budgeter`
parts 1--3 and of `lem:tfdom` against the dependency's own `Strategy`, `Trader`,
`EF`, `PCWorld` and `MarketMaker`, that `MarketMaker (TradingFirm^L)` satisfies the
generalized criterion, that the deductive instance recovers the source's Budgeter
value at every date and world, and that some assessment process is the deductive
instance of no deductive process. Logical Induction's `lem:mm` is used as the
dependency's theorem, not restated.

`EnforcementStrategy.lean` exhibits the compiled enforcement position as a
`LogicalInduction.Strategy n` and proves its exact rational value against a payout
table is the quantity `TraderizedEnforcement.lean`'s inequalities bound, together
with the rank, support and continuity facts that make it legal, and the per-row
tolerance corollary.

`EnforcementPreservation.lean` and `DeductiveEnforcement.lean` build the recursions
pricing the generalized firm plus one added trader and the source firm plus one
added trader, split the aggregate, and conclude the generalized and the original
criterion respectively from a bound on the added trader's assessed cumulative
liability. `DeductiveEnforcement.lean` also derives that bound as zero for a
presentation every deductively plausible world satisfies.

`AssessmentProperties.lean` generalizes two of the source's property families to an
assessment process, and recovers their deductive instances, exhibiting the shape
every family's hypotheses take.

`CoherenceModulus.lean` proves the modulus that turns presentation-relative row
conformance into a coherence measure: conformance at tolerance `delta` on an
`l1`-net of mesh `m` bounds the support gap of every coefficient vector in the unit
ball by `delta + m`, with the Hoelder step supplying the constant. The
identification of that supremum with the sup-norm distance to the convex hull is
ordinary convex duality, cited rather than reproved; the negative half -- that an
arbitrary presentation of the same region bounds no distance -- is a witness in the
round's `test_deduction.PresentationRelativeConformance`.

`IntrinsicCoherence.lean` composes the two: under a distance-complete
support-function presentation, per-row conformance at `delta` says that some
admissible credence's expectations are within `delta` of the displayed prices in
every priced coordinate, with no mesh and no presentation-dependent constant. The
distance-completeness of the exact dual-distance family is the arc's one
unformalized link -- established on paper and by exhaustive verification over
rational grids in the round's `tests/test_coherence.py`.

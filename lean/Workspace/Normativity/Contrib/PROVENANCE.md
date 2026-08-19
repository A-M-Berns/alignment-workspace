# Provenance — `Workspace.Normativity.Contrib`

| file | generator | review status | date | round | chat bundle |
|---|---|---|---|---|---|
| `PhiRegretBridge.lean` | `prompts/2026-08-11-phi-regret-bridge/` (executor: GPT-5 Codex, OpenAI; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-11 | `prompts/2026-08-11-phi-regret-bridge/` | — |
| `SurgicalRepairBound.lean` | `prompts/2026-08-13-crown-jewel-learning-theorem-refinement/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-13 | `prompts/2026-08-13-crown-jewel-learning-theorem-refinement/` | — |
| `TraderizedEnforcement.lean` | `prompts/2026-08-16-traderized-enforcement/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-16/17 | `prompts/2026-08-16-traderized-enforcement/` | — |
| `AssessmentProcess.lean`, `AssessmentFirm.lean`, `AssessmentProperties.lean`, `EnforcementStrategy.lean`, `EnforcementPreservation.lean`, `DeductiveEnforcement.lean`, `CoherenceModulus.lean`, `IntrinsicCoherence.lean` | `prompts/2026-08-16-traderized-enforcement/` (executor: Claude Opus 5, Anthropic; prompt author: unrecorded) | `ci-only` | 2026-08-18 | `prompts/2026-08-16-traderized-enforcement/` | — |
| `MaxMinRepresentation.lean` | `prompts/2026-08-18-maxmin-representation/` (executor: Claude Opus 5, Anthropic; prompt author: unrecorded) | `ci-only` | 2026-08-18 | `prompts/2026-08-18-maxmin-representation/` | — |

`MaxMinRepresentation.lean` proves Ovchinnikov's max–min representation theorem
(Beiträge zur Algebra und Geometrie 43 (2002) 297–302, Theorem 4.1) for a piecewise
affine function on a nonempty convex subset of a topological real vector space, in
both directions, together with its Lemma 4.1, the continuity of a piecewise affine
function on a closed domain, and an inhabitation witness. It is the only file here
that formalizes an external theorem rather than taking one as a hypothesis. One
declaration in it, `isPiecewiseAffineOn_maxMin` (the converse direction), was proved
by Harmonic's Aristotle from a statement and proof outline written here, then
reviewed and rebuilt locally; every other proof in the file is the executor's.

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

The closure pass added the inhabitation witness the round's theorems of record were
missing: `DeductiveEnforcement.witness_market_not_exploited` instantiates the whole
hypothesis package at a deductive process revealing one atom, with the liability bound
derived from the force algebra rather than assumed, and `witnessPres_is_violable` shows
the compiled position is not the zero trader. This answers `PRIORITIES.md` item 41.

## The projection-enforcement pass (2026-08-18/19)

The row-wise enforcement of the earlier arc is replaced by an intrinsic **projection
trader**, `E_n(p) = λ_n (q(p) − p)` with `q = proj_K(p)`. `ProjectionForce` carries the
algebra with no market, trader or presentation in sight: the variational inequality and
four consequences. `ProjectionMarket` licenses choosing the comparison point after the
price, by extending the market maker's contract from the cube's vertices to the cube.
`ProjectionCalibrated` fixes the intensity at `λ_n = ρ_n/δ_n²` with `ρ_n = ε_n + A_n`, at
which — and only at which — the day charge is `(ρ_n/δ_n)·d₂`. `ProjectionCore` adds the
`α`-homothetic-core refinement, whose liability bound is independent of `δ_n`; a positive
core does **not** by itself bound cumulative liability, and nothing here claims it does.

`RationalPolytope`, `PolyhedralProjection` and `PolyhedralCoverage` present the region by
its vertices rather than its facets. That is a deliberate call: the deductive region
arrives as a vertex list, so no facet enumeration is needed, and the nearest-point
certificate reduces to the vertices by convexity, so no Farkas lemma is needed.
`PolyhedralCoverage` establishes a **cover** only — not disjoint interiors, not normal
cones, not full-dimensionality — which is exactly what `IsPiecewiseAffineOn` asks.

`MaxMinRepresentation` is Ovchinnikov's Theorem 4.1, with an errata witness for the
uniqueness gap in the source's Definition 2.1. `maxMin_of_family` restates 4.1(a) with the
index family *supplied*, because the original builds it as a filter over an existential on
an infinite domain and no algorithm can evaluate that.

`FourierMotzkin` decides rational linear feasibility, `feasible_iff` in both directions,
with `≤` and `<` kept distinct — the strict form is load-bearing, since `λ_j > 0` is what
separates a support from a face containing it. `feasible_primrec₂` is uniform in the
dimension, which the fixed-dimension form is not and which the compiler needs.

`ProjectorGenerator` is the executable generator. Its system is linear because introducing
the barycentric weights together with **one auxiliary scalar** `c := ⟪x − q, q⟫` cancels
both quadratic terms at once; `c` is a free variable of the system and is *forced* rather
than assumed, which `cOf_eq_of_holds` proves by summing the support's residual equations
against the weights. The construction is **doubly exponential in the fragment dimension**
and no better bound is claimed.

`EffectiveRepresentation` writes the whole pipeline a second time over raw, proof-free,
non-dependent data. This was necessary because `projectorRep` takes a `Fragment` and a
dependently-indexed `RationalPolytope`, neither of which is `Primcodable`: the obstruction
was never that the generator is ineffective, but that its *type* is not one a computability
statement can mention.

`DeductiveRegion`, `DeductiveSchedule` and `DeductiveEffective` specialise to deductive
coherence. The pass's last question was whether an extra effective-stage hypothesis is
needed, since `DeductiveProcessComputation` gives a partial recursive program that merely
*eventually* emits the stage, not `Primrec DP.D`. It is not. The compiler already carries
the stage table as finite data — `decodedStageTable stages n = stages.getD n ∅` — and the
source's own Trading Firm reads it that way; letting the enforcer's trade map and the
schedule's representation read the day's stage too removes the need entirely.
`deductive_end_to_end` therefore assumes nothing about the deductive process beyond the
pinned source's own certificate.

Upstream, `LIACompiler` gained a purely additive public section: twenty exported
declarations, none of which changes an existing one, stated in the already-public
`Sentence.atoms` / `sentenceBool` / `tableConsistent` / `supportSentenceList` vocabulary so
that no caller has to rebuild the strong-recursion tower over the formula encoding.

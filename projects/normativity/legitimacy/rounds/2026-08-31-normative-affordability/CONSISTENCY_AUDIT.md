# Consistency audit of the round

Every claim this round has withdrawn, where it was withdrawn, and the state of its
surviving mentions. A claim is **clear** when no document asserts it and the
documents that once did carry an explicit withdrawal.

| withdrawn claim | withdrawn in | status |
|---|---|---|
| contiguity is derived from the transport theorem | `SERVICE_TRANSFER.md` §4 | clear; the two routes are declared incomparable |
| per-reason Uptake is free from the criterion's quantifier | `FOLLOWUP_REPORT.md` | clear; replaced by the MarketMaker cumulative cap |
| the criterion's preservation theorem is Uptake | `FOLLOWUP_REPORT.md` | clear; it is substrate preservation |
| pointwise self-financing is necessary for persistence | `FOLLOWUP_REPORT.md` §C | clear; alternating-norm counterexample |
| the sustainable authority-rate region is convex by time-sharing | `CAUSAL_CAPACITY.md` §1 | clear; and the object itself is withdrawn, since the rate region reports zero where persistence holds |
| the rate region is non-convex wherever non-degenerate | `CAUSAL_CAPACITY.md` §3 | clear; narrowed to the finite-horizon cumulative-authority frontier |
| the sharp criterion is exclusion depth alone dipping | `SHARP_PERSISTENCE.md` §3, Lemma S3 | clear; the criterion is `liminf L_t(1) = 0`, comparable to `min(D^2, D sqrt(m))` within four, and the depth-only reading holds under a floor on `m_t` |
| the online scheduler is factor-four competitive | `ONLINE_EXISTENCE.md` | clear; two dates cap any rule at a quarter |
| D1/D3 hold under mere star-shapedness | `BOUNDED_DELAY_AFFORDABILITY.md` §2, hypothesis table | clear; D1 needs concavity, D2/D3 additionally equal claim masses, both with exact counterexamples |
| bounded-delay cost interpolates to persistence as `H -> infinity` | `BOUNDED_DELAY_AFFORDABILITY.md` §6, `EVENTUAL_VS_UNIFORM_SERVICE.md` §1 | clear |
| eventual full service is strictly stronger than persistence | `EVENTUAL_VS_UNIFORM_SERVICE.md` §2, Theorem EV1 | clear; the two are equivalent as existence questions under EV1's hypotheses, and the old E2 is reproduced with its error named |
| positive density of cheap dates implies bounded gaps | `EVENTUAL_VS_UNIFORM_SERVICE.md` §4 | clear |
| bounded gaps imply finite timely-service cost | `EVENTUAL_VS_UNIFORM_SERVICE.md` §4, Countermodel E3 | clear; the only criterion is D4's sliding-window sum |
| `F_r` is a property of the norm, scheduler-independent | `SERVICEABILITY_FRONTIER.md` §3, `JOINT_SERVICEABILITY.md` §1 | clear; it is the misfit landscape read against the chosen service measure |
| the transport residual is the raw sum `sum T eps` | `SERVICE_TRANSFER.md` T3, `JOINT_SERVICEABILITY.md` §1 | clear; the normalized `epsbar_N(T)` replaces it, and `SERVICE_ADMISSIBLE_EXISTENCE.md`'s finite-horizon LP records why its unnormalized objective has the same argmin |
| every Pareto point is recovered by scalarization | `JOINT_SERVICEABILITY.md` JS2 | repaired rather than withdrawn: it is *true* under fractional splitting, because both objectives are linear on the transportation polytope; without fractional splitting only the supported frontier is recovered |
| every form of overload is liability overload | `OVERLOAD_TARGET.md` §2 | clear; conditioned on force feasibility, with an empty region, an unpriceable row or an illegal compiled control failing earlier |
| separate reason underwriting is necessary | `MULTIREASON_SERVICEABILITY.md` M1, `JOINT_SERVICEABILITY.md` §5 | clear; the additive test is sufficient and the true joint cost is subadditive |
| SS1 holds without a nestedness hypothesis on the live sets | `SHARP_SERVICEABILITY.md` SS1 | clear; hypothesis (N) `A_N subseteq A_t` is stated and its necessity explained |
| the square-root branch fails "only when `m_t` is not summable" | `SHARP_SERVICEABILITY.md` §3 | clear; the exact condition is `(1/A_N) sum (l_t + m_t)^2 / m_t -> 0`, and summability is neither necessary nor sufficient |

Two things this table is not. It is not a claim that no error remains — every entry
here was found by a reader and not by the author, and the rate has not fallen. And
it is not a record of *retreat*: eight of the twenty entries were replaced by exact
theorems rather than by silence, and three of those — EV1, the sharp persistence
criterion, and the sliding-window cost formula — are the strongest results the round
has.

## The pattern in the errors

Almost every entry is one of three moves:

1. **Pricing one plan and reading it as the minimum.** The withdrawn countermodel of
   `EVENTUAL_VS_UNIFORM_SERVICE.md`, whose block-batching cost was read as the
   optimum, and the factor-four online claim.
2. **Promoting a sufficient condition to a necessary one.** Self-financing, separate
   underwriting, bounded gaps, summable `m_t`.
3. **Losing a quantifier or a normalization in compression.** SS1's two live-world
   sets, the raw transport sum, D1 under star-shapedness, the depth-only criterion.

The third is the one the round should watch, because it is produced by the very act
of writing a slogan, and the slogans are what get carried into later work.

# Projection enforcement

Whether presentation-dependent row enforcement can be replaced by an intrinsic
projection trader that holds `λ(proj_K(P) − P)` — and if so, what that does to the
paper *Generalizing and Strengthening Logical Induction*.

The round was allowed to kill the idea. It does not.

Verdict: The intrinsic projection trader is the paper's construction, the market is computable, the representation the construction needs is generated rather than assumed, and the deductive specialization closes from the source's own assumptions: force, the calibrated budget with no free intensity, the homothetic-core refinement that removes the tolerance penalty, and the deductive end-to-end theorem are kernel-checked; ComputableMarket is gone as a premise and the bounded-evaluator compiler that replaced it is built, against a purely additive upstream public section of twenty exported declarations; the paper-facing input is a schedule of rational convex constraints from which the region predicate, the target and its nearest-point property are all derived, and against which finite-time conformance and the criterion hold with no hypotheses whatever; rational linear feasibility is decided and verified with strict and non-strict constraints kept distinct and uniformly in the dimension, which drives an executable generator for the projector's max-min representation; and deductive_end_to_end yields source-original IsLogicalInductor together with every-date conformance to the day's deductive region from a computable fragment schedule, a computable positive tolerance schedule, propositional satisfiability of each stage, and the source's own DeductiveProcessComputation and nothing more -- the extra effective-stage hypothesis that appeared necessary was an artifact of two interfaces indexing by the date, since the compiler already carries the stage table as finite data and the source's own Trading Firm reads it that way. The generator is doubly exponential in the fragment dimension and no better bound is claimed.

## What is here

| file | what it is |
| --- | --- |
| `DECISION_MEMO.md` | the deliverable to read first: every question graded proved / proved-conditional-on-a-named-theorem / likely-but-unresolved / false |
| `PAPER_CLOSURE.md` | the recommended theorem chain, what strengthens, what stays conditional, the calibrated budget, and the re-check of the whole chain |
| `PAPER_AUDIT.md` | the rest of the paper, split by how much it costs to leave alone, plus notation |
| `COMPARISON.md` | projection against rows, including the identity that makes rows the single-halfspace case |
| `COMPUTABILITY.md` | what has to be computable, what it costs, and the exact state of Debt B |
| `THEOREM_MAP.md` | paper statement ↔ Lean declaration, and the Python tests |
| `src/`, `tests/` | exact rational projection and twelve `Fraction`-exact regression tests |

Lean, all in `lean/Workspace/Normativity/Contrib/`:
`ProjectionForce`, `ProjectionMarket`, `ProjectionCompiler`, `ProjectionBudget`,
`ProjectionCalibrated`, `ProjectionCore`, `EnforcedComputation`, `ProjectionEnforcer`,
`EnforcedCompiler`.

## The theorem of record

`EnforcedCompiler.ProjectionSchedule.end_to_end_effective`. From a computable deductive
process, a fragment schedule, a positive rational tolerance schedule, a finite
representation of each day's projector, and the schedule's effectiveness — **no
`ComputableMarket` premise and no compiler object**:

* the market is a logical inductor **in the source's original sense** — `IsLogicalInductor`,
  not the generalized criterion;
* at every date `d₂(P_n|_{Φ_n}, K_n) ≤ δ_n`;
* and there is an admitted price vector agreeing with the displayed one to within `δ_n` on
  every sentence of `Φ_n`.

`eventual_coherence` adds the paper's closing consequence: for a fixed finite set of
sentences and any slack, from some date on the displayed prices agree with an admitted
vector to within that slack.

## The five things that had to be true

1. **The force inequality needs only the variational inequality.** No separation theorem,
   no duality, no net, no presentation. `ProjectionForce.force_inequality`.

2. **The comparison point may be chosen after the price is displayed.** The dangerous
   circularity: `q = proj_K(P)` does not exist until `P` does, and the market maker's
   contract is stated at worlds. A strategy's value is affine in the assessment point and
   the cube is the convex hull of the `{0,1}` assignments on the traded support, so the
   contract extends from the vertices to the cube.
   `ProjectionMarket.marketMaker_day_value_le_cube`.

3. **The external opposition bound `M_n` is not needed.** `Strategy.tradeListAbsBound` is
   a computable syntactic majorant in the pinned source, so `ρ_n = ε_n + A_n` and the
   calibrated `λ_n = ρ_n/δ_n²` buys `d₂ ≤ δ_n`.
   `ProjectionCalibrated.dist2_le_of_calibrated`.

4. **The paper's `ℓ∞` conclusion follows from the Euclidean one at the same `δ`.**
   `ProjectionForce.sup_conformance_of_dist2`. This is what takes the exact dual-distance
   presentation off the critical path.

5. **The market is computable without assuming it.** The enforcer is finite data; the
   modified recurrence is the source's own architecture with one extra trade list; and the
   bounded evaluator that closes it is built, not assumed.
   `EnforcedCompiler.computableMarket`, `EnforcedCompiler.isLogicalInductor`.

## What is not unconditional

* **The representation.** That each coordinate of `p ↦ proj_K(p)` has a max–min
  representation over rational affine forms, and that one is obtainable from a rational
  description of the region. Ovchinnikov's Theorem 4.1(a) (2002) gives the first, and its
  exact statement has been read and matched to the use rather than assumed from folklore;
  the piecewise affinity of the polyhedral projector is the standard active-set argument,
  written out in `COMPUTABILITY.md §1`. The Lean takes the representation as **data** and
  its correctness as a **hypothesis** — not an axiom, not a `sorry`.
* **`Primrec₂` for the projection schedule's trade map.** The general theorem is
  unconditional for any effective enforcer; establishing effectiveness for *this* enforcer
  is mechanical and bounded. `COMPUTABILITY.md §7` says what it needs. The upstream
  visibility block that used to sit here is gone: the dependency is pinned to a revision
  that re-exports the three lemmas, purely additively.

## The preservation hierarchy

Four levels, a continuum from an arbitrary convex constraint to the deductive case:
the abstract bounded-downside criterion; the generic charge `(ρ_n/δ_n)·d₂(w, K_n)`; the
**homothetic-core** refinement `((1−α_n)/α_n)·ρ_n` **with no tolerance penalty**
(`ProjectionCore.core_day_value_ge`); and zero liability when every live restriction is
admitted, which is the `α = 1` case. `μ(φ) ≥ 1/2` has a `1/2`-core against `P = [0,1]`;
`μ(φ) = 1/2` has none.

## Two negative results

* **Admission at the last date does not bound the budget.**
  `ProjectionBudget.late_admission_is_not_enough` exhibits one priced atom, a day-`0`
  region excluding the assessed world, a day-`1` region admitting everything, every other
  hypothesis satisfied, and cumulative value `−1/4`. So the zero-risk-capital theorem must
  carry `∀ k ≤ n`.

* **Row presentations are not intrinsic, on displayed data.** Rescaling every normal by
  `1/N` leaves the region alone and drives the maximal violation to zero, so no
  presentation-independent constant turns violations into distance. The operational cost
  is a factor `N²` in the intensity, which is paid in risk capital.

## One correction to this round's own earlier record

An earlier `PAPER_CLOSURE.md` wrote the day charge as `λ_kδ_k d₂(·) = (ρ_k/δ_k) d₂(·)`
under the hypothesis `λ_k ≥ ρ_k/δ_k²`. That equality is false under a lower bound; it
holds exactly at the calibrated value. `ProjectionCalibrated.calibratedIntensity_mul` is
the statement and `PAPER_CLOSURE.md §4` records the correction. The general free-`λ`
theorem is retained unweakened.

## What is not deleted

Nothing from the row arc. `EnforcementStrategy`, `EnforcementPreservation`,
`DeductiveEnforcement`, `CoherenceModulus` and `IntrinsicCoherence` are untouched, and no
theorem about them is weakened. The projection route *reuses* `DeductiveEnforcement`'s
preservation chain unchanged, because that chain was already generic in the added trader.
For a single halfspace the two constructions are the same trader.

## What this round did not do

It did not rewrite the paper. `PAPER_AUDIT.md` says what a rewrite has to fix, in order,
and flags the two items that close gaps rather than strengthen results: §6.4's contract
hypothesis is never discharged where §10.6 instantiates it, and §8.1 needs the per-date
quantifier.

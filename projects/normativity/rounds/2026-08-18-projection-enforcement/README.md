# Projection enforcement

Whether presentation-dependent row enforcement can be replaced by an intrinsic
projection trader that holds `λ(proj_K(P) − P)` — and if so, what that does to the
paper *Generalizing and Strengthening Logical Induction*.

The round was allowed to kill the idea. It does not.

Verdict: The intrinsic projection trader is the paper's construction — force, the calibrated budget with no free intensity, the per-date quantifiers and the deductive end-to-end theorem are kernel-checked; the ComputableMarket premise is gone, reduced to the same bounded-evaluator boundary the source isolates for ordinary LIA and blocked only by three private lemmas upstream; expressibility rests on a cited representation theorem rather than an axiom; and the paper's ℓ∞ conclusion follows from the Euclidean one at the same tolerance, which takes Debt A off the critical path.

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
`ProjectionCalibrated`, `EnforcedComputation`, `ProjectionEnforcer`.

## The theorem of record

`ProjectionEnforcer.ProjectionSchedule.end_to_end`. From a computable deductive process, a
fragment schedule, a positive rational tolerance schedule, a finite representation of each
day's projector, and one bounded-evaluator compiler:

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
   remaining obligation is the boundary the source itself isolates.
   `EnforcedComputation.EnforcedBoundedEvaluatorCompiler.toComputableMarket`.

## What is not unconditional

* **The representation.** That each coordinate of `p ↦ proj_K(p)` has a max–min
  representation over rational affine forms, and that one is obtainable from a rational
  description of the region. Ovchinnikov's Theorem 4.1(a) (2002) gives the first, and its
  exact statement has been read and matched to the use rather than assumed from folklore;
  the piecewise affinity of the polyhedral projector is the standard active-set argument,
  written out in `COMPUTABILITY.md §1`. The Lean takes the representation as **data** and
  its correctness as a **hypothesis** — not an axiom, not a `sorry`.
* **The bounded-evaluator compiler.** Blocked on three `private` lemmas in the pinned
  dependency's `LIACompiler.lean`. Module visibility and assembly, not mathematics;
  `COMPUTABILITY.md §7` carries the exact upstream ask.

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

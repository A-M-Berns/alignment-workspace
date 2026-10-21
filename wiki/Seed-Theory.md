# Seed Theory

The normative seed is the left-most object of the [Normative Record and Inquiry](Normative-Record-and-Inquiry)
picture made concrete: what a reasoner starts from, what it forces on the prices of a settled
fragment, how that changes as settlement, defeat and rebuttal arrive, and whether two
reasoners starting from different seeds end up anywhere together. This page says what the
seed is and what is proved about it; the statements of record are the Lean declarations
named, and the claims registry governs what is registered.

## The seed

A **seed** has three layers. The **substantive** layer is a list of leverage forms, each
carrying a strength `c ∈ (0,1)` and a docket **port**: `premise X c` says `P(X) ≥ c`;
`applicability X XA c` says `P(X∧A) ≥ c·P(X)`; `strength XA XAY c` says
`P(X∧A∧Y) ≥ c·P(X∧A)`. A warrant "`X∧A` makes `Y` likely" is the chain of the three. The
**structural** layer is raw rows of strength one — coherence, dominance, impartiality — with a
surface id. The **constitutive** layer is declared data: the standing set and the protected
coordinates; nothing in the statics computes from it. Two withdrawal channels are deliberately
separate: a docket defeat reaches only substantive items, a surface change only structural
ones (`Seed.liveStr_indep_defeat`, `Seed.liveSub_indep_withdraw`).

A seed is **humble** when every strength lies strictly inside `(0,1)` (`Seed.HumbleItems`): a
humble seed never asserts a logical fact.

## The statics

**The forced region.** On a fragment with some coordinates settled, the live items and the
live warrants compile — through the rational-row compiler the force layer already consumes —
to a bundle of cited rows, and the forced region is that bundle's region intersected with the
settlement's pins (`forcedBundle`, `forcedRegion`, read off by `forcedRegion_iff`). Membership
is decided by the compiler's own `checkCompiled` (`forcedRegion_iff_check`).

**The forced interval** of a coordinate is computed, not postulated: rows become linear
constraints, Fourier–Motzkin elimination removes every other coordinate, and the endpoints of
the one-dimensional system are valid bounds, attained over the reals
(`forcedInterval`, `forcedInterval_spec`, `forcedInterval_bounds`; **registered** against item 39
as `seed.forced-interval-spec`, `seed.forced-interval-bounds`). Rational attainment — that the
computed endpoint is reached at a rational point — is open (item 118).

**Monotonicity.** With the row set fixed, more settlement means a smaller region and nested
intervals (`forcedRegion_anti`, `IsForcedInterval.mono`, `forcedInterval_mono`); defeat widens
(`defeat_widens`). Both statements are about the *unspecialized-row* region and remain true.

**Certificates.** A lower or upper bound on a coordinate is certified by nonnegative
multipliers on allowed rows (`BoundCert`, `lowerCert_bound`, `upperCert_bound`); an empty
region is certified by a Farkas certificate (`SureLoss`, `sureLoss_of_cert`), whose positively
weighted rows already suffice (`FarkasCert.support_sound`).

**Seed-independence.** Humility read item by item does *not* make the pinned fragment
seed-independent: two strengths of one half pin a coordinate (`c3_refuted`). Read strictly —
substantive rows as open half-spaces — it does: a point forced by a closed convex layer cut by
an open layer is forced by the closed layer alone (`point_forced_of_open_layer`,
`seed_independence_strict`; **registered** against item 117 as `seed.independence-strict`). A
humble seed narrows or breaks and never pins.

## Rebuttal by settlement

A linear strength row contraposes: once `X∧A∧Y` is settled false, `P(X∧A∧Y) ≥ c·P(X∧A)` says
`P(X∧A) = 0`. A defeasible warrant said no such thing, and the [warrant round](https://github.com/A-M-Berns/alignment-workspace/blob/2f6e5e5ca9bf96fdb6dd5d467e0c3fff558c36b3/projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/COUNTERMODELS.md)
showed a market paying without bound for the difference. The rule (`DECISIONS.md`,
2026-10-21) acts on the form, which knows its antecedent and consequent: a form whose
consequent is pinned false is **rebutted**, whose antecedent is pinned false is **vacuous**, a
premise whose sentence is pinned false **retires** its occurrence — and in every case the row
leaves (`settleForm`). It keeps exactly the specialized rows of the non-degenerate forms
(`settleForm_eq_some_iff`; **registered** against item 113 as `rebuttal.settleform-sound`), and
the rows it removes are exactly the contraposing ones (`strength_contraposes`). A rebuttal does
not discount the applicability claim: undercut attacks applicability, rebuttal the conclusion.

Under the rule the orphan cannot form, a slack world survives the refutation, and the
enforcer's assessed net worth across the rebuttal is at least `−3ρ(2 + ρ)`
(`Fixture.liability_rebutted`; **registered** as `rebuttal.liability-rebutted`): the odds
bankroll `3ρ` before the reopening, plus `ρ` times a post-reopening slack mass the market's
capital bounds by `3 + 3ρ`. The smaller constant `3ρ` does not survive the reopening: a
counterparty's gains on the rebutted row cushion its later selling (an exact exhibit, item 123).

**Monotonicity, restated.** Settlement can now widen an interval. Without a reopening (no
form rebutted, vacuous or retired) the settled region shrinks as before
(`settledRegion_anti_of_survivors_eq`); across a reopening both the old and the new settled
regions lie inside the region the *kept* rows forced at the pre-step settlement
(`settledRegion_subset_kept`, `reopening_bound`), so an interval widens by at most what the
removed rows had been forcing. The widening is a reopening in the sense of the convergence
profile, and summable reopenings converge (`tendsto_of_summable_drops`).

## Dynamics

**Stabilization.** Along a chain in which a finite discovery class is raised monotonically and
settlement grows monotonically, every quantity computed from the two — the forced interval of
any coordinate — is eventually constant (`eventually_const_of_finite`; **registered** as
`seed.eventually-const`). On an infinite class a fresh warrant and an undercut can alternate
forever; a sequence bounded above whose downward steps are summable converges
(`tendsto_of_summable_drops`).

**The convergence profile.** For finitely many reasoners, each with a forced interval per
coordinate (`IntervalData`), the hull of the intervals, their common part and their
**discord** (an empty common part) give the three masses `Hull`, `Ovl`, `Disc` over a declared
fragment with declared positive weights. Under any nesting — settlement, shared or private
narrowing — hull and overlap fall and discord persists (`hullMass_anti`, `discord_persists`;
**registered** against item 119 as `convergence.hull-mass-anti`,
`convergence.discord-persists`); reopening raises the hull (`hullMass_mono`). Discord is
pairwise, Helly in dimension one (`discord_iff_pair`; **registered** as
`convergence.discord-pairwise`) — and that is exactly why merged infeasibility can hide from
it (item 119). `Disc = 0 → Ovl > 0` is false on touching intervals (`touching_refutes`).

## The first end-to-end run

One fixture, every stage, in sequence: a seed of one warrant and a coherence row, a second
warrant on a disjoint sentence, licences at entry, intervals by elimination, `X` settles (the
intervals nest), the applicability port is undercut (the interval widens, the certificate
citing it fails), `Y` is refuted (the strength row is rebutted, `X∧A` keeps its interval where
the old rule pinned it to `0`, the second warrant is untouched), the enforcer's bankroll and
the conditional Normative Inductor compose, and the record of the run is neither injective
nor constant and carries the docket. `EndToEndWitness.Run.witness` is the conjunction; the
[witness table](https://github.com/A-M-Berns/alignment-workspace/blob/2f6e5e5ca9bf96fdb6dd5d467e0c3fff558c36b3/projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/WITNESS.md)
has the run date by date. It is the object item 35 asked for and is not registered.

## Where the seed sits

The seed is what the [Normative Inductor](Normative-Inductor)'s compiler reads on its left:
`settleForm` and the docket give the surviving rows, the elimination gives the intervals, the
bridge `toForceRow` gives the force layer its presentation, and the odds bankroll is what the
[Theorem Spine](Theorem-Spine)'s conditional Normative Inductor consumes as its liability
hypothesis. What the seed does not yet have: a canonical selection rule for strengths and a
lock the docket can carry (item 117), rational attainment and certificate completeness (item
118), a region-level discord measure (item 119), and the exchange protocol that equalizes live
sets (item 120).

## Sources

- [`SeedStatics.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/2f6e5e5ca9bf96fdb6dd5d467e0c3fff558c36b3/lean/Workspace/Normativity/Contrib/SeedStatics.lean),
  [`ConvergenceMeasure.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/2f6e5e5ca9bf96fdb6dd5d467e0c3fff558c36b3/lean/Workspace/Normativity/Contrib/ConvergenceMeasure.lean),
  [`WarrantEntitlement.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/2f6e5e5ca9bf96fdb6dd5d467e0c3fff558c36b3/lean/Workspace/Normativity/Contrib/WarrantEntitlement.lean),
  [`EndToEndWitness.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/2f6e5e5ca9bf96fdb6dd5d467e0c3fff558c36b3/lean/Workspace/Normativity/Contrib/EndToEndWitness.lean).
- The seed-statics round, [`SEED.md`](https://github.com/A-M-Berns/alignment-workspace/blob/2f6e5e5ca9bf96fdb6dd5d467e0c3fff558c36b3/projects/normativity/seed/rounds/2026-09-16-seed-statics/SEED.md)
  and [`STATICS.md`](https://github.com/A-M-Berns/alignment-workspace/blob/2f6e5e5ca9bf96fdb6dd5d467e0c3fff558c36b3/projects/normativity/seed/rounds/2026-09-16-seed-statics/STATICS.md);
  the convergence round, [`MEASURE.md`](https://github.com/A-M-Berns/alignment-workspace/blob/2f6e5e5ca9bf96fdb6dd5d467e0c3fff558c36b3/projects/normativity/seed/rounds/2026-09-17-convergence-measure/MEASURE.md).
- The rebuttal round, [`REBUTTAL.md`](https://github.com/A-M-Berns/alignment-workspace/blob/2f6e5e5ca9bf96fdb6dd5d467e0c3fff558c36b3/projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/REBUTTAL.md)
  and [`LANDING.md`](https://github.com/A-M-Berns/alignment-workspace/blob/2f6e5e5ca9bf96fdb6dd5d467e0c3fff558c36b3/projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/LANDING.md).

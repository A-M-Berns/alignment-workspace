# Part B — the seed and convergence landing

Sources: `round/2026-09-16-seed-statics` (head `39ac06b8`, PR #102) and
`round/2026-09-17-convergence-measure` (head `aa6756cc`, PR #103, based on the seed branch and
carrying its files unchanged). Both 96 commits behind `main` at `dcb2cded`; neither merged.
Ported, not merged (M6). The two pull requests are superseded by this landing and are the
maintainer's to close with a pointer here.

## B1. One `SeedStatics.lean`

`lean/Workspace/Normativity/Contrib/SeedStatics.lean` (133 declarations audited). The
declarations the warrant round had copied into `WarrantEntitlement.lean` are removed from it;
`WarrantEntitlement.lean` imports and opens `SeedStatics`. The branch's `FourierMotzkin.lean`
and `NormativeInductorComposition.lean` are byte-identical to `main`'s, and every ported
section compiled on the first build.

| branch section | landed | why / what |
|---|---|---|
| §1 settlement and specialization | **yes** | consumed by Part A |
| §2 the seed, forms, items, docket | **yes** | with `DecidableEq` on `Form`, `SubItem`, `DocketState`, `Cite`, and `Form.applicability_sat_iff`, `strength_sat_iff` (from the warrant round) |
| §3 the forced region | **yes** | with a `Decidable` instance for `forcedRegion` |
| §4 monotonicity and defeat; `Pins`, `Refuted`, `leverage` | **yes** | `IsForcedInterval.mono` kept as stated (true of the unspecialized-row region; A4) |
| §5 certificates: `BoundCert`, `lowerCert_bound`, `upperCert_bound`, `SureLoss`, `sureLoss_of_cert`, `FarkasCert.support_sound`, `MinimalInfeasible` | **yes** | with `BoundCert.sound_of_pos`; `Settlement.empty_pinRowsAt` added |
| §6 elimination: `forcedRegionR`, `toLinCon`, `system`, `project`, `project_sat_iff`, `lo1`/`hi1`, `sat1_iff`, `endpoints_attained`, `forcedInterval`, `forcedInterval_spec`, `forcedInterval_bounds`, `forcedInterval_mono` | **yes** | the end-to-end witness's intervals go through `forcedInterval_spec` |
| §7 confinement: `confinement`, `confinement_forced`, `Seed.merge`, `forcedRegion_merge`, `confinement_common`, `measure_form_refuted` | **no** | excluded by the dispatch |
| §8 seed-independence: `negCoherence`, `sandwichSeed`, `emptySeed`, `sandwichSeed_humble`, `c3_refuted`, `StrictSatR`, `isOpen_strictLayer`, `regionR_convex`, `point_forced_of_open_layer`, `seed_independence_strict` | **yes** | |
| §9 transport: `transport`, `transport_sat_iff` | **no** | excluded; its negated-form drop (the convergence round's `transport_seed` "drops negated forms", `REPORT.md` §108 of that round) is filed as item 122, not fixed |
| §10 stabilization: `eventually_const_of_monotone`, `eventually_const_of_finite`, `tendsto_of_summable_drops` | **yes** | |
| §11 non-dogmatism: `Seed.structural`, `LevelNeutral`, `disguisedSeed`, `disguise_caught`, `emptySeed_levelNeutral`, `Seed.Humble`, `emptySeed_humble` | **no** | excluded |

## B3. `ConvergenceMeasure.lean`

`lean/Workspace/Normativity/Contrib/ConvergenceMeasure.lean` (55 declarations audited),
importing `SeedStatics` unchanged.

| branch section | landed |
|---|---|
| §1 interval data and the three masses: `IntervalData`, `Valid`, `hullLo/Hi/Width`, `commonLo/Hi/Width`, `Discord`, `Weights`, `hullMass`, `overlapMass`, `discordMass`, their bounds, `discordMass_eq_zero_iff`, `discordMass_pos`, `touching_refutes` | **yes** |
| §2 blocked hull mass: `hullSum`, `unpinned`, `naiveHull`, `blockedHull`, `naiveHull_insert_pinned_le`, `blockedHull_insert_pinned` | **yes** |
| §3 dynamics: `Nested`, `Nested.refl`, `Nested.ofPrivate`, the four monotonicity lemmas, `discord_persists`, `hullMass_anti`, `overlapMass_anti`, `hullMass_mono`, `discordMass_mono`, `discord_iff_pair` | **yes** |
| §4 region level: `forcedRegionR_anti_warrants`, `forcedRegionR_anti_defeat`, `forcedInterval_nest_of_subset` | **yes** (cheap; the dispatch asked for the first) |
| §5 the discord certificate: `mergeCert`, `allowed_append_*`, `region_append_iff`, `discord_certificate` | **no** — outside B3's scope; item 119 (hidden discord) is where it would be consumed |
| §6 convergence: `tendsto_of_summable_rises`, `hullLo_le_one`, `hullHi_nonneg`, `hullMass_tendsto_of_summable`, `hullMass_tendsto_of_summable_rises` | **no** — outside B3; P2's account uses the seed round's `tendsto_of_summable_drops`, which is landed |
| §7 the pinned fragment: `pinned_lift` | **no** — outside B3 |

## B2. The seed subproject

`projects/normativity/seed/` with `README.md` (new, one paragraph), and the two branch rounds
landed verbatim under `rounds/2026-09-16-seed-statics/` and
`rounds/2026-09-17-convergence-measure/`, each with an `ORIGIN.md` saying it is a branch round
landed by this one and which of its cited declarations are not on `main`. Their `prompts/`
entries (`PROMPT.md`, `REPORT.md`) are landed verbatim. Their runners run in the repository
runner: 28 and 20 checks, green. `state/projects.json` gains the subproject `normativity.seed`
(parent `normativity`), and `state/rounds.json` the two rounds' records with their branch
verdicts, so `checkers.workspace_state --check` sees the subproject and the rounds.

Not landed from the branches: their `DECISIONS.md` entries (2026-09-16: humility read three
ways, the defeat calculus as a trace discipline; 2026-09-17: convergence as a profile,
exhaustive sharing as equal live sets) — they are the branch rounds' agent-decided readings
and are cited from the landed documents, not from the ledger; landing them is the
maintainer's call at the next consolidation. Their `CLAIMS.md` registered nothing.

## B4. The items, re-filed

| branch item | branch title | re-filed on `main` as |
|---|---|---|
| 93 (seed-statics) | the selection lock: a canonical joint rule and a sealed selection | **117** |
| 94 (seed-statics) | rational attainment and certificate completeness for the computed forced interval | **118** |
| 95 (convergence) | hidden discord: a region-level convergence measure | **119** |
| 96 (convergence) | exhaustive sharing on trace-constitutive dockets | **120** |

Content unchanged; each carries one line naming its branch number. The branch's 93 collided
with `main`'s 93 (filed by PR #101); the branch's is the one re-filed.

## What the next instance of item 35 needs from the unlanded material

The confinement theorem (§7) is what a *two-reasoner* end-to-end run would report alongside
the hull mass; the discord certificate (ConvergenceMeasure §5) is what turns a persistent
discord into a `FarkasCert`; the convergence of hull mass (§6) is P2's sequence statement at
the limit. The transport (§9) is needed only when the fragment changes between dates, which
the first instance avoided. Non-dogmatism (§11) is a seed-construction check, not a run
stage.

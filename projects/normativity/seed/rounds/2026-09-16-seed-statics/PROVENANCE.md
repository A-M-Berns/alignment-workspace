# Provenance

| File / glob | Generator | Review status | Date | Originating round |
|---|---|---|---|---|
| `README.md`, `REPORT.md`, `SEED.md`, `STATICS.md`, `CONFINEMENT.md`, `STABILIZATION.md`, `CRITERION.md`, `COUNTERMODELS.md`, `FIXTURES.md`, `ALIGNMENT_READING.md`, `PROVENANCE.md` | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-09-16 | `prompts/2026-09-16-seed-statics/` |
| `src/*.py`, `tests/*.py` | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-09-16 | `prompts/2026-09-16-seed-statics/` |
| `lean/Workspace/Normativity/Contrib/SeedStatics.lean` | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-09-16 | `prompts/2026-09-16-seed-statics/` |
| `prompts/2026-09-16-seed-statics/PROMPT.md` | the maintainer, relayed verbatim | `ci-only` | 2026-09-16 | `prompts/2026-09-16-seed-statics/` |
| `prompts/2026-09-16-seed-statics/REPORT.md` | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-09-16 | `prompts/2026-09-16-seed-statics/` |

## Lean declarations

All in `Workspace.Normativity.Contrib.SeedStatics`; every `#print axioms` reports
`[propext, Classical.choice, Quot.sound]` or fewer.  Status: **unregistered**; names
provisional.  "Witness" marks a fixture-level declaration.

| declaration | kind | status |
|---|---|---|
| `truth`, `Settlement`, `Settlement.Pinned`, `Settlement.le`, `Settlement.empty`, `Settlement.pinRowsAt`, `Settlement.pinRows`, `settledTerm`, `specialize` | definitions | — |
| `Settlement.empty_pinned`, `Settlement.le_refl`, `Settlement.Pinned.mono`, `Settlement.pinRowsAt_sat_iff`, `Settlement.pinRows_sat_iff` | lemmas | proved |
| `specialize_sat_iff` | theorem (specialization exact on the pinned slice) | proved |
| `Form`, `Form.c`, `Form.row`, `SubItem`, `StrKind`, `StrItem`, `Constitutive`, `Seed`, `Seed.HumbleItems` (+ `Decidable`), `DocketState`, `DocketState.quiet`, `Seed.liveSub`, `Seed.liveStr` | definitions | — |
| `Form.premise_sat_iff` | lemma | proved |
| `Seed.liveStr_indep_defeat`, `Seed.liveSub_indep_withdraw` | theorems (two withdrawal channels) | proved (`rfl`) |
| `Cite`, `pinCited`, `forcedBundle`, `forcedRegion` | definitions | — |
| `forcedRegion_iff_check` | theorem (`checkCompiled` decides membership) | proved |
| `pinCited_sat_iff`, `forcedRegion_iff` | lemma, theorem | proved |
| `forcedRegion_anti` | theorem (monotonicity under settlement) | proved |
| `LowerBound`, `UpperBound`, `IsForcedInterval`, `Pins`, `Refuted`, `leverage` | definitions | — |
| `IsForcedInterval.le`, `IsForcedInterval.unique`, `IsForcedInterval.mono` | theorems | proved |
| `widenSeed`, `defeat_widens` | witness | proved |
| `allowed_sat` | lemma | proved |
| `BoundCert`, `BoundCert.value` | definitions | — |
| `BoundCert.sound`, `lowerCert_bound`, `upperCert_bound` | theorems | proved |
| `SureLoss`, `MinimalInfeasible` | definitions | — |
| `sureLoss_of_cert` | theorem | proved (wraps `conflict_sound`) |
| `FarkasCert.support_sound` | theorem (support is infeasible) | proved |
| `forcedRegionR`, `Settlement.PinnedR` | definitions | — |
| `sat_iff_satR`, `single_satR`, `forcedRegionR_of_forcedRegion`, `Settlement.pinRowsAt_satR_iff`, `pinCited_satR_iff`, `specialize_satR_iff`, `forcedRegionR_iff`, `Settlement.PinnedR.mono`, `forcedRegionR_anti` | real-form mirrors | proved |
| `pos`, `toLinCon`, `cubeRows`, `system`, `project`, `NonStrict`, `c0`, `lowerList`, `upperList`, `lo1`, `hi1`, `forcedInterval` | definitions (elimination) | — |
| `pos_zero`, `pos_self`, `pos_pos`, `toLinCon_coeff`, `toLinCon_coeff_ge`, `toLinCon_strict`, `toLinCon_const`, `cubeUpper_satR_iff`, `cubeLower_satR_iff`, `cubeRows_satR_iff`, `mem_elim_of_lastCoeff_zero`, `mem_project_of_zero`, `combine_strict`, `elim_nonStrict`, `project_nonStrict`, `eval_one`, `le_cast_foldr_max`, `cast_foldr_max_le`, `cast_foldr_min_le`, `le_cast_foldr_min`, `sat_one_iff`, `cube_phi_lastCoeff`, `cube_phi_lower_mem`, `cube_phi_upper_mem`, `system_nonStrict` | lemmas | proved |
| `toLinCon_sat_iff`, `system_sat_iff`, `project_sat_iff`, `sat1_iff`, `endpoints_attained` | theorems (elimination computes the projection; the one-dimensional system is an interval) | proved |
| `forcedInterval_spec` | theorem (computed endpoints valid and attained, real region nonempty) | proved |
| `forcedInterval_bounds`, `forcedInterval_mono` | theorems | proved |
| `confinement`, `confinement_forced` | theorems (C1, hull form) | proved |
| `Seed.merge`, `forcedRegion_merge`, `confinement_common` | definition, theorems | proved |
| `measure_form_refuted` | refutation (C1 measure form) | proved |
| `negCoherence`, `sandwichSeed`, `emptySeed`, `sandwichSeed_humble`, `c3_refuted` | witness (C3 under item humility) | proved |
| `StrictSatR`, `isOpen_strictLayer`, `regionR_convex` | definition, lemmas | proved |
| `point_forced_of_open_layer`, `seed_independence_strict` | theorems (C3′) | proved |
| `transport`, `transport_sat_iff` | definition, theorem | proved |
| `eventually_const_of_monotone`, `eventually_const_of_finite` | theorems (S1) | proved |
| `tendsto_of_summable_drops` | theorem (S2) | proved |
| `Seed.structural`, `Seed.LevelNeutral`, `disguisedSeed`, `Seed.Humble` | definitions | — |
| `disguise_caught`, `emptySeed_levelNeutral`, `emptySeed_humble` | witnesses | proved |

Not stated in Lean: rational attainment of the computed endpoints; LP duality
(tightness of bound certificates); the grounded extension; the reduction of S1 to
finitely many distinct rows; anything from `CRITERION.md`.

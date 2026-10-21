# Provenance

| File / glob | Generator | Review status | Date | Originating round |
|---|---|---|---|---|
| `README.md`, `REPORT.md`, `MEASURE.md`, `GAMEABILITY.md`, `DYNAMICS.md`, `MANY.md`, `CONSENSUS.md`, `LI_COMPARISON.md`, `COUNTERMODELS.md`, `FIXTURES.md`, `PROVENANCE.md` | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-09-17 | `prompts/2026-09-17-convergence-measure/` |
| `src/*.py` (loads `../2026-09-16-seed-statics/src/` by path, unmodified), `tests/*.py` | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-09-17 | `prompts/2026-09-17-convergence-measure/` |
| `lean/Workspace/Normativity/Contrib/ConvergenceMeasure.lean` | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-09-17 | `prompts/2026-09-17-convergence-measure/` |
| `prompts/2026-09-17-convergence-measure/PROMPT.md` | the maintainer, relayed verbatim | `ci-only` | 2026-09-17 | `prompts/2026-09-17-convergence-measure/` |
| `prompts/2026-09-17-convergence-measure/REPORT.md` | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-09-17 | `prompts/2026-09-17-convergence-measure/` |

## Lean declarations

All in `Workspace.Normativity.Contrib.ConvergenceMeasure`; every `#print axioms` reports
`[propext, Classical.choice, Quot.sound]` or fewer.  **Unregistered**; names provisional.

| declaration | kind | status |
|---|---|---|
| `IntervalData`, `Valid`, `hullLo`, `hullHi`, `hullWidth`, `commonLo`, `commonHi`, `commonWidth`, `Discord` (+ `Decidable`), `Weights`, `hullMass`, `overlapMass`, `discordMass` | definitions | — |
| `hullLo_le`, `le_hullHi`, `le_commonLo`, `commonHi_le`, `hullLo_nonneg`, `hullHi_le_one`, `hullWidth_nonneg`, `hullWidth_le_one`, `commonWidth_nonneg`, `commonWidth_le_hullWidth`, `hullLo_le_one`, `hullHi_nonneg` | lemmas | proved |
| `overlapMass_le_hullMass`, `hullMass_le_one`, `hullMass_nonneg`, `discordMass_nonneg` | inequalities | proved |
| `discordMass_eq_zero_iff`, `discordMass_pos` | positivity of discord mass under declared weights | proved |
| `touching`, `touching_refutes` | refutation of `Disc = 0 → Ovl > 0` | proved |
| `hullSum`, `unpinned`, `naiveHull`, `blockedHull` | definitions | — |
| `naiveHull_insert_pinned_le`, `blockedHull_insert_pinned` | dilution succeeds / is blocked | proved |
| `Nested`, `Nested.refl`, `Nested.ofPrivate` | definition, lemmas | proved |
| `hullLo_mono`, `hullHi_anti`, `commonLo_mono`, `commonHi_anti`, `hullWidth_anti`, `commonWidth_anti` | lemmas | proved |
| `discord_persists`, `hullMass_anti`, `overlapMass_anti`, `hullMass_mono`, `discordMass_mono` | H1 on interval data | proved |
| `discord_iff_pair` | Helly in dimension one | proved |
| `forcedRegionR_anti_warrants`, `forcedRegionR_anti_defeat` | region inclusion under narrowing / reopening | proved |
| `forcedInterval_nest_of_subset` | computed intervals nest under region inclusion | proved |
| `mergeCert`, `allowed_append_left`, `allowed_append_right`, `region_append_iff` | the discord certificate's construction | proved |
| `discord_certificate` | soundness: crossing bound certificates refute every common point | proved |
| `tendsto_of_summable_rises`, `hullMass_tendsto_of_summable`, `hullMass_tendsto_of_summable_rises` | H2 | proved |
| `pinned_lift` | `seed_independence_strict` for a family | proved |

Not stated in Lean: existence of the endpoint bound certificates (LP duality, item 94);
the exhaustive-sharing condition and H3's eventual constancy (stated in `DYNAMICS.md`
§3 from the seed round's `eventually_const_of_finite`, not composed in Lean); the
inclusion–exclusion identity relating hull mass to seed leverage; interval invariance
under fresh refinements (transport attack); anything in `CONSENSUS.md` or
`LI_COMPARISON.md`.

# Origin

This directory is a **branch round landed by a later round.** Its documents, `src/` and
`tests/` are the files of the round `2026-09-17-convergence-measure` as they stood on the
branch `round/2026-09-17-convergence-measure` (head `aa6756cc`, pull request #103, never
merged; the branch was based on the seed-statics branch), copied verbatim by the round
`2026-10-21-rebuttal-and-end-to-end` (its dispatch's Part B2). Nothing in them was edited
at landing. Its `src/profile.py` loads the seed-statics round's `src/` by relative path,
which the landed layout preserves.

The Lean was landed in part. `lean/Workspace/Normativity/Contrib/ConvergenceMeasure.lean`
on `main` carries the branch file's §1–§4 (interval data and the three masses, blocked
hull mass, dynamics on interval data, the region level); §5 (the discord certificate,
`mergeCert`, `discord_certificate`), §6 (`hullMass_tendsto_of_summable`,
`hullMass_tendsto_of_summable_rises`, `tendsto_of_summable_rises`) and §7 (`pinned_lift`)
are **not on `main`**, and the declaration tables in this directory's `PROVENANCE.md` and
`REPORT.md` name them. The landing round's `LANDING.md` has the table.

The round's items 95 and 96 were re-filed on `main` as items 119 and 120 by the landing
round (those numbers were taken on `main` in the meantime); the text in this directory
cites them by the branch numbers.

# Origin

This directory is a **branch round landed by a later round.** Its documents, `src/` and
`tests/` are the files of the round `2026-09-16-seed-statics` as they stood on the branch
`round/2026-09-16-seed-statics` (head `39ac06b8`, pull request #102, never merged), copied
verbatim by the round `2026-10-21-rebuttal-and-end-to-end` (its dispatch's ruling M6 and
Part B2). Nothing in them was edited at landing; where they cite `main`, they mean `main`
as of 2026-09-16 (`dcb2cded`).

What was *not* carried over verbatim is the Lean. The branch's
`lean/Workspace/Normativity/Contrib/SeedStatics.lean` was landed by the same round with
its §7 (confinement), §9 (transport) and §11 (non-dogmatism) left out and five small
additions from the warrant-enforcement-semantics round; the landing round's `LANDING.md`
has the table. The declaration tables in this directory's `PROVENANCE.md` and `REPORT.md`
therefore name some declarations (`confinement`, `confinement_common`,
`measure_form_refuted`, `transport`, `transport_sat_iff`, `Seed.structural`,
`Seed.LevelNeutral`, `disguise_caught`, `emptySeed_levelNeutral`, `Seed.Humble`,
`emptySeed_humble`) that are **not on `main`**.

The rulings this round cites "from the dispatch" (2026-08-08 past-self burn and seam
ordering; 2026-08-09 strength selection) were landed in `DECISIONS.md` on 2026-10-21,
subject to the maintainer's confirmation.

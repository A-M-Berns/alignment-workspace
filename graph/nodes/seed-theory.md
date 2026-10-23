---
id: seed-theory
kind: frame
children: [docket-seed, rebuttal.settleform-sound, rebuttal.liability-rebutted, seed.forced-interval-spec, seed.forced-interval-bounds, seed.independence-strict, seed.eventually-const, convergence.hull-mass-anti, convergence.discord-persists, convergence.discord-pairwise]
question: "What does a normative seed force on the prices of a settled fragment, how does that change under settlement, defeat and rebuttal, and do reasoners starting from different seeds end up anywhere together?"
owner: "@anson"
filed_from: wiki
narrative: wiki/Seed-Theory.md
roots:
  - {id: docket-seed, role: shared-claim, preset: worst-case}
  - {id: rebuttal.settleform-sound, role: shared-claim, preset: worst-case}
  - {id: rebuttal.liability-rebutted, role: shared-claim, preset: worst-case}
  - {id: seed.forced-interval-spec, role: shared-claim, preset: worst-case}
  - {id: seed.forced-interval-bounds, role: shared-claim, preset: worst-case}
  - {id: seed.independence-strict, role: shared-claim, preset: worst-case}
  - {id: seed.eventually-const, role: shared-claim, preset: worst-case}
  - {id: convergence.hull-mass-anti, role: shared-claim, preset: worst-case}
  - {id: convergence.discord-persists, role: shared-claim, preset: worst-case}
  - {id: convergence.discord-pairwise, role: shared-claim, preset: worst-case}
work:
  - {kind: round, ref: projects/normativity/seed/rounds/2026-09-16-seed-statics}
  - {kind: round, ref: projects/normativity/seed/rounds/2026-09-17-convergence-measure}
author: "@smithy-verity"
size: M
size_reason: "the statics, the rebuttal rule and the convergence profile, nine registered results and the seed project's work orders"
version: 1
---
## Statement
A seed's forced region and intervals are computed by the force layer's compiler and Fourier–Motzkin elimination, settlement nests them and defeat widens them, a form whose consequent is settled false is rebutted rather than contraposed, strict humility makes the pinned fragment seed-independent, and finitely many reasoners' intervals carry a convergence profile whose discord persists under nesting.

## Source
wiki/Seed-Theory.md, The statics, Rebuttal by settlement and Dynamics; projects/normativity/CLAIMS.md, the section Rebuttal by settlement and the seed statics (seed.*, rebuttal.*, convergence.*); projects/normativity/seed/README.md.

## Notes
Drafted from wiki/Seed-Theory.md per ruling M3 (prompts/2026-10-22-map-as-canonical); the owner has not confirmed. Roots: the registered seed, rebuttal and convergence results as formal results, and the docket of the seed project's work orders (items 117 to 123 and 126).

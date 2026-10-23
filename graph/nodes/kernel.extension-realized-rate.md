---
id: kernel.extension-realized-rate
kind: and
children: [kernel.extension-realized-rate.record, kernel.extension-realized-rate.bridge, kernel.extension-realized-rate.complete, kernel.extension-realized-rate.setting, kernel.extension-realized-rate.h1]
work: [{kind: round, ref: projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2}]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
author: "@smithy-verity"
---
## Statement
The registered claim kernel.extension-realized-rate (The extension's interface theorem: avg π ≤ avg (D − c_k)/ϖ + ε̄ ((D − w)/ϖ + θ_hi) + (B(K) + M(K))/(ϖ Σ w_k)) holds as its declaration states it; the registry's note is quoted in the Source.

## Source
projects/deference/CLAIMS.md, entry `kernel.extension-realized-rate` (class lean-proved, status active, origin round 2026-09-27-corrigibility-kernel-phase2; answers item 104).
Documentation: verification: projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md; context: prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md.
The signature of `Workspace.Deference.Contrib.KernelExtension.DecisionInterface.realized_rate` in lean/Workspace/Deference/Contrib/KernelExtension.lean.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; the hypotheses are the signature's explicit proposition binders, tagged open unless the registry settles them, and the data binders are the setting leaf. Registry note: For any chooser at the decision interface; with `maximizer_excludes` and `exploration_never_violates`. Restated by the follow-up (2026-09-27, Part 3): the exploration set's third clause is dropped, so the exploration term is the honest `ε̄ ((D − w)/ϖ + θ_hi)` (`lo = w` the range floor, `explore_range` the range fact) rather than `ε̄ θ_hi`; the clause survives as the variant `AboveAsking` with `rate_above_asking`, under which no-lock-in holds only for options estimated at least as good as asking (`above_asking_locks_in`, the fixture `src/exploration_lockin.py`). Inhabited by the BRIA realization `briaInterface`. What it does not say: that `B(K)` is `o(K)` — that is the realization's to discharge (BRIA's budget; unbiasedness from feedback, PAPER).

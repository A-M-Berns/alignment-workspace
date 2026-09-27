# Attribution — 2026-09-27-corrigibility-kernel-phase2

| | |
|---|---|
| Prompt author | the maintainer (`PROMPT.md`, verbatim) |
| Executor | Claude Fable 5.1 (Anthropic), in Claude Code |
| Round directory | `projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/` |
| Lean | `lean/Workspace/Deference/Spec/Headline.lean` (specification layer), `lean/Workspace/Deference/Contrib/KernelExtension.lean` |
| Landing | a pull request stacked on the phase-1 branch, which was open and unmerged at dispatch |

One deviation from the dispatch's premise: PR #113 (phase 1) was not merged when this
round was dispatched, so the round builds on that branch and its pull request targets it;
the maintainer confirmed this in conversation.  Two deviations in content, both stated in
the round's `REPORT.md`: the permitted exploration set carries a third clause (the
estimated residual at least asking's), without which the exploration term of the
realized-rate theorem is `ε̄ (D − w)/ϖ + ε̄ θ_hi` rather than `ε̄ θ_hi`; and promotion to
the specification layer is by re-declaration under the promoted names with the landed
originals unchanged, because moving the landed declarations would rename them and break
the axiom-audit baseline that conservativity freezes.  `incidents_le` is not deleted: the
theorem spine no longer cites it, and its deletion is a conservativity change reserved to
a maintainer commit.

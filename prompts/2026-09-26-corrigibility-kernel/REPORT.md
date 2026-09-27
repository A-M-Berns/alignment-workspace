# Attribution — 2026-09-26-corrigibility-kernel

| | |
|---|---|
| Prompt author | the maintainer (`PROMPT.md`, verbatim) |
| Executor | Claude Fable 5.1 (Anthropic), in Claude Code |
| Round directory | `projects/deference/rounds/2026-09-26-corrigibility-kernel/` |
| Lean | `lean/Workspace/Deference/Contrib/CorrigibilityKernel.lean` (adapters only) |
| Landing | its own pull request from `main` after the after-compromise round |

Phase 1 of two: a specification (`SPEC.md`) and an inventory (`REPORT.md`) for the
maintainer's review, with adapter lemmas only.  Two deviations from the dispatch's
expectations, both stated in the round's `REPORT.md` §9: ratification and clean
overwrite are partial cases of the count's remedy step rather than of the evaluator
`V_J`; and the landed `uncertainty_deference_le` bounds the true cost of deferring rather
than the estimated margin for asking, so the adapter proves the dispatch's direction and
the report keeps both.  What did not compress is reported (§6) rather than forced: the
recognized count is a sum over four models, the split gate is a finite model, the
evaluator-to-auction bridge is by hand, Box 2 is on the thin allocation.  Nothing is
registered; nothing is deleted; no item is filed; five decisions are queued.

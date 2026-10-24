---
id: compiler.deductive-end-to-end.h-stages-satisfiable
kind: leaf
leaf_kind: hypothesis
discharge: open
author: "@smithy-verity"
size: S
size_reason: "one hypothesis of the declaration, read"
version: 1
---
## Statement
Every stage of the deductive process is propositionally satisfiable: some propositionally consistent world agrees with the stage.

## Source
projects/normativity/CLAIMS.md, entry `compiler.deductive-end-to-end` (class lean-proved, status active, origin round 2026-08-18-projection-enforcement; answers item 48).
The signature of `Workspace.Normativity.Contrib.DeductiveEffective.deductive_end_to_end` in lean/Workspace/Normativity/Contrib/DeductiveEffective.lean, read by the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice); the file's header docstring ("The hypotheses are exactly: …").

## Notes
The binder `hsat`. Open: a consistency assumption on the process that the declaration consumes and does not derive; the source's deductive processes are consistent by stipulation, and a reader granting the claim for a given process must grant this of it. It does not restate the conclusion.

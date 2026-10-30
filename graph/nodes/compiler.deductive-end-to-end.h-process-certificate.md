---
id: compiler.deductive-end-to-end.h-process-certificate
kind: leaf
leaf_kind: hypothesis
discharge: definitional
author: "@smithy-verity"
size: S
size_reason: "one hypothesis of the declaration, read"
version: 1
---
## Statement
The deductive process carries the pinned source's own computability certificate: a program that eventually emits each stage.

## Source
projects/normativity/CLAIMS.md, entry `compiler.deductive-end-to-end` (class lean-proved, status active, origin round 2026-08-18-projection-enforcement; answers item 48).
The signature of `Workspace.Normativity.Contrib.DeductiveEffective.deductive_end_to_end` in lean/Workspace/Normativity/Contrib/DeductiveEffective.lean, read by the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice); the file's header docstring ("The hypotheses are exactly: …").

## Notes
The binder `process : DeductiveProcessComputation DP`. Definitional: the source's definition of a deductive process (a computably enumerable stage sequence), the hypothesis the source's own theorem carries, and no restriction added by this declaration; the file's header says no hypothesis about the process beyond the source's own is needed.

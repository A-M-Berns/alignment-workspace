---
id: compiler.deductive-end-to-end.h-fragment-schedule
kind: leaf
leaf_kind: hypothesis
discharge: definitional
author: "@smithy-verity"
size: S
size_reason: "one hypothesis of the declaration, read"
version: 1
---
## Statement
The fragment schedule assigns each date a duplicate-free list of sentences and is primitive recursive.

## Source
projects/normativity/CLAIMS.md, entry `compiler.deductive-end-to-end` (class lean-proved, status active, origin round 2026-08-18-projection-enforcement; answers item 48).
The signature of `Workspace.Normativity.Contrib.DeductiveEffective.deductive_end_to_end` in lean/Workspace/Normativity/Contrib/DeductiveEffective.lean, read by the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice); the file's header docstring ("The hypotheses are exactly: …").

## Notes
The binders `coords`, `nodup` and `hcoords`: the schedule object's own data and its computability, read as one hypothesis. Definitional: it says what a fragment schedule is, and asks nothing of the deductive process.

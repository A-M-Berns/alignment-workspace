---
id: certificate.grade-register-strict.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `certificate.grade-register-strict` formalizes the registered claim as the registry reads it: the strict grade-register theorem.

## Source
projects/deference/CLAIMS.md, entry `certificate.grade-register-strict` (class lean-proved, status active, origin round 2026-08-11-phase-ii-promotion; answers item 23).
Documentation: verification: prompts/2026-08-11-phase-ii-promotion/REPORT.md; context: prompts/2026-08-11-deference-certificates/REPORT.md.
Short name: the strict grade-register theorem.
Conclusion of the signature: `gradeValuation p v (fun _ => π) < gradeValuation p v (gatedAct S j J)`.

---
id: kernel.corrigible-fidelity-score.bridge
kind: leaf
leaf_kind: bridge
attribution: formalizer-stated
size: S
size_reason: "one signature against the registry's reading"
version: 1
author: "@smithy-verity"
---
## Statement
The statement of record of `kernel.corrigible-fidelity-score` formalizes the registered claim as the registry reads it: The fidelity score is corrigible: known faithfulness beats known unfaithfulness by ϖ − (D − w) whatever the ordinary values, and risk is accepted only at (D − c)/ϖ.

## Source
projects/deference/CLAIMS.md, entry `kernel.corrigible-fidelity-score` (class lean-proved, status active, origin round 2026-09-27-corrigibility-kernel-phase2; answers item 104).
Documentation: verification: projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md; context: prompts/2026-09-27-corrigibility-kernel-phase2/FOLLOWUP.md.
Short name: The fidelity score is corrigible: known faithfulness beats known unfaithfulness by ϖ − (D − w) whatever the ordinary values, and risk is accepted only at (D − c)/ϖ.
Conclusion of the signature: `Corrigible (fun bid n p => P.evalOf bid n p 0) P.D P.w P.ϖ`.

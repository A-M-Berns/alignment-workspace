---
id: trace-nonrecoverability.record
kind: leaf
leaf_kind: record
statement_of_record: IdentifiedSet.defect_consistent_iff
hypotheses: [trace-finite-report-layer]
author: "@smithy-verity"
size: S
size_reason: "two declarations and the package gate"
version: 1
---
## Statement
The declarations no_recovery and IdentifiedSet.defect_consistent_iff in
Cleanroom.Trust.LegitFiniteDefect are accepted by the Lean kernel under the
package's gate.

## Source
projects/deference/faf-cleanroom-2026-10-02/packages/legit-finite-defect/legit-finite-defect-report.md,
"Gate: PASS" (952 declarations; axioms propext, Classical.choice, Quot.sound;
no sorry) and the identified-set item of "State of the package".

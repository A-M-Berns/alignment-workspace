---
id: legit-ddb-transfer.record
kind: leaf
leaf_kind: record
statement_of_record: Transfer.legitimizingTT_iff_legitValue
hypotheses: [legit-finite-frames, legit-positive-mass]
author: "@smithy-verity"
size: S
size_reason: "three declarations and the package gate"
version: 1
---
## Statement
The declarations Transfer.legitimizingTT_iff_legitValue,
Transfer.legitimizingTT_iff_hullAndModestlyInformed and
Transfer.legitimizingTT_iff_epistemicValue in
Cleanroom.Corrigibility.CorrLegitGeneral are accepted by the Lean kernel under
the package's gate.

## Source
projects/deference/faf-cleanroom-2026-10-02/packages/corr-legit-general/corr-legit-general-ledger.md
(the three declarations) and corr-legit-general-report.md, "Gate: PASS" (2910
declarations; axioms propext, Classical.choice, Quot.sound).

## Notes
The public package carries the report, ledger, findings and audit files, not
the Lean sources. Without a claims-registry entry the
record's own validity level caps at 2; a human map-read lifts it.

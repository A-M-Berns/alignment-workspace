---
id: pressure-as-external-trader.record
kind: leaf
leaf_kind: record
statement_of_record: exo_day_value_le
hypotheses: [pressure-as-external-trader.setting]
author: "@smithy-verity"
size: S
size_reason: one declaration and its ledger row
version: 1
---
## Statement
The declaration exo_day_value_le of the clean-room package corr-exo-trader is
accepted by the Lean kernel with the axioms propext, Classical.choice and
Quot.sound only.

## Source
projects/deference/faf-cleanroom-2026-10-02/packages/corr-exo-trader/corr-exo-trader-ledger.md,
the row for `exo_day_value_le`; the package's report and findings files beside
it.

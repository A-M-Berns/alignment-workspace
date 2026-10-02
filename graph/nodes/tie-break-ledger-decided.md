---
id: tie-break-ledger-decided
kind: leaf
leaf_kind: assumption
author: "@smithy-verity"
size: S
size_reason: one page's opening paragraph and one remark item
version: 1
---
## Statement
The rule selecting among equal-maximal menu options is computable from the
published estimates and the ledger, so the followed strategy is an efficiently
describable logically uncertain variable whose value the expert's estimate
places at the maximum.

## Source
projects/deference/note-dump-2026-08-11/wiki/ledger-decided-tie-breaks.md,
opening: "The argmax strategy's tie-break rule must be computable from the
published estimates — equivalently, Γ-decided given the ledger."

projects/deference/note-dump-2026-08-11/wiki/mart-implies-value.md, Remark:
"the tie-break must be ledger-decided (Γ-decided given the published estimates
— equivalently, computable from them), or F1 fails outright by correlation".

## Notes
Discharges part of hUM_S. The page's counterexample shows a definable but
undecidable rule breaks F1 by correlation and, with an adversarial rule,
breaks Value itself.

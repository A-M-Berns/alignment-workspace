---
id: mart-implies-value-kernel.record
kind: leaf
leaf_kind: record
statement_of_record: DeferenceArgmax.value_argmax_asymptotic
hypotheses: [tt-implies-mart-gap-bets, expert-knows-own-estimates, tie-break-ledger-decided, novice-expprovind]
author: "@smithy-verity"
size: S
size_reason: one declaration and its axiom print
version: 1
---
## Statement
The declaration DeferenceArgmax.value_argmax_asymptotic (ES Em Emi Eoi : ℕ →
ℝ) (hUM_S : Approx ES Em) (hMon : AsympLE Emi Em) (hCee : Approx Eoi Emi) :
AsympLE Eoi ES is accepted by the Lean kernel.

## Source
projects/deference/note-dump-2026-08-11/lean-deference/LeanDeference.lean L317
(`theorem value_argmax_asymptotic`) and L376 (`#print axioms
DeferenceArgmax.value_argmax_asymptotic`); the signature as quoted at
projects/deference/note-dump-2026-08-11/wiki/mart-implies-value.md, Status.

## Notes
Without a claims registry in this tree the record's own validity level caps at
2; a human map-read lifts it.

---
id: mart-implies-value-kernel
kind: and
children: [mart-implies-value-kernel.record, mart-implies-value-kernel.bridge, tt-implies-mart-gap-bets, expert-knows-own-estimates, tie-break-ledger-decided, novice-expprovind, mart-implies-value-kernel.complete]
author: "@smithy-verity"
size: M
size_reason: "one theorem page, a Lean signature and four discharging claims"
version: 1
---
## Statement
For every efficiently describable sequence of finite menus and every fixed
index i, the novice asymptotically weakly prefers following the expert to
committing to any fixed option: E^H_n(Ŝ_n) ≳_n E^H_n(O^i_n), which is Value of
the novice toward the expert.

## Source
projects/deference/note-dump-2026-08-11/wiki/mart-implies-value.md, Statement:
"by the novice's own current lights, 'let the expert decide' is asymptotically
weakly preferred to committing to any fixed option — Value". Status:
"KERNEL-CHECKED — `DeferenceArgmax.value_argmax_asymptotic` (in
`LeanDeference.lean`)".

## Notes
A formal result: the record is the kernel-checked composition, the bridge says
what its three hypotheses mean, and the four discharging claims are the
children the record's hypotheses field names. hUM_S is discharged by the
gap-bet tower, the expert's knowledge of its own estimates and the
ledger-decided tie-break together; hMon by expectation provability induction
for the novice; hCee by the gap-bet tower on the fixed option.

The page's own caveat is the line the completeness leaf carries: the kernel
certifies the composition, and the tower steps, the market and the traders are
unmodeled.

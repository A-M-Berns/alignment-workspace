---
id: warrant.licence-chain.h-authorized-event
kind: leaf
leaf_kind: hypothesis
discharge: definitional
author: "@smithy-verity"
size: S
size_reason: "one hypothesis of the declaration, read"
version: 1
---
## Statement
The event that issued and selected the certificate is one the record authorizes.

## Source
projects/normativity/CLAIMS.md, entry `warrant.licence-chain` (class lean-proved, status active, origin round 2026-10-20-warrant-enforcement-semantics; answers item 56).
The signature of `Workspace.Normativity.Contrib.WarrantEntitlement.licence_chain` and the definitions `Admissible`, `SupportedOn`, `Supported`, `RecordState` and `Licensed` in lean/Workspace/Normativity/Contrib/WarrantEntitlement.lean; projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/LICENCE_CHAIN.md, A2 (the chain); read by the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice).

## Notes
The second conjunct of `h : Licensed R φ v c event`. Definitional: part of what Licensed means; the conclusion does not read it (neither Supported nor Admissible mentions the event), so the chain carries the authorization clause without using it. Where a licence is refused for lack of authorization is the countermodel `supported_not_licensed`, not this theorem.

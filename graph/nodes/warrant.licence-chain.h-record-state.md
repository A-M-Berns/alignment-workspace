---
id: warrant.licence-chain.h-record-state
kind: leaf
leaf_kind: hypothesis
discharge: definitional
author: "@smithy-verity"
size: S
size_reason: "one hypothesis of the declaration, read"
version: 1
---
## Statement
A record state at a step consists of admitted grounds, a docket, a settlement and the set of record events the record authorizes.

## Source
projects/normativity/CLAIMS.md, entry `warrant.licence-chain` (class lean-proved, status active, origin round 2026-10-20-warrant-enforcement-semantics; answers item 56).
The signature of `Workspace.Normativity.Contrib.WarrantEntitlement.licence_chain` and the definitions `Admissible`, `SupportedOn`, `Supported`, `RecordState` and `Licensed` in lean/Workspace/Normativity/Contrib/WarrantEntitlement.lean; projects/normativity/rounds/2026-10-20-warrant-enforcement-semantics/LICENCE_CHAIN.md, A2 (the chain); read by the site-vertical-slice round (projects/enabling/rounds/2026-10-24-site-vertical-slice).

## Notes
The implicit binder `R : RecordState d` and the coordinate and value `φ`, `v`. Definitional: the object the chain is stated over, Part A's view of the record; nothing is assumed of its contents.

---
id: delegation.gradetrust-refinement.h6
kind: leaf
leaf_kind: hypothesis
discharge: open
size: S
size_reason: "one binder of one declaration"
version: 1
author: "@smithy-verity"
---
## Statement
The hypothesis `hsum : ∀ x : C, ∑ y ∈ univ.filter (fun y => r y = x), q y = 1` of the declaration holds.

## Source
The signature of `Workspace.Deference.Contrib.DelegationBridge.gradeTrust_of_refinement` in lean/Workspace/Deference/Contrib/DelegationBridge.lean.
Binder: `hsum : ∀ x : C, ∑ y ∈ univ.filter (fun y => r y = x), q y = 1`.

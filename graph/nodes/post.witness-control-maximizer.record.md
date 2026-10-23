---
id: post.witness-control-maximizer.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.EffectiveAuthority.Dep.control_maximizer_floods_module
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: post.witness-control-maximizer
---
## Statement
The declaration Workspace.Deference.Contrib.EffectiveAuthority.Dep.control_maximizer_floods_module is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `post.witness-control-maximizer` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.EffectiveAuthority.Dep.control_maximizer_floods_module` (theorem) in lean/Workspace/Deference/Contrib/EffectiveAuthority.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (z : ℕ → Unit) :
        exercises (canonicalAsks pr₃ [0, 1, 2]) < exercises [0, 1, 2] ∧
          asksDeviate pr₃ [0, 1, 2] [0, 1, 2] = true ∧
          FloodShortfall depI (revocationJ (5 / 4)) (fun _ _ => True) depCost (1 / 4) 0
            (exercises (canonicalAsks pr₃ [0, 1, 2])) (exercises [0, 1, 2]) 0 z ⟨1, false⟩ ()

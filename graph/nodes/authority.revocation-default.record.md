---
id: authority.revocation-default.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.EffectiveAuthority.Dep.atrophy_on_module
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: authority.revocation-default
---
## Statement
The declaration Workspace.Deference.Contrib.EffectiveAuthority.Dep.atrophy_on_module is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `authority.revocation-default` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.EffectiveAuthority.Dep.atrophy_on_module` (theorem) in lean/Workspace/Deference/Contrib/EffectiveAuthority.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (z : ℕ → Unit) :
        ¬ Short depI (revocationJ 1) (fun _ _ => True) depCost 0 z ⟨1, false⟩ () ∧
          Short depI (revocationJ 1) (fun _ _ => True) depCost 0 z ⟨2, false⟩ () ∧
          CausedShortfall depI (revocationJ 1) (fun _ _ => True) depCost buildPolicy (at_ ⟨1, false⟩) 0 z () ∧
          EntrenchAt depI (revocationJ 1) (fun _ _ => True) depCost buildPolicy (at_ ⟨1, false⟩) 0 z () ∧
          ¬ CausedShortfall depI (revocationJ 1) (fun _ _ => True) depCost buildPolicy (at_ ⟨0, false⟩) 0 z ()

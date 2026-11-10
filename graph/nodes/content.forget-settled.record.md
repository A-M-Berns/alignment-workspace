---
id: content.forget-settled.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.Forgetting.forget_settled
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: content.forget-settled
---
## Statement
The declaration Workspace.Normativity.Contrib.Forgetting.forget_settled is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `content.forget-settled` (class lean-proved, status active, origin round 2026-11-08-content-recollection; answers item 134).
Documentation: verification: projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md; context: projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md.
The signature of `Workspace.Normativity.Contrib.Forgetting.forget_settled` (theorem) in lean/Workspace/Normativity/Contrib/Forgetting.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {A : Type*} (S : Seed (d + 1) A) (W : List (SubItem (d + 1)))
        (st : DocketState) {F F' : Settlement (d + 1)} (k : Fin (d + 1)) {b : Bool}
        (hk : F.val k = some b) (hF : F.le F') (x : Fin d → ℚ) :
        projection k.succAbove (forcedRegion S W st F') x ↔
          InCube x ∧ (dropSettlement k F').Pinned x ∧
          (∀ it ∈ S.liveSub st ++ W, (dropCoord k (specialize F it.form.row)).Sat x) ∧
          (∀ it ∈ S.liveStr st, (dropCoord k (specialize F it.row)).Sat x)

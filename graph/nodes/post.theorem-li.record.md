---
id: post.theorem-li.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.PostStatement.post_theorem_li
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: post.theorem-li
---
## Statement
The declaration Workspace.Deference.Contrib.PostStatement.post_theorem_li is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `post.theorem-li` (class lean-proved, status active, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.PostStatement.post_theorem_li` (theorem) in lean/Workspace/Deference/Contrib/PostStatement.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {Q M Res Disc : Type*} [DecidableEq M] {P : History} {DP : DeductiveProcess}
        [IsLogicalInductor P DP] (L : LexParams) (J : AllocationOfAuthority M Res Disc)
        (resolves approved : Q → M → Prop) (Viol : Q → Bool)
        (hviol : ∀ a m, J.Reserved m → resolves a m → ¬ approved a m → Viol a = true)
        (queue : Q) (hq : ∀ m, ¬ resolves queue m) (hqv : Viol queue = false)
        (pool : List M) (pr : Workspace.Deference.Contrib.EffectiveAuthority.Protocol M) (asks : Q → List M)
        (hask : ∀ a, Workspace.Deference.Contrib.EffectiveAuthority.asksDeviate pr pool (asks a) = true →
          Viol a = true)
        (hqa : asks queue = Workspace.Deference.Contrib.EffectiveAuthority.canonicalAsks pr pool)
        (bid : Q → ℝ)
        (nKnown : Q → ℕ) (XS : Q → LUV) (n : ℕ) (hb : ∀ a, bid a ≤ L.D)
        (hcount : ∀ a, Viol a = true → 1 ≤ nKnown a) (hqk : nKnown queue = 0)
        (hqp : (XS queue).expect P n = 0) (hqw : L.w ≤ bid queue) :
        let H : PostHypotheses Q M Res Disc

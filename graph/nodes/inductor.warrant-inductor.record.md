---
id: inductor.warrant-inductor.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.WarrantInductor.warrant_inductor
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: inductor.warrant-inductor
---
## Statement
The declaration Workspace.Normativity.Contrib.WarrantInductor.warrant_inductor is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `inductor.warrant-inductor` (class lean-proved, status active, origin round 2026-10-22-normative-inductor-integration; answers item 35).
Documentation: verification: projects/normativity/rounds/2026-10-22-normative-inductor-integration/THEOREM_STORY.md; context: projects/normativity/rounds/2026-10-22-normative-inductor-integration/HANDOFFS.md.
The signature of `Workspace.Normativity.Contrib.WarrantInductor.warrant_inductor` (theorem) in lean/Workspace/Normativity/Contrib/WarrantInductor.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    {Occ Req : Type*} {S : Protocol Occ Req} {anchor : Occ → Req}
        {O : ObligationState S anchor} {Expresses : Req → Form d → Prop} {Q : Type} [Fintype Q]
        [DecidableEq Q]
        (N : ℕ → NormState d) (F : FragmentMap d) (res : ℕ → CompileResult (Cite d) d)
        (tol : ℕ → ℚ) (htol : ∀ n, 0 < tol n)
        (ent : ∀ n, Entitlement O (N n).grounds Expresses) (hwf : ∀ n, (N n).grounds.WellFormed)
        (DP : DeductiveProcess) (process : DeductiveProcessComputation DP)
        (hE : EffectiveEnforcerComputation (schedule N F res tol htol).enforcer)
        (B : ℝ)
        (hliab : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
          -B ≤ (realizedEnforcer DP ((schedule N F res tol htol).enforcer.adaptive DP)).netWorth
            ((schedule N F res tol htol).market DP) v n)
        (A : AdapterProtocol O d Q)
        (henf : ∀ s ∈ A.services, Enforced (N s) (res s))
        (hex : ∀ s ∈ A.services, (A.prob s).Excludes (N s).bundle)
        (hmar : ∀ s ∈ A.services, (A.prob s).Margins (N s).bundle (tol s))
        (hεad : ∀ s ∈ A.services, 0 ≤ A.εad s) (hD : 0 ≤ A.D)
        (hadequate : ∀ r, ∀ s ∈ A.services, ∀ q ∈ (A.prob s).A, A.lam r s q ≤ A.εad s)
        (hbound : ∀ r s q, A.lam r s q ≤ A.D)
        (hlam : ∀ s ∈ A.services, 0 ≤ A.lamS s) (hlampos : 0 < ∑ s ∈ A.services, A.lamS s)
        (hbudget : ∀ s ∈ A.services, A.lamS s * (((A.prob s).massCap * tol s : ℚ) : ℝ) ^ 2 ≤ A.ρ s)
        (hΓ : 0 ≤ A.Γ)
        (hamp : ∀ s ∈ A.services, ∑ e ∈ O.boundary.exposed, A.T e s * (A.D * (A.prob s).κ) ≤
          A.Γ * (A.lamS s / ∑ t ∈ A.services, A.lamS t)) :
        IsLogicalInductor ((schedule N F res tol htol).market DP) DP ∧
        (∀ n, Enforced (N n) (res n) →
          ∀ c ∈ (N n).bundle, excess c.row ((schedule N F res tol htol).priceVec DP n) ≤ tol n) ∧
        (∀ n, ∀ c ∈ (schedule N F res tol htol).bundle n,
          (∃ o ∈ (N n).survivors, c.cites = Cite.sub o.id ∧ (ent n).Entitled o ∧
            ∀ j, o.cites = .occurrence j → ∃! o', o' ∈ (N n).survivors ∧ o'.id = j) ∨
          (∃ it ∈ (N n).seed.liveStr (N n).docket, c.cites = Cite.str it.id) ∨
          ∃ i, c.cites = Cite.settled i) ∧
        (∀ s ∈ A.services,
          massOff ((A.prob s).gate fun j => (schedule N F res tol htol).market DP s (F.ι j))
              (A.prob s).A ≤
            (A.prob s).κ * (A.evaluation F.ι).defect s ((schedule N F res tol htol).market DP) ∧
          (A.evaluation F.ι).defect s ((schedule N F res tol htol).market DP) ≤
            (((A.prob s).massCap * tol s : ℚ) : ℝ)) ∧
        (A.evaluation F.ι).progress ((schedule N F res tol htol).market DP) ≤
          (A.evaluation F.ι).modulus + (A.evaluation F.ι).error +
            A.D * (A.evaluation F.ι).residual

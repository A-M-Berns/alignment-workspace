import Cleanroom.Corrigibility.LegitNegDynamic.Revision

/-!
Audit r2 (adversarial) probe for `legit-neg-dynamic`, E6: finding 46, the ledger's refuted row and
the docstrings of `E6_refuted`/`E6_blocks_iff_dominance` assert — in prose only — that the *"if"*
direction of the source's sentence fails too: `A1` with `ϖ < d` is revision-invariant and PREs at
every credence. Machine-checked here: with `ϖ < d`, `rulesToy … 1` (A1) is `RevisionInvariant` and
`H WAIT < H PRE` for every `ρ ∈ [0, 1]`. So V-E6's "revision-invariance is sufficient" needs
`ϖ ≥ d` (true of the fixture's `ϖ = 2 > d = 1/10`, silently). Not imported by the library.
-/

namespace Cleanroom.Corrigibility.LegitNegDynamic

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem
  Cleanroom.Corrigibility.LegitNegPricing

example (d h ϖ c : ℚ) (hϖ : ϖ < d) :
    (∀ ρ (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1), RevisionInvariant (rulesToy d h ϖ c ρ h0 h1 1)) ∧
    (∀ ρ (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1),
      (rulesToy d h ϖ c ρ h0 h1 1).H 0 < (rulesToy d h ϖ c ρ h0 h1 1).H 1) := by
  refine ⟨fun ρ h0 h1 => ?_, fun ρ h0 h1 => ?_⟩
  · unfold RevisionInvariant; simp [rulesToy, rulesU]
  · have e := (rulesToy_Δ d h ϖ c ρ h0 h1).2.1
    unfold Δ at e; linarith

-- and, through the surviving neighbour, the sufficiency clause's penalty hypothesis is exactly what
-- `ϖ < d` violates: the branchwise-dominance criterion fails on both branches.
example (d h ϖ c : ℚ) (hϖ : ϖ < d) :
    ¬ (rulesU 1 d h ϖ c 0 1 ≤ rulesU 1 d h ϖ c 0 0 ∧ rulesU 1 d h ϖ c 1 1 ≤ rulesU 1 d h ϖ c 1 0) := by
  simp [rulesU]; linarith

end Cleanroom.Corrigibility.LegitNegDynamic

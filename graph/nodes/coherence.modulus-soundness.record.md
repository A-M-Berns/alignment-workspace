---
id: coherence.modulus-soundness.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Normativity.Contrib.CoherenceModulus.gap_le_of_mixture
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: coherence.modulus-soundness
---
## Statement
The declaration Workspace.Normativity.Contrib.CoherenceModulus.gap_le_of_mixture is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/normativity/CLAIMS.md, entry `coherence.modulus-soundness` (class lean-proved, status active, origin round 2026-08-16-traderized-enforcement; answers item 42).
Documentation: verification: projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md; context: projects/normativity/rounds/2026-08-16-traderized-enforcement/PROOF_CLOSURE.md.
The signature of `Workspace.Normativity.Contrib.CoherenceModulus.gap_le_of_mixture` (theorem) in lean/Workspace/Normativity/Contrib/CoherenceModulus.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (coords : Finset κ) (worlds : Finset ι) (Wld : ι → κ → ℚ)
        (p : κ → ℚ) (low : (κ → ℚ) → ℚ)
        (hlow_le : ∀ c, ∀ w ∈ worlds, low c ≤ pair coords c (Wld w))
        (μ : ι → ℚ) (hμ : IsCredence worlds μ) {B : ℚ} (hB : 0 ≤ B)
        (hclose : ∀ k ∈ coords, |mixture worlds Wld μ k - p k| ≤ B)
        (c : κ → ℚ) (hc : l1 coords c ≤ 1) :
        gap coords low p c ≤ B

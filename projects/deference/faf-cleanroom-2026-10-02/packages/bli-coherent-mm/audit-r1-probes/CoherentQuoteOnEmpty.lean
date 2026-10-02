import Cleanroom.Bli.BliCoherentMm.Maker

/-!
Audit round 1, adversarial lens — probe for the coherence notion of record `CoherentQuoteOn`
(T2(b), T3, T6): on an **empty** priced set it says only that some world measure exists. So the
T6 coherence headline `pcOverlay_coherent_mentioned` has no content on a day whose priced set is
empty (the firm mentions nothing and `X n = ∅`); the package's guard is
`pcOverlay_paperDP_mentioned_nonempty` (nonempty from some day on, at the witness). Not imported
by the library.
-/

namespace Cleanroom.Bli.BliCoherentMm.AuditR1Adv

open LogicalInduction LO.Propositional BoolPCWorld Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliOverlay

/-- `CoherentQuoteOn V ∅ D B` holds iff some world measure over `D` exists: it constrains `V`
not at all. -/
theorem coherentQuoteOn_empty_iff (V : Sentence → ℚ) (D : Finset Sentence) (B : ℕ) :
    CoherentQuoteOn V ∅ D B ↔ ∃ w : FiniteWorld B → ℚ, IsWorldMeasure w D := by
  constructor
  · rintro ⟨w, hw, _⟩
    exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, hw, fun φ hφ => by simp at hφ⟩

end Cleanroom.Bli.BliCoherentMm.AuditR1Adv

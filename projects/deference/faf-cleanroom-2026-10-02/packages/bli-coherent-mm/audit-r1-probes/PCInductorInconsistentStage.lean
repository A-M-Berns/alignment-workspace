import Cleanroom.Bli.BliCoherentMm.Recursion

/-!
Audit round 1, adversarial lens — probe for `PCInductor` and the unconditional T6 headline
`pcOverlay_no_ec_trader_exploits` (every `DP`, `ov`, `X`).

Two checks on the process whose every stage is `{⊥}` (legal for FAF's `DeductiveProcess`, which
has no consistency field — findings F11): (1) `PCInductor` has **no** inhabitant there, so the
structure's `coh` field is not vacuous — it cannot be met by a fallback table; (2) every trader's
plausible-assessment set is empty there, so FAF's `Exploits` is refutable for free: the
unconditional "no e.c. trader exploits" headline is vacuous exactly on such processes, which the
package discloses and guards with the `paperDP 𝗜𝚺₁` witness
(`pcOverlay_paperDP_plausibleAssessments_nonempty`). Not imported by the library.
-/

namespace Cleanroom.Bli.BliCoherentMm.AuditR1Adv

open LogicalInduction LO.Propositional BoolPCWorld Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliOverlay

/-- The process every stage of which is `{⊥}`. -/
def botDP : DeductiveProcess := ⟨fun _ => {⊥}, fun _ => Finset.Subset.refl _⟩

/-- No `PCWorld` is consistent with `{⊥}`. -/
theorem not_consistentWith_bot (v : PCWorld) : ¬ v.ConsistentWith ({⊥} : Finset Sentence) := by
  intro h
  have := h ⊥ (Finset.mem_singleton_self _)
  simp [PCWorld.Holds, LO.Propositional.Formula.Boolean.val] at this

/-- No world measure exists over `{⊥}` (the support clause forces every weight to `0`). -/
theorem not_isWorldMeasure_bot {B : ℕ} (w : FiniteWorld B → ℚ) :
    ¬ IsWorldMeasure w ({⊥} : Finset Sentence) := by
  rintro ⟨_, hsum, hsupp⟩
  have h0 : ∑ u, w u = 0 := Finset.sum_eq_zero fun u _ => by
    by_contra h
    exact not_consistentWith_bot _ (hsupp u h)
  rw [hsum] at h0
  exact one_ne_zero h0

/-- `PCInductor` has no inhabitant over a process with an inconsistent stage: the `coh` field has
teeth (a fallback table cannot inhabit the structure). -/
theorem pcInductor_isEmpty_bot : IsEmpty (PCInductor botDP) := by
  refine ⟨fun I => ?_⟩
  obtain ⟨B, w, hw, _, _⟩ := I.coh 0
  exact not_isWorldMeasure_bot w hw

/-- Over such a process every trader's plausible-assessment set is empty, so `¬ Exploits` holds
for free: the unconditional T6 headline is vacuous there (disclosed, F11). -/
theorem plausibleAssessments_bot_eq_empty (Tr : Trader) (P : History) :
    Tr.plausibleAssessments P botDP = ∅ := by
  ext x
  constructor
  · rintro ⟨n, v, hv, _⟩
    exact absurd hv (not_consistentWith_bot v)
  · intro h
    exact absurd h (Set.notMem_empty x)

end Cleanroom.Bli.BliCoherentMm.AuditR1Adv

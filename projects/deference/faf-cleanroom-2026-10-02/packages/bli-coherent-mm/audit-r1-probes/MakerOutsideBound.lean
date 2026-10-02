import Cleanroom.Bli.BliCoherentMm.Contrast

/-!
Audit round 1, adversarial lens — probe for the D4 docstring of `interiorCoherentMarketMaker`
(record `Maker.lean`: "non-dogmatic on every sentence of `S` undecided by `D`") and the report's
headline sentence ("non-dogmatic on every undecided sentence of `S`").

The theorems carry an atom-bound qualifier (`interior_nonDogmatic` is over **finite** worlds;
`interior_D_ND_day_on` carries `hBS`); the D4 docstring and the report sentence do not. This probe
shows the qualifier is load-bearing: `atom B` is undecided by `D = ∅` in the `PCWorld` sense, yet
every weight vector over `B` atoms — hence the interior maker, whenever `atom B ∈ S` — prices it
at exactly `0`. Not imported by the library.
-/

namespace Cleanroom.Bli.BliCoherentMm.AuditR1Adv

open LogicalInduction LO.Propositional BoolPCWorld Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliOverlay

/-- Every weight vector over `B` atoms prices `atom B` at `0`: the atom reads `false` in every
finite world over `B` atoms. -/
theorem marginal_atom_bound_eq_zero {B : ℕ} (w : FiniteWorld B → ℚ) :
    marginal w (Formula.atom B) = 0 := by
  unfold marginal AttemptA.marginal
  apply Finset.sum_eq_zero
  intro u _
  simp [FiniteWorld.payoutRat, FiniteWorld.toBoolPCWorld, eval]

/-- `atom B` is undecided by the empty stage in the `PCWorld` sense. -/
theorem atom_bound_undecided (B : ℕ) :
    (∃ v : PCWorld, v.ConsistentWith ∅ ∧ v.Holds (Formula.atom B)) ∧
    (∃ v : PCWorld, v.ConsistentWith ∅ ∧ ¬ v.Holds (Formula.atom B)) :=
  ⟨⟨fun _ => True, fun _ h => by simp at h, (PCWorld.holds_atom _ _).mpr trivial⟩,
   ⟨fun _ => False, fun _ h => by simp at h, fun h => (PCWorld.holds_atom _ _).mp h⟩⟩

/-- The interior maker prices a sentence of `S` outside the atom bound at `0`, although that
sentence is undecided by `D = ∅`: the D4 docstring's "non-dogmatic on every sentence of `S`
undecided by `D`" needs "within the atom bound". -/
theorem interior_quote_atom_bound_eq_zero {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (B : ℕ) (S : Finset Sentence) (hS : mentionedSet T ⊆ S)
    {ε : ℚ} (hε : 0 < ε) (hφ : Formula.atom B ∈ S) :
    (interiorCoherentMarketMaker T past ∅ B S hS (hW_empty B) hε).quote (Formula.atom B) = 0 := by
  rw [interior_quote_eq_pi T past ∅ B S hS (hW_empty B) hε hφ]
  exact marginal_atom_bound_eq_zero _

end Cleanroom.Bli.BliCoherentMm.AuditR1Adv

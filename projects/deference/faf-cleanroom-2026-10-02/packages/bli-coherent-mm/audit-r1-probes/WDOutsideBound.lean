import Cleanroom.Bli.BliCoherentMm.Worlds

/-!
Audit round 1, adversarial lens — probe for D1 `WD` without the atom bound, as used by the record
headline `coherent_fixed_point` (which dropped the mandate's `hB`). "Consistent with `D`" is read
through `worldOf` (atoms `≥ B` read `false`), so a stage sentence outside the bound constrains
nothing (`{∼atom B}`) or everything (`{atom B}`): the record's `hW` then holds, or fails,
for a reason unrelated to the satisfiability of `D`. The theorem stays true (it is about finite
worlds) and its `PCWorld` form carries `hB`; this probe only makes the docstring caveat on `WD`
("meaningful under `hB`") concrete. Not imported by the library.
-/

namespace Cleanroom.Bli.BliCoherentMm.AuditR1Adv

open LogicalInduction LO.Propositional BoolPCWorld Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliOverlay

/-- A stage `{∼atom B}` outside the bound constrains nothing: every finite world over `B` atoms
is "consistent" with it. -/
theorem WD_neg_atom_bound_eq_univ (B : ℕ) :
    WD ({∼ Formula.atom B} : Finset Sentence) B = Finset.univ := by
  ext u
  simp only [Finset.mem_univ, iff_true]
  rw [mem_WD]
  intro φ hφ
  rw [Finset.mem_singleton] at hφ
  subst hφ
  simp [worldOf, BoolPCWorld.toPCWorld, FiniteWorld.toBoolPCWorld]

/-- Dually, no finite world over `B` atoms is "consistent" with `{atom B}`, although `atom B` is
satisfiable: `hW` fails for the wrong reason. -/
theorem not_mem_WD_atom_bound (B : ℕ) (u : FiniteWorld B) :
    u ∉ WD ({Formula.atom B} : Finset Sentence) B := by
  intro hu
  rw [mem_WD] at hu
  have := hu _ (Finset.mem_singleton_self _)
  simp [worldOf, BoolPCWorld.toPCWorld, FiniteWorld.toBoolPCWorld] at this

end Cleanroom.Bli.BliCoherentMm.AuditR1Adv

import Cleanroom.Decision.DpWorldsJb
import Mathlib.Data.Finset.Grade

/-!
# dp-worlds-jb — audit round 2, fidelity lens: probes

Not imported by the library. Evidence for non-blocking notes only (no blocking issue was found).

* **Probe A (ledger row `worldJω_equiv_atoms`, Witness cell).** The ledger says the equivalence
  `World (Jω E) ≃ {b // IsAtom b}` on a countable algebra is witnessed only on the empty side
  (`Dy`, both sides empty) and that "any finite algebra would do" for the inhabited side. It does:
  on `Finset (Fin 3)` (finite, hence countable) the equivalence is inhabited on both sides, and
  `World (Jω (Finset (Fin 3)))` has exactly three elements — v2 §0's "on a finite algebra worlds
  are just the atoms", now as an instance of the package's own theorem.
* **Probe B (`rigid_eq_true_iff`, the `hac`-guarded form).** The mandate's `hac` version is a
  one-line weakening of the shipped identity, so shipping (ii) without `hac` loses nothing.
-/

namespace Cleanroom.Decision.DpWorldsJb.AuditR2

open Cleanroom.Decision.DpWorldsJb Finset

noncomputable section

open Classical

/-! ## Probe A -/

/-- `Finset (Fin 3)` is countable (it is finite). -/
instance : Countable (Finset (Fin 3)) := Finite.to_countable

/-- The atom `{0}` of `Finset (Fin 3)`. -/
theorem probeA_isAtom_singleton (i : Fin 3) : IsAtom ({i} : Finset (Fin 3)) :=
  Finset.isAtom_singleton i

/-- `World (Jω (Finset (Fin 3)))` is inhabited: the atom world at `{0}`. -/
theorem probeA_world_nonempty : Nonempty (World (Jω (Finset (Fin 3)))) :=
  ⟨atomWorld _ {0} (probeA_isAtom_singleton 0)⟩

/-- The equivalence of the ledger row, instantiated on a countable algebra **with** atoms. -/
def probeA_equiv : World (Jω (Finset (Fin 3))) ≃ {b : Finset (Fin 3) // IsAtom b} :=
  worldJω_equiv_atoms

/-- The atoms of `Finset (Fin 3)` are exactly the singletons. -/
theorem probeA_atoms_eq_singletons (b : Finset (Fin 3)) : IsAtom b ↔ ∃ i, b = {i} :=
  Finset.isAtom_iff

/-- So the `Jω`-worlds of the three-atom algebra are in bijection with `Fin 3`: v2 §0's "worlds are
just the atoms" on a finite algebra, as an instance of `worldJω_equiv_atoms`. -/
def probeA_worlds_equiv_fin3 : World (Jω (Finset (Fin 3))) ≃ Fin 3 :=
  worldJω_equiv_atoms.trans
    { toFun := fun b => Classical.choose ((probeA_atoms_eq_singletons b.1).1 b.2)
      invFun := fun i => ⟨{i}, probeA_isAtom_singleton i⟩
      left_inv := fun b => by
        apply Subtype.ext
        exact (Classical.choose_spec ((probeA_atoms_eq_singletons b.1).1 b.2)).symm
      right_inv := fun i => by
        have h := Classical.choose_spec
          ((probeA_atoms_eq_singletons ({i} : Finset (Fin 3))).1 (probeA_isAtom_singleton i))
        exact (Finset.singleton_inj.1 h).symm }

/-! ## Probe B -/

/-- The `hac`-guarded (ii) of the mandate is the shipped identity with an unused hypothesis. -/
theorem probeB_rigid_eq_true_iff_of_ac {W Ω : Type*} [Fintype W] [Fintype Ω] [DecidableEq W]
    [DecidableEq Ω] (π : W → Ω) (μ μa : Dist W) (u : W → ℝ)
    (_hac : ∀ ω, 0 < push π μa.p ω → 0 < push π μ.p ω) :
    (∀ X : Finset Ω, 0 < mass (push π μa.p) X → rigidV π μ.p μa.p u X = coarseV π μa.p u X) ↔
      ∀ ω, 0 < push π μa.p ω → coarseV π μa.p u {ω} = coarseV π μ.p u {ω} :=
  rigid_eq_true_iff π μ μa u

end

end Cleanroom.Decision.DpWorldsJb.AuditR2

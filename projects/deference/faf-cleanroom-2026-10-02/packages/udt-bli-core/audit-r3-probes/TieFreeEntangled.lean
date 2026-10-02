import Cleanroom.Bli.UdtBliCore

/-!
# `udt-bli-core` · audit round 3, adversarial lens · probe: a dependency that cancels, exhibited

Not part of the library (never imported by it). Elaborated with `scripts/lean-check`.

Mandate T10 asked for "`NoCrossBranch` without `CoordinationFree` (a dependency that cancels)".
Repair round 2 delivers it as `Xor.noCrossBranch_without_coordinationFree`, a non-existence
statement (no structure is coordination-free), proved through `LocalUtility`'s failure. This probe
exhibits the dependency itself, on the refutation-of-record prior `tfPrior`:

1. `tfEntangled`: an explicit `Entangled` structure with `dep _ = {T2}` — `T1`'s utility reads
   `T2`'s point — and `depP _ = ∅`; the structure type is inhabited.
2. `T2_mem_dep_T1`: **every** `Entangled` structure on `tfPrior` has `T2 ∈ dep T1` (the outcomes
   `(T1, true, true)` and `(T1, true, false)` have utilities `4` and `1`).
3. `cancels`: `NoCrossBranch` holds (`TieFree.noCrossBranch`), `tfEntangled` is not
   coordination-free, and no structure is — the mandate's sentence with the structure in hand.
-/

namespace AuditR3

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliCore.FiniteBLIPrior
  Finset

namespace TfEnt

/-- Every policy-level cell of `tfPrior` has mass `1/8`. -/
lemma cellMass_eq (T : ↥twoTables) (π : Policy twoTables Bool) : tfPrior.cellMass T π = 1 / 8 := by
  rw [TieFree.policy_eq_tfPP π]
  rcases eq_T1_or_T2 T with rfl | rfl <;>
  · unfold FiniteBLIPrior.cellMass tfPrior
    rw [handPrior_massOf]
    simp only [handPrior, massOf, TieFree.tfPP_eq_iff]
    cases π T1 <;> cases π T2 <;>
    · norm_num [tfMass, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2,
        T2_ne_T1, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]

/-- An `Entangled` structure on `tfPrior`: every branch may read `T2`'s point, no branch's
probability reads any point. -/
def tfEntangled : tfPrior.Entangled where
  dep := fun _ => {T2}
  depP := fun _ => ∅
  U_sound := by
    rintro ⟨i, b, c⟩ ⟨i', b', c'⟩ hs hp
    have hs' : twoState i = twoState i' := hs
    have hc : tfPP (i, b, c) T2 = tfPP (i', b', c') T2 :=
      hp T2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [TieFree.tfPP_T2, TieFree.tfPP_T2] at hc
    simp only at hc
    subst hc
    fin_cases i <;> fin_cases i'
    · have hb : tfPP ((0 : Fin 2), b, c) T1 = tfPP ((0 : Fin 2), b', c) T1 :=
        hp T1 (Finset.mem_insert_self _ _)
      rw [TieFree.tfPP_T1, TieFree.tfPP_T1] at hb
      simp only at hb
      subst hb
      rfl
    · exact absurd hs' T1_ne_T2
    · exact absurd hs' T2_ne_T1
    · rfl
  mass_sound := by
    intro T π π' _
    rw [cellMass_eq, cellMass_eq, TieFree.policyMass_eq, TieFree.policyMass_eq]

/-- Every `Entangled` structure on `tfPrior` has `T2 ∈ dep T1`. -/
theorem T2_mem_dep_T1 (E : tfPrior.Entangled) : T2 ∈ E.dep T1 := by
  by_contra hno
  have hU := E.U_sound ((0 : Fin 2), true, true) ((0 : Fin 2), true, false) rfl (by
    intro T' hT'
    change T' ∈ insert T1 (E.dep T1) at hT'
    have hT'1 : T' = T1 := by
      rcases Finset.mem_insert.mp hT' with h | h
      · exact h
      · rcases eq_T1_or_T2 T' with h1 | h2
        · exact h1
        · rw [h2] at h
          exact absurd h hno
    subst hT'1
    show tfPP ((0 : Fin 2), true, true) T1 = tfPP ((0 : Fin 2), true, false) T1
    rw [TieFree.tfPP_T1, TieFree.tfPP_T1])
  have h4 : tfPrior.U ((0 : Fin 2), true, true) = 4 := by
    show tfU ((0 : Fin 2), true, true) = 4
    simp [tfU]
  have h1 : tfPrior.U ((0 : Fin 2), true, false) = 1 := by
    show tfU ((0 : Fin 2), true, false) = 1
    simp [tfU]
  rw [h4, h1] at hU
  norm_num at hU

/-- The mandate's T10 sentence with the structure exhibited: `NoCrossBranch` holds, the
structure type is inhabited, the exhibited structure is not coordination-free, and none is. -/
theorem cancels :
    tfPrior.NoCrossBranch ∧ Nonempty tfPrior.Entangled ∧
      ¬ tfPrior.CoordinationFree tfEntangled ∧
      ∀ E : tfPrior.Entangled, ¬ tfPrior.CoordinationFree E :=
  ⟨TieFree.noCrossBranch, ⟨tfEntangled⟩,
    fun h => T2_ne_T1 (Finset.mem_singleton.mp ((h T1).1 (Finset.mem_singleton_self _))),
    fun E hE => T2_ne_T1 (Finset.mem_singleton.mp ((hE T1).1 (T2_mem_dep_T1 E)))⟩

end TfEnt

end AuditR3

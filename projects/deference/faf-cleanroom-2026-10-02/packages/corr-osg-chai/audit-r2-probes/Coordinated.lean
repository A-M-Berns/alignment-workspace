import Cleanroom.Corrigibility.CorrOsgChai.POOSG

/-!
# Audit r2 (adversarial) probe — `Coordinated` is strictly larger than `Independent`

The shared coin `ν(·) = ½ δ_(0,0) + ½ δ_(1,1)` (both players receive the same fair coin) is a
coordinated garbling (a two-term mixture of the constant independent garblings `δ_(0,0)` and
`δ_(1,1)`) but not an independent one (its mass on `(0,1)` is `0` while its masses on `(0,0)`
and `(1,1)` are `½`, which no product `νH ⊗ νA` can do). So the "coordinated" clause of
Theorem 4.7 (⇐) (`optValue_withObs_le_of_moreInformative`) is a genuine generalisation of the
independent case — the hypothesis class the theorem is proved for is not secretly the
independent class. (Every `MoreInformative` inhabitant in the package itself goes through
`Independent.coordinated`; this probe is the only non-independent coordinated instance.)
Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrOsgChai.AuditR2

open FactoredSpaces Cleanroom.Corrigibility.CorrOsgChai
open Finset hiding expect

/-- The shared coin on `Fin 2 × Fin 2`: mass `1/2` on `(0,0)` and on `(1,1)`. -/
noncomputable def coin : Distr (Fin 2 × Fin 2) where
  mass p := if p.1 = p.2 then 1 / 2 else 0
  nonneg p := by split_ifs <;> norm_num
  sum_eq_one := by
    rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp
    norm_num

/-- The constant garbling from the trivial observation pair to the shared coin. -/
noncomputable def coinGarbling : ObsGarbling Unit Unit (Fin 2) (Fin 2) := fun _ => coin

/-- The constant garbling to a Dirac is independent (both kernels Dirac). -/
lemma const_delta_independent (a b : Fin 2) :
    Independent (fun _ : Unit × Unit => Distr.delta (a, b)) := by
  refine ⟨fun _ => Distr.delta a, fun _ => Distr.delta b, fun _ _ oH' oA' => ?_⟩
  simp only [Distr.delta_mass, Prod.mk.injEq]
  by_cases h1 : oH' = a <;> by_cases h2 : oA' = b <;> simp [h1, h2]

/-- The shared coin is a coordinated garbling. -/
theorem coinGarbling_coordinated : Coordinated coinGarbling := by
  refine ⟨2, ![1 / 2, 1 / 2],
    ![fun _ => Distr.delta ((0 : Fin 2), (0 : Fin 2)), fun _ => Distr.delta ((1 : Fin 2), (1 : Fin 2))],
    ⟨fun i => by fin_cases i <;> simp, by simp [Fin.sum_univ_two]; norm_num⟩, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact const_delta_independent 0 0
    · exact const_delta_independent 1 1
  · rintro o ⟨a, b⟩
    fin_cases a <;> fin_cases b <;>
      simp [coinGarbling, coin, Fin.sum_univ_two, Distr.delta_mass]

/-- The shared coin is not an independent garbling. -/
theorem coinGarbling_not_independent : ¬ Independent coinGarbling := by
  rintro ⟨νH, νA, h⟩
  have h00 := h () () 0 0
  have h11 := h () () 1 1
  have h01 := h () () 0 1
  simp only [coinGarbling, coin] at h00 h11 h01
  simp at h00 h11 h01
  rcases h01 with h0 | h0
  · simp only [h0, zero_mul] at h00
    norm_num at h00
  · simp only [h0, mul_zero] at h11
    norm_num at h11

end Cleanroom.Corrigibility.CorrOsgChai.AuditR2

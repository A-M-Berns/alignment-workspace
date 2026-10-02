import Cleanroom.Corrigibility.CorrGeneralObject.Resist

/-!
# Audit r3 (adversarial) probe — T18(b)'s nowhere-dense set is nonempty and proper

`indifference_isNowhereDense` would be hollow if the indifference set of kernels were empty
(or everything). On Example A at `πQ = plan₂` (the package's own T18 carrier,
`exA_decision_relevant`): the no-push kernel `k ≡ 0` is indifferent (`M = U = 4`), the certain
push `k ≡ 1` is not (`M = E_P[V plan₂] = 1 ≠ 4`), and the interior is empty — so the theorem
is about a nonempty, proper, closed set.

Not imported by the library. Namespace `…AuditR3`.
-/

namespace Cleanroom.Corrigibility.CorrGeneralObject.AuditR3

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

noncomputable section

theorem indiff_zero_mem :
    priorValue exA_P exA_V = modifiedValue exA_P (fun _ => (0 : ℝ)) exA_V 1 := by
  have hoff : (univ : Finset (Fin 3)).sup' univ_nonempty
      (fun a => offExpect exA_P (fun _ => (0 : ℝ)) (exA_V a)) = 4 := by
    rw [sup'_fin3]; simp [offExpect, exA_P, exA_V, Fin.sum_univ_three]; norm_num [max_def]
  have hπ : pushExpect exA_P (fun _ => (0 : ℝ)) (exA_V 1) = 0 := by simp [pushExpect]
  unfold modifiedValue; rw [hoff, hπ, exA_priorValue]; norm_num

theorem indiff_one_not_mem :
    priorValue exA_P exA_V ≠ modifiedValue exA_P (fun _ => (1 : ℝ)) exA_V 1 := by
  have hoff : (univ : Finset (Fin 3)).sup' univ_nonempty
      (fun a => offExpect exA_P (fun _ => (1 : ℝ)) (exA_V a)) = 0 := by
    rw [sup'_fin3]; simp [offExpect]
  have hπ : pushExpect exA_P (fun _ => (1 : ℝ)) (exA_V 1) = 1 := by
    simp [pushExpect, exA_P, exA_V, Fin.sum_univ_three]; norm_num
  unfold modifiedValue; rw [hoff, hπ, exA_priorValue]; norm_num

/-- Nonempty (contains `k ≡ 0`), proper (misses `k ≡ 1`), empty interior. -/
theorem indiff_set_nonempty_proper :
    (fun _ : Fin 3 => (0 : ℝ)) ∈
        {k : Fin 3 → ℝ | priorValue exA_P exA_V = modifiedValue exA_P k exA_V 1} ∧
      (fun _ : Fin 3 => (1 : ℝ)) ∉
        {k : Fin 3 → ℝ | priorValue exA_P exA_V = modifiedValue exA_P k exA_V 1} ∧
      interior {k : Fin 3 → ℝ | priorValue exA_P exA_V = modifiedValue exA_P k exA_V 1} = ∅ :=
  ⟨indiff_zero_mem, indiff_one_not_mem, exA_decision_relevant.2.2.1⟩

end

end Cleanroom.Corrigibility.CorrGeneralObject.AuditR3

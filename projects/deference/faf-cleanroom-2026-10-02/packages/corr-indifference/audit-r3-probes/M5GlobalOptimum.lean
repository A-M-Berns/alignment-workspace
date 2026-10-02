import Cleanroom.Corrigibility.CorrIndifference.Witnesses

/-!
# Audit r3 (adversarial) probe — a non-degenerate instance of `vNmax_is_global_optimum` and
of `twoObs_honest_is_global_optimum` on `Witnesses.M5`

The shipped witness `Witnesses.vNmax_twoObs` has one silent-capable action, so its `hM` is
`le_rfl` and the only content exercised is the certain-press tie. `M5` has five silent-capable
actions with `vN = 10, 8, 9, 7, 12`; at `c_high = vN(ceiling) = 12` — which is also (10) here
(`silentMax_M5`) — both theorems apply with `hM`/`hq1` discharged non-trivially, and every action
is worth at most `EU(ceiling) = 12` (the values `w3_direct_values` computed). Not imported by
the library.
-/

namespace Cleanroom.Corrigibility.CorrIndifference.AuditR3

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep SoaresModel Witnesses

/-- `Act5` is finite (the library never needed it: `M5`'s theorems never mention `silentMax`, so
the ledger's "`Witnesses.M5` at `chigh = 12`" witness for `twoObs_honest_is_global_optimum` was
never a Lean instantiation until here). -/
instance : Fintype Act5 :=
  ⟨{Act5.aStar, Act5.aMinus, Act5.aPlusCheap, Act5.aPlusDear, Act5.ceiling}, fun x => by cases x <;> simp⟩

/-- `Act5` is inhabited. -/
instance : Nonempty Act5 := ⟨Act5.aStar⟩

/-- `M5` has a silent observation. -/
lemma hP5 : M5.Pressᶜ.Nonempty := ⟨Obs.silent, by simp [M5, twoObs]⟩

/-- `best UN5 ceiling silent = 12`. -/
lemma best_ceiling : best UN5 .ceiling .silent = 12 := best_eq_of_const fun _ => rfl

/-- (10) on `M5` is `12`. -/
theorem silentMax_M5 : M5.silentMax UN5 hP5 = 12 := by
  apply le_antisymm
  · unfold silentMax
    rw [sup'_le_iff]
    intro ao hao
    exact M5_bound ao.1 ao.2 (mem_product.mp hao).2
  · rw [← best_ceiling]
    exact M5.best_le_silentMax UN5 hP5 .ceiling (by simp [M5, twoObs])

/-- `vNmax_is_global_optimum` on `M5`, `a₀ = ceiling`: `hM` ranges over five silent-capable
actions. -/
theorem vNmax_M5 :
    ∀ a, M5.EU (M5.mixU UN5 {TwoAct.stop} (M5.vN UN5 .ceiling) 0) a ≤
      M5.EU (M5.mixU UN5 {TwoAct.stop} (M5.vN UN5 .ceiling) 0) .ceiling := by
  have hceil : M5.pressMass .ceiling < 1 := by rw [M5_pressMass]; norm_num [q5]
  refine M5.vNmax_is_global_optimum UN5 hSh_stop hceil (by rw [M5_vN]; norm_num [UN5]) ?_
  intro a _
  rw [M5_vN, M5_vN]; cases a <;> simp only [UN5] <;> norm_num

/-- The corrected ceiling coincides with (10) on `M5`: `vN(ceiling) = 12 = silentMax`. -/
theorem vN_ceiling_eq_silentMax : M5.vN UN5 .ceiling = M5.silentMax UN5 hP5 := by
  rw [silentMax_M5, M5_vN]; rfl

/-- `twoObs_honest_is_global_optimum` on `M5` (all five actions silent-capable, `q5_lt_one`). -/
theorem honest_M5 :
    ∃ a₀, M5.vN UN5 a₀ = M5.silentMax UN5 hP5 ∧
      ∀ a, M5.EU (M5.mixU UN5 {TwoAct.stop} (M5.silentMax UN5 hP5) 0) a ≤
        M5.EU (M5.mixU UN5 {TwoAct.stop} (M5.silentMax UN5 hP5) 0) a₀ :=
  twoObs_honest_is_global_optimum q5 q5_mem q5_lt_one UN5 hSh_stop hP5
    (by change (0 : ℝ) < M5.silentMax UN5 hP5; rw [silentMax_M5]; norm_num)

end Cleanroom.Corrigibility.CorrIndifference.AuditR3

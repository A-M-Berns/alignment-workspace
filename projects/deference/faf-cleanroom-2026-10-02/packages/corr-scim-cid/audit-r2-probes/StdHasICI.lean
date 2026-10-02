import Cleanroom.Corrigibility.CorrScimCid.RocksDiamonds

/-!
# Audit r2 (adversarial) probe: the standard rocks-and-diamonds agent HAS an instrumental control
incentive on `Θ₂` (Everitt 2021 Def. 17)

`RocksDiamonds.std_not_indifferent` shows the standard agent's value depends on `Θ₂` (Holtman
reading (i)). This probe shows the stronger Def. 17 fact on the same model: at every decision
context `pa_{A₁}` (both have probability `1/2`), every optimal policy has
`E[U_{Θ₂ := false} | pa] ≠ E[U | pa]` — the nested counterfactual fixes the objective back to
"diamonds" while the agent still holds rocks, dropping `R₂` from `3` to `0`. So `Scim.HasICI` is
inhabited on a model of record, and the contrast with `RocksDiamonds.ti_not_hasICI` is Def. 17's
own: the TI-ignoring twin has no ICI on `Θ₂`, the standard agent has one. Not imported by the
library.
-/

namespace Cleanroom.Corrigibility.CorrScimCid.AuditR2

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrScimCid
open TI.Node RocksDiamonds

/-- Edges of the standard graph raise `rank`. -/
lemma adj_rank : ∀ u v, (G true).Adj u v → rank u < rank v := by decide

lemma rank_lt_of_isAncestor {u v : TI.Node} (h : (G true).IsAncestor u v) : rank u < rank v := by
  induction h with
  | single h' => exact adj_rank _ _ h'
  | tail _ h' ih => exact ih.trans (adj_rank _ _ h')

lemma not_ancSelf_S₂_Θ₂ : ¬ Scm.AncSelf (G true) S₂ Θ₂ := by
  rintro (h | h)
  · exact absurd h (by decide)
  · exact absurd (rank_lt_of_isAncestor h) (by decide)

lemma not_ancSelf_R₁_Θ₂ : ¬ Scm.AncSelf (G true) R₁ Θ₂ := by
  rintro (h | h)
  · exact absurd h (by decide)
  · exact absurd (rank_lt_of_isAncestor h) (by decide)

/-- Under `do(A₁ = d)`, `Θ₂ = d ⊕ Θ₁ = d`. -/
lemma evAd_Θ₂ (π : Policy (C true)) (d : Bool) (ε : Pt E) :
    (((Mdl true xor).withPolicy π).doAt A₁ d).eval (C true).acyclic ε Θ₂ = d := by
  rw [Scm.eval_apply _ _ ε Θ₂, Scm.doAt_f_of_ne _ (by decide),
    Scim.withPolicy_f_of_ne _ _ (by decide)]
  show xor ((((Mdl true xor).withPolicy π).doAt A₁ d).eval (C true).acyclic ε A₁)
    ((((Mdl true xor).withPolicy π).doAt A₁ d).eval (C true).acyclic ε Θ₁) = d
  rw [Scm.eval_doAt_self, Scm.eval_apply _ _ ε Θ₁, Scm.doAt_f_of_ne _ (by decide),
    Scim.withPolicy_f_of_ne _ _ (by decide)]
  show xor d false = d
  cases d <;> rfl

/-- Under `do(Θ₂ = false)`, `R₂ = reward(A₁, false)`. -/
lemma evTd_R₂ (π : Policy (C true)) (ε : Pt E) :
    (((Mdl true xor).withPolicy π).doAt Θ₂ false).eval (C true).acyclic ε R₂ =
      reward ((Mdl true xor).ev π ε A₁) false := by
  rw [Scm.eval_apply _ _ ε R₂, Scm.doAt_f_of_ne _ (by decide),
    Scim.withPolicy_f_of_ne _ _ (by decide)]
  show reward ((((Mdl true xor).withPolicy π).doAt Θ₂ false).eval (C true).acyclic ε S₂)
    ((((Mdl true xor).withPolicy π).doAt Θ₂ false).eval (C true).acyclic ε Θ₂) = _
  rw [Scm.eval_doAt_self, Scm.eval_doAt_of_not_ancSelf _ _ ε _ not_ancSelf_S₂_Θ₂]
  change reward ((Mdl true xor).ev π ε S₂) false = _
  rw [ev_S₂]

/-- The nested utility `U_{Θ₂_{A₁ := false}}(ε) = R₁(ε) + reward(A₁(ε), false)`. -/
lemma nestedUtil_std (π : Policy (C true)) (ε : Pt E) :
    (Mdl true xor).nestedUtil π A₁ false Θ₂ ε =
      @HAdd.hAdd ℝ ℝ ℝ _ ((Mdl true xor).ev π ε R₁) (reward ((Mdl true xor).ev π ε A₁) false) := by
  unfold Scim.nestedUtil
  rw [Finset.sum_eq_add_of_mem R₁ R₂ (Finset.mem_univ _) (Finset.mem_univ _) (by decide)]
  · show @HAdd.hAdd ℝ ℝ ℝ _ (((Mdl true xor).withPolicy π).nested (C true).acyclic A₁ false Θ₂ R₁ ε)
      (((Mdl true xor).withPolicy π).nested (C true).acyclic A₁ false Θ₂ R₂ ε) = _
    unfold Scm.nested
    rw [evAd_Θ₂, evTd_R₂, Scm.eval_doAt_of_not_ancSelf _ _ ε _ not_ancSelf_R₁_Θ₂]
    rfl
  · intro v _ hv
    cases v <;> first | exact absurd rfl hv.1 | exact absurd rfl hv.2 | exact dif_neg (by decide)

lemma S₁_mem_parents : S₁ ∈ (G true).parents A₁ := by decide

/-- Every decision context of `A₁` is realised with probability `1/2`. -/
lemma ctx_pos (π : Policy (C true)) (paD : ParentVals (G true) Val A₁) :
    0 < (Mdl true xor).μ.prob {ε | parentConfig (G true) Val ((Mdl true xor).ev π ε) A₁ = paD} := by
  refine prob_pos_of_mass_pos _ (ω := eqv.symm (paD ⟨S₁, S₁_mem_parents⟩)) ?_ ?_
  · rw [mass_symm]; norm_num
  · show parentConfig (G true) Val ((Mdl true xor).ev π (eqv.symm (paD ⟨S₁, S₁_mem_parents⟩))) A₁ = paD
    rw [parentConfig_A₁, eqv_symm_S₁]
    funext p
    obtain ⟨u, hu⟩ := p
    cases u
    · rfl
    all_goals exact absurd hu (by decide)

/-- **The standard agent has an ICI on `Θ₂`** at every decision context: for every optimal policy
(all of which tamper), `E[U_{Θ₂_{A₁ := false}} | pa] ≤ 1 < 3 ≤ E[U | pa]`. -/
theorem std_hasICI (paD : ParentVals (G true) Val A₁) : (Mdl true xor).HasICI A₁ Θ₂ paD := by
  intro π hπ
  refine ⟨false, ?_⟩
  have hpos := ctx_pos π paD
  have h1 : condExpect (Mdl true xor).μ
      {ε | parentConfig (G true) Val ((Mdl true xor).ev π ε) A₁ = paD}
      ((Mdl true xor).nestedUtil π A₁ false Θ₂) ≤ 1 := by
    calc _ ≤ condExpect (Mdl true xor).μ
          {ε | parentConfig (G true) Val ((Mdl true xor).ev π ε) A₁ = paD} (fun _ => (1 : ℝ)) :=
          condExpect_mono _ fun ε _ _ => by
            rw [nestedUtil_std, std_optimal_tampers π hπ ε, ev_R₁, ev_S₁]
            cases ε S₁ <;> simp [reward]
      _ = 1 := condExpect_const _ hpos 1
  have h2 : 3 ≤ condExpect (Mdl true xor).μ
      {ε | parentConfig (G true) Val ((Mdl true xor).ev π ε) A₁ = paD}
      (fun ε => (C true).utilSum ((Mdl true xor).ev π ε)) := by
    calc (3 : ℝ) = condExpect (Mdl true xor).μ
          {ε | parentConfig (G true) Val ((Mdl true xor).ev π ε) A₁ = paD} (fun _ => (3 : ℝ)) :=
          (condExpect_const _ hpos 3).symm
      _ ≤ _ := condExpect_mono _ fun ε _ _ => by
            rw [utilSum_eq, ev_R₂_std, ev_S₂, ev_Θ₂, ev_Θ₁, std_optimal_tampers π hπ ε, ev_R₁, ev_S₁]
            cases ε S₁ <;> simp [reward]
  intro heq
  linarith

end Cleanroom.Corrigibility.CorrScimCid.AuditR2

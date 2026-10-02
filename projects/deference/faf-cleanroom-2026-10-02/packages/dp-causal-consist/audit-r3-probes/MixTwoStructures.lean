import Cleanroom.Decision.DpCausalConsist.MixtureWitness

/-!
# Audit r3 (adversarial) probe: a *two-structure* instance of `tcdt_mix_iff_tedt`

`MixtureWitness.lean` (repair round 2) ships `direct_tcdt_mix_iff_tedt_LMK` as the "literal
instance" of the mixture corollary and grades it N+. Its prior is `FinDistr.pure 0` on `Fin 1`: a
point mass, so the mixture is a single component and nothing of the mixing (`π.sum_one`, two
structures with different parent sets both discharging `hpa`) is exercised — the analogue of a
constant sequence for an asymptotic theorem. This probe builds the non-degenerate instance: the
fair prior over the two temporal structures `sLMK` (`ℓ → m`, parent cells the lesion cells,
discharged by `s1Fam_preQuery_ell`) and `sColl` (`pa(m) = ∅`), whose DAGs are shown to differ.
Not imported by the library.
-/

namespace Cleanroom.Decision.DpCausalConsist

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Decision.DpCalibration
  FactoredSpaces Finset

/-- The two structures: `sLMK` (`ℓ → m`, `ℓ → k`, `m → k`) and `sColl` (`ℓ → k ← m`). -/
noncomputable def twoStruct : Fin 2 → CausalStructure (fun _ : Fin 3 => Bool)
  | 0 => sLMK
  | 1 => sColl

/-- The fair prior over the two structures. -/
noncomputable def fairPrior : FinDistr ℝ (Fin 2) := FinDistr.uniform

/-- Both weights are `1/2`: a genuine mixture, no component null. -/
theorem fairPrior_w (i : Fin 2) : fairPrior.w i = 1 / 2 := by
  simp [fairPrior, FinDistr.uniform, Fintype.card_fin]

/-- The two structures have different DAGs: `ℓ → m` is an edge of `gLMK` and not of `gColl`. -/
theorem twoStruct_G_ne : (twoStruct 0).G ≠ (twoStruct 1).G := by
  show gLMK ≠ gColl
  intro h
  have h1 : gLMK.Adj 0 1 := by decide
  rw [h] at h1
  exact absurd h1 (by decide)

/-- **A two-structure instance of `tcdt_mix_iff_tedt`** on the direct-effect tree at label `1/2`:
the fair prior over `sLMK` and `sColl`, every hypothesis as in `direct_tcdt_iff_tedt_LMK` /
`direct_tcdt_iff_tedt`, for every supervenient payoff. -/
theorem direct_tcdt_mix_two_iff_tedt (u : W3 → ℚ) :
    TCdtAt (fun _ => directState u) s1ActEv procHalf ()
        (fun a => mixState fairPrior fun i => cfG (twoStruct i) 1 (fun x => (u x : ℝ)) (id a))
      ↔ TEdtAt (fun _ => directState u) s1ActEv procHalf () := by
  refine tcdt_mix_iff_tedt s1Obs s1ActEv (fun _ => directState u)
    (s1Fam_recordsFor _ _ _ _ _ _ u procHalf) (nu_univ_pos procHalf _)
    (s1State_strict _ _ _ _ _ _ u procHalf) 1 id (fun _ => rfl) fairPrior twoStruct
    (fun i => by
      rw [directTree_toDistr]
      match i with
      | 0 => exact sLMK_isFor
      | 1 => exact sColl_isFor)
    (fun i => match i with
      | 0 => fun c => by
        have hc : parentCell (twoStruct 0) 1 c
            = Finset.univ.filter fun x : W3 => x 0 = c ⟨0, zero_mem_parents_LMK⟩ :=
          parentCell_sLMK c
        rw [hc]
        exact s1Fam_preQuery_ell _ _ _ _ _ _ u procHalf _
      | 1 => fun c => by
        have hc : parentCell (twoStruct 1) 1 c = Finset.univ :=
          parentCell_eq_univ_of_parents_empty sColl 1 gColl_parents.2.1 c
        rw [hc]
        exact preQuery_univ s1Obs procHalf (directTree u) ())
    u (s1Fam_payoff _ _ _ _ _ _ u) ?_
  rw [directState_aPlus, Finset.inter_univ]
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ
    (fun a => (mixState fairPrior
      fun i => cfG (twoStruct i) 1 (fun x => (u x : ℝ)) (id a)).V (s1ActEv () a))
    Finset.univ_nonempty
  exact ⟨a, (mem_argmaxAll _ a).mpr fun b => ha b (Finset.mem_univ b)⟩

end Cleanroom.Decision.DpCausalConsist

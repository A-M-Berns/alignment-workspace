import Cleanroom.Udt.UdtSupercondition

/-!
# udt-supercondition — audit round 2, lens `fidelity`: probes

Not imported by the library. Two probes about T11's fixed-structure definition
`CrossCoherentVia` (SC Def 12.2 read with `(Ā, κ)` fixed):

* Probe A: its anticipation clause (`BridgeCalibrated as ci`) does not mention `Xj` — the
  witness `as` for `(Xi, Xj)` is a witness for every `Xj'` that satisfies clause (1). SC's gloss
  "Condition (2) ensures `dᵢ` anticipated `dⱼ`'s beliefs" is not what clause (2) says.
* Probe B: the pinned cross-ontology analogue of Def 12.1 / `CoherentVia` — `as` is
  `Ĉ`-calibrated and `Xj` *is* one of the anticipated beliefs, `Xj = κ_{ā₀}` on a positive atom —
  implies clause (1) (bounded density `1/Xi(ā₀)`, range condition automatic), hence
  `CrossCoherentVia`. So a `CrossCoherentAt`-style definition would be the cross-ontology
  counterpart of `CoherentVia → Downstream`, and is what a dependent needing "`dᵢ` anticipated
  `dⱼ`'s beliefs" should import.
-/

namespace Cleanroom.Udt.UdtSupercondition

open scoped ENNReal
open Set

variable {Ωi Ωj : Type} [Countable Ωi] [Countable Ωj] (ci : CommonInfo Ωi Ωj) (Xi : PMF Ωi)

omit [Countable Ωi] [Countable Ωj] in
/-- Probe A: the anticipation clause of `CrossCoherentVia` does not see `Xj`. -/
theorem crossCoherentVia_indep_Xj (Xj Xj' : PMF Ωj) (as : AnticipationStructure Xi Ωj)
    (h : CrossCoherentVia ci Xi Xj as) (h1 : ∃ m : CondModel Xi Xj', Compatible m ci) :
    CrossCoherentVia ci Xi Xj' as :=
  ⟨h1, h.2⟩

/-- The pinned cross-ontology analogue of Def 12.1: `as` is `Ĉ`-calibrated and `Xj = κ_{ā₀}` for
a positive atom `ā₀`. -/
def CrossCoherentAt (Xj : PMF Ωj) (as : AnticipationStructure Xi Ωj) : Prop :=
  BridgeCalibrated as ci ∧ ∃ ā₀ : as.A, 0 < (Xi.map as.a) ā₀ ∧ Xj = as.κ ā₀

/-- Probe B: the pinned variant implies clause (1) of Def 12.2 with bound `1/Xi(ā₀)`, hence
`CrossCoherentVia` — the cross-ontology counterpart of `CoherentVia → Downstream`. -/
theorem CrossCoherentAt.crossCoherentVia (Xj : PMF Ωj) (as : AnticipationStructure Xi Ωj)
    (h : CrossCoherentAt ci Xi Xj as) : CrossCoherentVia ci Xi Xj as := by
  obtain ⟨hb, ā₀, hpos, rfl⟩ := h
  refine ⟨?_, hb⟩
  rw [commonInfo_condModel_iff]
  refine ⟨⟨((Xi.map as.a) ā₀)⁻¹, ENNReal.inv_ne_top.2 hpos.ne', fun y => ?_⟩,
    fun y hy => hb.range as ci y hy⟩
  rw [CommonInfo.C₂_apply, CommonInfo.C₁_apply]
  have e := hb ā₀ y
  have hne : (Xi.map as.a) ā₀ ≠ 0 := hpos.ne'
  have hnt : (Xi.map as.a) ā₀ ≠ ⊤ := PMF.apply_ne_top _ _
  calc mass (as.κ ā₀) (ci.c' ⁻¹' {y})
      = mass (as.κ ā₀) (ci.c' ⁻¹' {y}) * (Xi.map as.a) ā₀ * ((Xi.map as.a) ā₀)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hne hnt, mul_one]
    _ = mass Xi (as.a ⁻¹' {ā₀} ∩ ci.c ⁻¹' {y}) * ((Xi.map as.a) ā₀)⁻¹ := by rw [e]
    _ ≤ mass Xi (ci.c ⁻¹' {y}) * ((Xi.map as.a) ā₀)⁻¹ :=
        mul_le_mul' (mass_mono _ inter_subset_right) le_rfl
    _ = ((Xi.map as.a) ā₀)⁻¹ * mass Xi (ci.c ⁻¹' {y}) := mul_comm _ _

end Cleanroom.Udt.UdtSupercondition

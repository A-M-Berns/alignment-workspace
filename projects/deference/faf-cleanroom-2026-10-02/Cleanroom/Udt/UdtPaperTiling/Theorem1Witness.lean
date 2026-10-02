import Cleanroom.Udt.UdtPaperTiling.Theorem1
import Cleanroom.Bli.UdtBliCore.WitnessLayers

/-!
# `udt-paper-tiling` · Theorem1Witness: Theorem 1 over a general procedure layer, and its failure
without fairness (T3's witnesses)

* `thm1_procLayer`: Theorem 1 over an arbitrary `ProcLayer` with a section `ι : Policy → Proc`
  (`eff (ι (eff p)) = eff p`): one application of `PolicyFair` (the mandate's shape probe).
* `thm1_fails_unfair`: on `udt-bli-core`'s `layerOf unfairU` (procedures `0` and `1` with the same
  effective behaviour, "written in C++"), the conclusion fails: `procEU 0 = 1 ≠ −1 = procEU 1`
  with both positive — the failure witness of record for Theorem 1 and for `udt-bli-tiling`'s U9.
  The imported `policyFair_fair` (N+) and `not_policyFair_unfair` (N−) are the fairness witnesses.
* `NoFair`: a three-line paper prior where, without fairness, a self-modifying policy is strictly
  preferred to every non-modifying one: `Act = {x, m}`, `𝒜^m = {m}`, `m̂ = x`, `mod m = ∅`, so
  `eff (m, x) = (x, x) = eff (x, x)` by the causal construction (`effCausal`); the environment
  pays `1` for choosing `(m, x)` and `0` for `(x, x)`. Policy Fairness fails and `(m, x)` beats
  `(x, x)`. Its `eff` is `CausalStructure.effCausal`, so the layer's `eff` hypotheses are grade (a).

Package `udt-paper-tiling` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Udt.UdtPaperTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {Act : Type} [Fintype Act]
  [DecidableEq Act] {P : FiniteBLIPrior 𝒮 m 𝒟 Act}

/-- **Theorem 1 over a general procedure layer**: with a section `ι` of `eff` on effective
behaviours, every positive procedure `p` whose non-modifying implementation `ι (eff p)` is positive
is exactly as good as it. One application of the hypothesis.
Source: `main.tex` 149–161, Theorem 1 (bli-paper-005); mandate §8 (the shape probe)
Kind: L
Fidelity: exact
Hyps: (a) `PolicyFair`, positivities, the section property -/
theorem thm1_procLayer (L : P.ProcLayer) (ι : Policy 𝒟 Act → L.Proc)
    (hι : ∀ p, L.eff (ι (L.eff p)) = L.eff p) (hF : P.PolicyFair L) (p : L.Proc)
    (hp : 0 < L.procMass p) (hE : 0 < L.procMass (ι (L.eff p))) :
    L.procEU p = L.procEU (ι (L.eff p)) :=
  hF p (ι (L.eff p)) (hι p).symm hp hE

/-- Every procedure of `layerOf u` has mass `1/3`.
Source: none: infrastructure (recomputed from `udt-bli-core`'s `WitnessLayers`)
Kind: L
Fidelity: n/a -/
lemma procMass_layerOf (u : Fin 3 → ℚ) (p : Fin 3) : (layerOf u).procMass p = 1 / 3 := by
  unfold FiniteBLIPrior.ProcLayer.procMass layerOf layerPrior
  rw [handPrior_massOf]
  simp only [handPrior]
  match p with
  | 0 =>
    simp only [massOf, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [fin3_01, fin3_02, fin3_12, fin3_01.symm, fin3_02.symm, fin3_12.symm]
  | 1 =>
    simp only [massOf, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [fin3_01, fin3_02, fin3_12, fin3_01.symm, fin3_02.symm, fin3_12.symm]
  | 2 =>
    simp only [massOf, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [fin3_01, fin3_02, fin3_12, fin3_01.symm, fin3_02.symm, fin3_12.symm]

/-- **Theorem 1's conclusion fails on the unfair layer**: procedures `0` and `1` behave identically,
both have mass `1/3`, and score `1` and `−1`. This is the failure witness of record for Theorem 1
(and for `udt-bli-tiling`'s U9); `not_policyFair_unfair` is the corresponding failure of the
hypothesis.
Source: bli-paper-004/005 ("unfair to punish agents for … being written in C++"); mandate T3
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem thm1_fails_unfair :
    (layerOf unfairU).eff (0 : Fin 3) = (layerOf unfairU).eff (1 : Fin 3) ∧
    0 < (layerOf unfairU).procMass (0 : Fin 3) ∧ 0 < (layerOf unfairU).procMass (1 : Fin 3) ∧
    (layerOf unfairU).procEU (0 : Fin 3) = 1 ∧ (layerOf unfairU).procEU (1 : Fin 3) = -1 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · rw [procMass_layerOf]; norm_num
  · rw [procMass_layerOf]; norm_num
  · rw [procEU_layerOf]; rfl
  · rw [procEU_layerOf]; rfl

/-! ## A paper prior without fairness where a self-modifying policy is strictly preferred -/

namespace NoFair

/-- `Rec ≠ Ask`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mRec_ne_mAsk : mRec ≠ mAsk := mAsk_ne_mRec.symm

/-- The structure: `Act = {x = 0, m = 1}`, every action available everywhere, `𝒜^m = {m}`,
`m̂ = x`, `mod m = ∅` (a self-modification with no forced point).
Source: mandate T3 ("a three-line paper prior")
Kind: D
Fidelity: n/a -/
def S : PaperStructure twoTables (Fin 2) where
  Aof := fun _ => Finset.univ
  selfMod := {1}
  twin := fun a => if a = 1 then 0 else a
  twin_nonMod := by decide
  twin_typed := by intro a T _; exact Finset.mem_univ _
  twin_id := by intro a ha; fin_cases a <;> simp_all
  mod := fun _ _ => none
  mod_nonMod_none := by intro _ _ _; rfl

/-- The causal structure: nothing is forced, so every condition is vacuous.
Source: mandate T1(b)
Kind: D
Fidelity: n/a -/
def C : S.CausalStructure where
  rank := fun _ => 0
  rank_lt := by intro a o o' a' _ h; simp [S] at h
  no_disagree := by intro a b o' x y h; simp [S] at h
  mod_nonMod := by intro a o' a' h; simp [S] at h
  mod_typed := by intro a o' a' h; simp [S] at h

/-- Nothing is ever forced in `C`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma not_forced (π : Policy twoTables (Fin 2)) (o : ↥twoTables) : ¬ C.Forced π o := by
  rintro ⟨a', o₁, _, h⟩
  simp [S] at h

/-- **`effCausal` on `C`**: the twin at self-modifying points, the policy elsewhere.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma effCausal_eq (π : Policy twoTables (Fin 2)) (o : ↥twoTables) :
    C.effCausal π o = if π o = 1 then 0 else π o := by
  rw [C.effCausal_of_not_forced (not_forced π o)]
  by_cases h : π o = 1 <;> simp [S, h]

/-- The two-point policy. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def pol (a b : Fin 2) : Policy twoTables (Fin 2) := fun T => if T = T1 then a else b

/-- `pol a b o = a`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma pol_T1 (a b : Fin 2) : pol a b T1 = a := by simp [pol]
/-- `pol a b ō = b`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma pol_T2 (a b : Fin 2) : pol a b T2 = b := by simp [pol, mRec_ne_mAsk]

/-- `pol` is injective. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pol_inj {a b a' b' : Fin 2} : pol a b = pol a' b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    exact ⟨by simpa using congrFun h T1, by simpa using congrFun h T2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The chosen policy: `(m, x)` in the worlds with second coordinate `true`, `(x, x)` otherwise.
Source: mandate T3
Kind: D
Fidelity: n/a -/
def chosen (ω : Fin 2 × Bool) : Policy twoTables (Fin 2) := pol (if ω.2 then 1 else 0) 0

/-- **The unfair paper prior**: four worlds of mass `1/4`, `pp = effCausal ∘ chosen`, and the
environment pays `1` for choosing `(m, x)`, `0` for `(x, x)` — a punishment for the ritual of
cognition.
Source: mandate T3
Kind: D
Fidelity: n/a -/
noncomputable def prior : FiniteBLIPrior witIndex 1 twoTables (Fin 2) :=
  handPrior (Fin 2 × Bool) (fun _ => 1 / 4) (fun _ => by norm_num)
    (by norm_num [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool])
    (fun ω => twoState ω.1) two_zeroOne (fun ω => C.effCausal (chosen ω))
    (fun ω => if ω.2 then 1 else 0)

/-- The paper layer, with `eff := effCausal` (grade (a) for its properties).
Source: mandate T3
Kind: D
Fidelity: n/a -/
noncomputable def Λ : PaperLayer prior where
  chosen := chosen
  eff := C.effCausal
  pp_eff := fun _ => rfl

/-- The chosen coordinate. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma Λ_chosen (ω : Fin 2 × Bool) : Λ.chosen ω = chosen ω := rfl

/-- The positive chosen policies are `(m, x)` and `(x, x)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pos_cases {π : Policy twoTables (Fin 2)} (h : 0 < Λ.procMass π) :
    π = pol 1 0 ∨ π = pol 0 0 := by
  rw [PaperLayer.procMass_eq] at h
  obtain ⟨ω, hω, _⟩ := (massOf_pos_iff prior.μ prior.μ_nonneg _).mp h
  rw [Λ_chosen] at hω
  rw [← hω]
  rcases ω with ⟨s, b⟩
  cases b <;> simp [chosen]

/-- The masses. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma procMass_eq : Λ.procMass (pol 1 0) = 1 / 2 ∧ Λ.procMass (pol 0 0) = 1 / 2 := by
  refine ⟨?_, ?_⟩ <;>
  · rw [PaperLayer.procMass_eq]
    unfold prior
    rw [handPrior_massOf]
    simp only [handPrior, massOf, Λ_chosen, chosen, pol_inj, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fintype.sum_bool]
    norm_num

/-- The values: `(m, x)` scores `1`, `(x, x)` scores `0`.
Source: mandate T3. Kind: L. Fidelity: n/a -/
lemma procEU_eq : Λ.procEU (pol 1 0) = 1 ∧ Λ.procEU (pol 0 0) = 0 := by
  refine ⟨?_, ?_⟩ <;>
  · rw [PaperLayer.procEU_eq]
    unfold prior
    rw [handPrior_condExp]
    simp only [handPrior, condExp, massOf, integralOf, Λ_chosen, chosen, pol_inj,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]
    norm_num

/-- Both chosen policies have the same effective policy `(x, x)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma eff_eq : C.effCausal (pol 1 0) = pol 0 0 ∧ C.effCausal (pol 0 0) = pol 0 0 := by
  constructor <;>
  · funext o
    rw [effCausal_eq]
    rcases eq_T1_or_T2 o with rfl | rfl <;> simp

/-- **Without Policy Fairness, Theorem 1 fails**: on this paper prior (whose `eff` is the causal
construction), Policy Fairness is false and the self-modifying policy `(m, x)` is strictly
preferred to every well-typed non-modifying policy of positive mass.
Source: mandate T3 (the failure witness for the corollary); bli-paper-004/005
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem no_fairness_no_tiling :
    ¬ prior.PolicyFair Λ.toProcLayer ∧
    ∃ π, S.WellTyped π ∧ ¬ S.NonMod π ∧ 0 < Λ.procMass π ∧
      ∀ π', S.WellTyped π' → S.NonMod π' → 0 < Λ.procMass π' → Λ.procEU π' < Λ.procEU π := by
  obtain ⟨m1, m0⟩ := procMass_eq
  obtain ⟨v1, v0⟩ := procEU_eq
  obtain ⟨e1, e0⟩ := eff_eq
  refine ⟨fun hF => ?_, pol 1 0, fun _ => Finset.mem_univ _, ?_, by rw [m1]; norm_num,
    fun π' _ hnm hpos => ?_⟩
  · have := hF (pol 1 0) (pol 0 0) (by show C.effCausal (pol 1 0) = C.effCausal (pol 0 0); rw [e1, e0])
      (by show 0 < Λ.procMass (pol 1 0); rw [m1]; norm_num)
      (by show 0 < Λ.procMass (pol 0 0); rw [m0]; norm_num)
    change Λ.procEU (pol 1 0) = Λ.procEU (pol 0 0) at this
    rw [v1, v0] at this
    norm_num at this
  · intro h
    have := h T1
    simp [S] at this
  · rcases pos_cases hpos with rfl | rfl
    · exact absurd (by simp [S] : pol 1 0 T1 ∈ S.selfMod) (hnm T1)
    · rw [v1, v0]; norm_num

end NoFair

end Cleanroom.Udt.UdtPaperTiling

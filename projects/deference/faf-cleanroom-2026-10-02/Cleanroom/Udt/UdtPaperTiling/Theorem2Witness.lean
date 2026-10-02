import Cleanroom.Udt.UdtPaperTiling.CoordinationWitness

/-!
# `udt-paper-tiling` · Theorem2Witness: the witnesses of Theorem 2's full hypothesis package
(repair round 1, B-1 of the fidelity audit / B2 of the adversarial audit)

Round 1 of the audits found that no model in the package inhabited the full hypothesis package of
`thm2_udt10_tiling` / `thm2_no_strict_selfMod` (the ledger pointed at `prior3`, where Policy
Coordination fails). Two models repair this, both lifted from the auditors' probes:

* **`Thm2Wit`** (adversarial probe): `S9` with the four chosen policies of `prior4`, each of mass
  `1/4` (every well-typed policy positive), and `U = 20` on `(x,x)`, `10` elsewhere. Policy
  Fairness holds, Policy Coordination for `πstar = (m,y)` holds and its antecedent fires
  (`(x,x)` is strictly better than `πstar` with a different effective policy; `(x,y)` ties), and
  the conclusion of `thm2_udt10_tiling` is **strict** at `o`: `chosenEU o m = 10 < 15 =
  chosenEU o x`. `πstar` is not a UDT 1.0 fixed point here — it cannot be in a non-tie model
  (`thm2_forced_tie`). But PC's *consequent* is automatic here (`πstar`'s points are pointwise
  minimal), so this is the minimal witness of the fixed-point form; the witness of record is
  `Thm2Six` (below, repair round 2).
* **`Thm2Tie`** (fidelity probe): `S9` extended by a third, dominated action `z` at `o`
  (`𝒜_o = {x, m, z}`), chosen policies `(m,y)`, `(x,y)`, `(z,y)` of mass `1/3` each, `U = 10` on
  the first two and `0` on `(z,y)`. This inhabits the **full** package of `thm2_no_strict_selfMod`,
  `IsUDT10` included, non-degenerately: Policy Fairness with two `eff`-classes of different value,
  Policy Coordination firing at `(x,y) ≠ πstar`, the fixed point `(m,y)` strictly beating `z`
  (`10 > 0`), and the one tie `chosenEU o m = chosenEU o x = 10` that `thm2_forced_tie` says every
  witness of this package must have. Grade N+ (the tie is the content of the hypotheses, not a
  degeneracy of the model).
* **`Thm1Wit4`**: Theorem 1's full package (`thm1_no_strict_selfMod`) on a `PaperLayer` — `prior4`
  with `eff9` non-injective and every well-typed policy positive — rather than on `udt-bli-core`'s
  `ProcLayer` witness (adversarial N3).
* **`Thm2Six`** (repair round 2, from the round-2 adversarial audit's probe `Thm2SixPolicy`, N1,
  with the utility split by state for N3): in `Thm2Wit`, `πstar = (m,y)` has the pointwise
  *minimal* chosen-point value at both observations, so Policy Coordination's consequent holds
  for every policy whatever its antecedent says — PC constrains nothing there, and the strict
  conclusion holds without PF or PC. `Thm2Six` is `S9z` with all six well-typed policies positive
  (`1/6` each) and `U = 20` on `(x,x)`, mean `10` on the `eff = (x,y)` class, `0` on the `z`
  policies: PC holds, its antecedent **excludes** the `z` policies whose point `z` at `o` is
  strictly worse than `πstar`'s (the consequent would fail for them: PC does work), and the
  conclusion of `thm2_udt10_tiling` is strict at `o`. Policy Fairness holds **with intra-fibre
  variance**: `U` is `5` or `15` by state on `(m,x)` and `(m,y)` (means `10`), so `U` is not a
  function of the effective policy, nor even of the chosen one, and fairness is used as the
  equality of means it is (every other PF witness of the package has `U = f(pp)`). This is the
  witness of record for `thm2_udt10_tiling`; `Thm2Wit` stays as the minimal one.

Package `udt-paper-tiling` (faf-cleanroom run, 2026-09-30; repair 2026-10-01).
-/

namespace Cleanroom.Udt.UdtPaperTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset CoordWit

/-! ## The non-tie witness of the fixed-point form -/

namespace Thm2Wit

/-- `U = 20` on the chosen policy `(x,x)`, `10` elsewhere.
Source: audit r1 adversarial probe `Thm2Witness` (B2)
Kind: D
Fidelity: n/a -/
def U (ω : Fin 2 × Bool × Bool) : ℚ := if ω.2.1 = false ∧ ω.2.2 = false then 20 else 10

/-- **The prior**: eight worlds of mass `1/8`, `pp = eff9 ∘ chosen4`.
Source: audit r1 adversarial probe `Thm2Witness` (B2)
Kind: D
Fidelity: n/a -/
def prior : FiniteBLIPrior witIndex 1 twoTables (Fin 4) :=
  handPrior (Fin 2 × Bool × Bool) (fun _ => 1 / 8) (fun _ => by norm_num)
    (by norm_num [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool])
    (fun ω => twoState ω.1) two_zeroOne (fun ω => eff9 (chosen4 ω)) U

/-- The paper layer. Source: audit r1 adversarial probe. Kind: D. Fidelity: n/a -/
def Λ : PaperLayer prior where
  chosen := chosen4
  eff := eff9
  pp_eff := fun _ => rfl

/-- The chosen coordinate. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma Λ_chosen (ω : Fin 2 × Bool × Bool) : Λ.chosen ω = chosen4 ω := rfl

/-- The positive chosen policies are the four well-typed ones.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pos_cases {π : Policy twoTables (Fin 4)} (h : 0 < Λ.procMass π) :
    π = pol 0 0 ∨ π = pol 0 1 ∨ π = pol 2 0 ∨ π = pol 2 1 := by
  rw [PaperLayer.procMass_eq] at h
  obtain ⟨ω, hω, _⟩ := (massOf_pos_iff prior.μ prior.μ_nonneg _).mp h
  rw [Λ_chosen] at hω
  rw [← hω]
  rcases ω with ⟨s, b₁, b₂⟩
  cases b₁ <;> cases b₂ <;> simp [chosen4]

/-- Each well-typed policy has mass `1/4`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma procMass (a b : Fin 4) (ha : a = 0 ∨ a = 2) (hb : b = 0 ∨ b = 1) :
    Λ.procMass (pol a b) = 1 / 4 := by
  rw [PaperLayer.procMass_eq]
  unfold prior
  rw [handPrior_massOf]
  simp only [handPrior, massOf, Λ_chosen, chosen4, pol_inj, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fintype.sum_bool]
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    norm_num [g01, g02, g03, g12, g13, g23, g01.symm, g02.symm, g03.symm, g12.symm, g13.symm, g23.symm]

/-- The values of the four policies: `(x,x) ↦ 20`, the others `10`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma procEU : Λ.procEU (pol 0 0) = 20 ∧ Λ.procEU (pol 0 1) = 10 ∧
    Λ.procEU (pol 2 0) = 10 ∧ Λ.procEU (pol 2 1) = 10 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [PaperLayer.procEU_eq]
    unfold prior
    rw [handPrior_condExp]
    simp only [handPrior, condExp, massOf, integralOf, Λ_chosen, chosen4, pol_inj, U,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]
    norm_num [g01, g02, g03, g12, g13, g23, g01.symm, g02.symm, g03.symm, g12.symm, g13.symm, g23.symm]

/-- The chosen-point values: `x ↦ 15` and `m ↦ 10` at `o`; `x ↦ 15` and `y ↦ 10` at `ō`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma chosenEU : Λ.chosenEU T1 0 = 15 ∧ Λ.chosenEU T1 2 = 10 ∧
    Λ.chosenEU T2 0 = 15 ∧ Λ.chosenEU T2 1 = 10 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · unfold PaperLayer.chosenEU prior
    rw [handPrior_condExp]
    simp only [handPrior, condExp, massOf, integralOf, Λ_chosen, chosen4, pol_T1, pol_T2, U,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]
    norm_num [g01, g02, g03, g12, g13, g23, g01.symm, g02.symm, g03.symm, g12.symm, g13.symm, g23.symm]

/-- The chosen-point masses, all `1/2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pointMass : Λ.pointMass T1 0 = 1 / 2 ∧ Λ.pointMass T1 2 = 1 / 2 ∧
    Λ.pointMass T2 0 = 1 / 2 ∧ Λ.pointMass T2 1 = 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · unfold PaperLayer.pointMass prior
    rw [handPrior_massOf]
    simp only [handPrior, massOf, Λ_chosen, chosen4, pol_T1, pol_T2, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fintype.sum_bool]
    norm_num [g01, g02, g03, g12, g13, g23, g01.symm, g02.symm, g03.symm, g12.symm, g13.symm, g23.symm]

/-- **Every well-typed policy is positive** (`NDPROC`).
Source: audit r1 adversarial probe
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem ndproc : ∀ π, S9.WellTyped π → 0 < Λ.procMass π := by
  intro π hπ
  rw [wellTyped9_iff] at hπ
  rw [eq_pol π, procMass _ _ hπ.1 hπ.2]
  norm_num

/-- **Policy Fairness holds**: `(x,y)`, `(m,x)`, `(m,y)` share `eff = (x,y)` and the value `10`;
`(x,x)` is alone in its class.
Source: audit r1 adversarial probe; `main.tex` 145–147
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem policyFair : prior.PolicyFair Λ.toProcLayer := by
  intro p q hpq hp hq
  have hpq' : eff9 p = eff9 q := hpq
  show Λ.procEU p = Λ.procEU q
  obtain ⟨v00, v01, v20, v21⟩ := procEU
  rcases pos_cases hp with rfl | rfl | rfl | rfl <;> rcases pos_cases hq with rfl | rfl | rfl | rfl <;>
    simp [eff9_pol, pol_inj] at hpq' <;> simp [v00, v01, v20, v21]

/-- **Policy Coordination holds** for `πstar = (m, y)`: every positive policy is at least as good
(`10 ≤ 20`, `10 ≤ 10`), and pointwise `chosenEU o m = 10 ≤ 15 = chosenEU o x`,
`chosenEU ō y = 10 ≤ 15 = chosenEU ō x`.
Source: audit r1 adversarial probe; `main.tex` 175–180
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem pc : PolicyCoordination S9 Λ (pol 2 1) := by
  intro π _ hpos _ o _ _
  obtain ⟨c10, c12, c20, c21⟩ := chosenEU
  rcases pos_cases hpos with rfl | rfl | rfl | rfl <;> rcases eq_T1_or_T2 o with rfl | rfl <;>
    simp only [pol_T1, pol_T2, c10, c12, c20, c21] <;> norm_num

/-- **Policy Coordination's antecedent fires**: `(x,x)` is strictly better than `πstar` and has a
different effective policy; `(x,y)` is exactly as good. The *consequent* is automatic here, though
(audit r2 adversarial N1): `πstar = (m,y)` has the pointwise minimal chosen-point value at both
observations (`10 ≤ 15` at `o`, `10 ≤ 15` at `ō`), so PC constrains nothing in this model and
the strict conclusion holds without PF or PC. `Thm2Six` is the model where PC's antecedent
excludes a positive policy whose point is worse than `πstar`'s; it is the witness of record.
Source: audit r1 adversarial probe
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem pc_fires : Λ.procEU (pol 2 1) < Λ.procEU (pol 0 0) ∧ eff9 (pol 0 0) ≠ eff9 (pol 2 1) ∧
    Λ.procEU (pol 2 1) = Λ.procEU (pol 0 1) := by
  obtain ⟨v00, v01, _, v21⟩ := procEU
  refine ⟨by rw [v21, v00]; norm_num, ?_, by rw [v21, v01]⟩
  simp [eff9_pol, pol_inj]

/-- **The full hypothesis package of `thm2_udt10_tiling`, inhabited with every well-typed policy
positive, and its conclusion strict at `o`**: `chosenEU o m = 10 < 15 = chosenEU o x`. The
minimal witness: PC's consequent is automatic here (`pc_fires`), so for the package exercised with
PC doing work see `Thm2Six.full_package_strict` (repair round 2).
Source: audit r1 adversarial probe (B2); mandate T7 ("an N+ where PC holds non-vacuously")
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem thm2_full_package_Nplus :
    prior.PolicyFair Λ.toProcLayer ∧ PolicyCoordination S9 Λ (pol 2 1) ∧
    Λ.eff (Λ.eff (pol 2 1)) = Λ.eff (pol 2 1) ∧ S9.NonMod (Λ.eff (pol 2 1)) ∧
    S9.WellTyped (Λ.eff (pol 2 1)) ∧ 0 < Λ.procMass (pol 2 1) ∧ 0 < Λ.procMass (Λ.eff (pol 2 1)) ∧
    (∀ π, S9.WellTyped π → 0 < Λ.procMass π) ∧
    (∃ a ∈ S9.Aof T1, a ∉ S9.selfMod ∧ 0 < Λ.pointMass T1 a ∧
      Λ.chosenEU T1 2 < Λ.chosenEU T1 a) := by
  have heff : Λ.eff (pol 2 1) = pol 0 1 := by simp [Λ, eff9_pol]
  obtain ⟨c10, c12, _, _⟩ := chosenEU
  obtain ⟨p10, _, _, _⟩ := pointMass
  refine ⟨policyFair, pc, eff9_idem _, eff9_nonMod _,
    eff9_wellTyped _ ((wellTyped9_iff _).mpr (by simp)), ?_, ?_, ndproc,
    ⟨0, by simp [S9], by simp [S9], by rw [p10]; norm_num, by rw [c12, c10]; norm_num⟩⟩
  · rw [procMass 2 1 (by simp) (by simp)]; norm_num
  · rw [heff, procMass 0 1 (by simp) (by simp)]; norm_num

/-- **`thm2_udt10_tiling` applied on the witness**: its (weak) conclusion at every observation.
Source: audit r1 adversarial probe
Kind: N+
Fidelity: n/a
Hyps: (a) none (every hypothesis discharged by `thm2_full_package_Nplus`) -/
theorem thm2_applies : ∀ o, ∃ a ∈ S9.Aof o, a ∉ S9.selfMod ∧ 0 < Λ.pointMass o a ∧
    Λ.chosenEU o (pol 2 1 o) ≤ Λ.chosenEU o a := by
  obtain ⟨hF, hPC, hidem, hnm, hwt, hstar, heff, _, _⟩ := thm2_full_package_Nplus
  exact thm2_udt10_tiling S9 Λ hF hPC hidem hnm hwt hstar heff

/-- **`πstar = (m,y)` is not a UDT 1.0 fixed point here** (`chosenEU o x = 15 > 10 = chosenEU o m`):
as `thm2_forced_tie` says, a witness of the package *with* the rule must tie at `o`.
Source: audit r1 adversarial probe; `thm2_forced_tie`
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem not_isUDT10 : ¬ IsUDT10 S9 Λ (pol 2 1) := by
  intro h
  obtain ⟨c10, c12, _, _⟩ := chosenEU
  obtain ⟨p10, _, _, _⟩ := pointMass
  have := (h T1).2 0 (by simp [S9]) (by rw [p10]; norm_num)
  rw [pol_T1, c10, c12] at this
  norm_num at this

end Thm2Wit

/-! ## The full package with the UDT 1.0 rule: the forced tie, exhibited non-degenerately -/

namespace Thm2Tie

/-- `S9` with a third, dominated action `z = 3` at `o`: `𝒜_o = {x, m, z}`, `𝒜_ō = {x, y}`,
`𝒜^m = {m}`, `m̂ = x`, `mod m = {(ō, y)}`.
Source: audit r1 fidelity probe `Thm2Package` (B-1)
Kind: D
Fidelity: n/a -/
def S9z : PaperStructure twoTables (Fin 4) where
  Aof := fun T => if T = T1 then {0, 2, 3} else {0, 1}
  selfMod := {2}
  twin := fun a => if a = 2 then 0 else a
  twin_nonMod := by decide
  twin_typed := by
    intro a T ha
    by_cases hT : T = T1
    · simp only [hT, if_true] at ha ⊢
      fin_cases a <;> simp_all
    · simp only [hT, if_false] at ha ⊢
      fin_cases a <;> simp_all
  twin_id := by
    intro a ha
    fin_cases a <;> simp_all
  mod := fun a T => if a = 2 ∧ T = T2 then some 1 else none
  mod_nonMod_none := by
    intro a ha T
    fin_cases a <;> simp_all

/-- Chosen policies by index: `0 ↦ (m,y)`, `1 ↦ (x,y)`, `2 ↦ (z,y)`.
Source: audit r1 fidelity probe. Kind: D. Fidelity: n/a -/
def chosenZ (ω : Fin 2 × Fin 3) : Policy twoTables (Fin 4) :=
  pol (if ω.2 = 0 then 2 else if ω.2 = 1 then 0 else 3) 1

/-- Utility `10` on the first two chosen policies, `0` on `(z,y)`.
Source: audit r1 fidelity probe. Kind: D. Fidelity: n/a -/
def UZ (ω : Fin 2 × Fin 3) : ℚ := if ω.2 = 2 then 0 else 10

/-- **The tie prior**: six worlds of mass `1/6`; `pp = eff9 ∘ chosenZ`.
Source: audit r1 fidelity probe (B-1)
Kind: D
Fidelity: n/a -/
def priorZ : FiniteBLIPrior witIndex 1 twoTables (Fin 4) :=
  handPrior (Fin 2 × Fin 3) (fun _ => 1 / 6) (fun _ => by norm_num)
    (by norm_num [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin])
    (fun ω => twoState ω.1) two_zeroOne (fun ω => eff9 (chosenZ ω)) UZ

/-- The paper layer. Source: audit r1 fidelity probe. Kind: D. Fidelity: n/a -/
def ΛZ : PaperLayer priorZ where
  chosen := chosenZ
  eff := eff9
  pp_eff := fun _ => rfl

/-- The chosen coordinate. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma ΛZ_chosen (ω : Fin 2 × Fin 3) : ΛZ.chosen ω = chosenZ ω := rfl

/-- The positive chosen policies. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pos_casesZ {π : Policy twoTables (Fin 4)} (h : 0 < ΛZ.procMass π) :
    π = pol 2 1 ∨ π = pol 0 1 ∨ π = pol 3 1 := by
  rw [PaperLayer.procMass_eq] at h
  obtain ⟨ω, hω, _⟩ := (massOf_pos_iff priorZ.μ priorZ.μ_nonneg _).mp h
  rw [ΛZ_chosen] at hω
  rw [← hω]
  rcases ω with ⟨s, i⟩
  match i with
  | 0 => simp [chosenZ]
  | 1 => simp [chosenZ]
  | 2 => simp [chosenZ, f3_20]

/-- The three policies have mass `1/3` each. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma procMassZ : ΛZ.procMass (pol 2 1) = 1 / 3 ∧ ΛZ.procMass (pol 0 1) = 1 / 3 ∧
    ΛZ.procMass (pol 3 1) = 1 / 3 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [PaperLayer.procMass_eq]
    unfold priorZ
    rw [handPrior_massOf]
    simp only [handPrior, massOf, ΛZ_chosen, chosenZ, pol_inj, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [f3_02, f3_12, f3_10, f3_20, f3_02.symm, f3_12.symm, f3_10.symm, f3_20.symm, g01, g02,
      g03, g12, g13, g23, g01.symm, g02.symm, g03.symm, g12.symm, g13.symm, g23.symm]

/-- The values: `(m,y) ↦ 10`, `(x,y) ↦ 10`, `(z,y) ↦ 0`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma procEUZ : ΛZ.procEU (pol 2 1) = 10 ∧ ΛZ.procEU (pol 0 1) = 10 ∧ ΛZ.procEU (pol 3 1) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [PaperLayer.procEU_eq]
    unfold priorZ
    rw [handPrior_condExp]
    simp only [handPrior, condExp, massOf, integralOf, ΛZ_chosen, chosenZ, pol_inj, UZ,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [f3_02, f3_12, f3_10, f3_20, f3_02.symm, f3_12.symm, f3_10.symm, f3_20.symm, g01, g02,
      g03, g12, g13, g23, g01.symm, g02.symm, g03.symm, g12.symm, g13.symm, g23.symm]

/-- The chosen-point values: `m ↦ 10`, `x ↦ 10`, `z ↦ 0` at `o`; `y ↦ 20/3` at `ō`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma chosenEUZ : ΛZ.chosenEU T1 2 = 10 ∧ ΛZ.chosenEU T1 0 = 10 ∧ ΛZ.chosenEU T1 3 = 0 ∧
    ΛZ.chosenEU T2 1 = 20 / 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · unfold PaperLayer.chosenEU priorZ
    rw [handPrior_condExp]
    simp only [handPrior, condExp, massOf, integralOf, ΛZ_chosen, chosenZ, pol_T1, pol_T2, UZ,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [f3_02, f3_12, f3_10, f3_20, f3_02.symm, f3_12.symm, f3_10.symm, f3_20.symm, g01, g02,
      g03, g12, g13, g23, g01.symm, g02.symm, g03.symm, g12.symm, g13.symm, g23.symm]

/-- The chosen-point masses. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pointMassZ : ΛZ.pointMass T1 2 = 1 / 3 ∧ ΛZ.pointMass T1 0 = 1 / 3 ∧
    ΛZ.pointMass T1 3 = 1 / 3 ∧ ΛZ.pointMass T2 1 = 1 ∧ ΛZ.pointMass T2 0 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · unfold PaperLayer.pointMass priorZ
    rw [handPrior_massOf]
    simp only [handPrior, massOf, ΛZ_chosen, chosenZ, pol_T1, pol_T2, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [f3_02, f3_12, f3_10, f3_20, f3_02.symm, f3_12.symm, f3_10.symm, f3_20.symm, g01, g02,
      g03, g12, g13, g23, g01.symm, g02.symm, g03.symm, g12.symm, g13.symm, g23.symm]

/-- **Policy Fairness holds**, with two `eff`-classes of different value: `{(m,y), (x,y)}` at `10`
and `{(z,y)}` at `0`.
Source: audit r1 fidelity probe; `main.tex` 145–147
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem policyFairZ : priorZ.PolicyFair ΛZ.toProcLayer := by
  intro p q hpq hp hq
  have hpq' : eff9 p = eff9 q := hpq
  show ΛZ.procEU p = ΛZ.procEU q
  obtain ⟨v21, v01, v31⟩ := procEUZ
  rcases pos_casesZ hp with rfl | rfl | rfl <;> rcases pos_casesZ hq with rfl | rfl | rfl <;>
    simp [eff9_pol, pol_inj] at hpq' <;> simp [v21, v01, v31]

/-- **`(m,y)` is a UDT 1.0 fixed point**, strictly beating `z` at `o` (`10 > 0`).
Source: audit r1 fidelity probe; `main.tex` 123–127
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem isUDT10Z : IsUDT10 S9z ΛZ (pol 2 1) := by
  obtain ⟨c12, c10, c13, c21⟩ := chosenEUZ
  obtain ⟨p12, p10, p13, p21, p20⟩ := pointMassZ
  intro o
  rcases eq_T1_or_T2 o with rfl | rfl
  · refine ⟨by simp [S9z], fun a ha _ => ?_⟩
    simp only [pol_T1, c12]
    simp [S9z] at ha
    rcases ha with rfl | rfl | rfl <;> simp [c10, c12, c13]
  · refine ⟨by simp [S9z, mRec_ne_mAsk], fun a ha hpos => ?_⟩
    simp only [pol_T2, c21]
    simp [S9z, mRec_ne_mAsk] at ha
    rcases ha with rfl | rfl
    · rw [p20] at hpos; norm_num at hpos
    · rw [c21]

/-- **Policy Coordination holds, and fires at `(x,y) ≠ πstar`** (non-vacuously): `(x,y)` is
exactly as good as `πstar` and its points are pointwise as good (`10 ≤ 10`, `20/3 ≤ 20/3`);
`(z,y)` is strictly worse overall, so the antecedent excludes it.
Source: audit r1 fidelity probe; `main.tex` 175–180
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem pcZ : PolicyCoordination S9z ΛZ (pol 2 1) := by
  intro π _ hpos hle o _ _
  obtain ⟨v21, v01, v31⟩ := procEUZ
  obtain ⟨c12, c10, c13, c21⟩ := chosenEUZ
  rcases pos_casesZ hpos with rfl | rfl | rfl
  · exact le_refl _
  · rcases eq_T1_or_T2 o with rfl | rfl
    · rw [pol_T1, pol_T1, c12, c10]
    · rw [pol_T2, pol_T2]
  · rw [v21, v31] at hle; norm_num at hle

/-- `eff (m,y) = (x,y)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem effZ : ΛZ.eff (pol 2 1) = pol 0 1 := by simp [ΛZ, eff9_pol]

/-- **A non-degenerate witness of Theorem 2's full hypothesis package, the UDT 1.0 rule
included**: Policy Fairness with two classes of different value, Policy Coordination firing at
`(x,y) ≠ πstar`, the fixed point `(m,y)` strictly beating `z` (`10 > 0`), `πstar` and
`eff πstar = (x,y)` positive, the `eff` properties; the conclusion of `thm2_udt10_tiling` at both
observations; and the tie `chosenEU o m = chosenEU o x = 10` that `thm2_forced_tie` makes
mandatory for every witness of this package. Grade N+ (ruled by audit r2, N-1): utility
non-constant, fairness non-trivial, coordination non-vacuous at `o`, and the only tie is the one
the hypotheses force. Non-degenerate **at `o` only** (audit r2 adversarial N5): at `ō` every
positive chosen policy already plays `y` (`pointMass ō x = 0`), so `m`'s modification changes
nothing on the support there and `IsUDT10`/PC at `ō` hold by the vacuity of the positivity
guards. This too is forced by the package: a real modification at `ō` would tie there as well
(`thm2_forced_tie`), and breaking that tie with a dominated `(z,·)` policy breaks either PC at
`(x,y)` or the fixed point at `ō` — so the package admits only models that tie and are
degenerate elsewhere, or models in which every positive policy has the same value.
Source: audit r1 fidelity probe (B-1); mandate T7; `thm2_forced_tie`
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem full_package :
    priorZ.PolicyFair ΛZ.toProcLayer ∧ PolicyCoordination S9z ΛZ (pol 2 1) ∧
    IsUDT10 S9z ΛZ (pol 2 1) ∧
    ΛZ.eff (ΛZ.eff (pol 2 1)) = ΛZ.eff (pol 2 1) ∧ S9z.NonMod (ΛZ.eff (pol 2 1)) ∧
    S9z.WellTyped (ΛZ.eff (pol 2 1)) ∧ 0 < ΛZ.procMass (pol 2 1) ∧
    0 < ΛZ.procMass (ΛZ.eff (pol 2 1)) ∧
    -- non-degeneracy
    ΛZ.procEU (pol 3 1) < ΛZ.procEU (pol 0 1) ∧ ΛZ.procEU (pol 0 1) = ΛZ.procEU (pol 2 1) ∧
    0 < ΛZ.procMass (pol 0 1) ∧ pol 0 1 ≠ pol 2 1 ∧ ΛZ.chosenEU T1 3 < ΛZ.chosenEU T1 2 ∧
    -- the conclusion, and the forced tie
    (∀ o, ∃ a ∈ S9z.Aof o, a ∉ S9z.selfMod ∧ 0 < ΛZ.pointMass o a ∧
      ΛZ.chosenEU o (pol 2 1 o) ≤ ΛZ.chosenEU o a) ∧
    ΛZ.chosenEU T1 2 = ΛZ.chosenEU T1 0 := by
  obtain ⟨v21, v01, v31⟩ := procEUZ
  obtain ⟨c12, c10, c13, c21⟩ := chosenEUZ
  obtain ⟨m21, m01, m31⟩ := procMassZ
  have hidem : ΛZ.eff (ΛZ.eff (pol 2 1)) = ΛZ.eff (pol 2 1) := by rw [effZ]; simp [ΛZ, eff9_pol]
  have hnm : S9z.NonMod (ΛZ.eff (pol 2 1)) := by
    rw [effZ]; intro T; rcases eq_T1_or_T2 T with rfl | rfl <;> simp [S9z]
  have hwt : S9z.WellTyped (ΛZ.eff (pol 2 1)) := by
    rw [effZ]; intro T; rcases eq_T1_or_T2 T with rfl | rfl <;> simp [S9z, mRec_ne_mAsk]
  have heff : 0 < ΛZ.procMass (ΛZ.eff (pol 2 1)) := by rw [effZ, m01]; norm_num
  refine ⟨policyFairZ, pcZ, isUDT10Z, hidem, hnm, hwt, by rw [m21]; norm_num, heff,
    by rw [v31, v01]; norm_num, by rw [v01, v21], by rw [m01]; norm_num, by simp [pol_inj],
    by rw [c13, c12]; norm_num,
    thm2_udt10_tiling S9z ΛZ policyFairZ pcZ hidem hnm hwt (by rw [m21]; norm_num) heff,
    by rw [c12, c10]⟩

/-- **`thm2_no_strict_selfMod` applied on the tie witness** (its full package, rule included).
Source: audit r1 fidelity probe
Kind: N+
Fidelity: n/a
Hyps: (a) none (every hypothesis discharged by `full_package`) -/
theorem thm2_no_strict_applies :
    ¬ ∃ o, ∃ aₘ ∈ S9z.Aof o, aₘ ∈ S9z.selfMod ∧ 0 < ΛZ.pointMass o aₘ ∧
      ∀ a ∈ S9z.Aof o, a ∉ S9z.selfMod → 0 < ΛZ.pointMass o a →
        ΛZ.chosenEU o a < ΛZ.chosenEU o aₘ := by
  obtain ⟨hF, hPC, hU, hidem, hnm, hwt, hstar, heff, _⟩ := full_package
  exact thm2_no_strict_selfMod S9z ΛZ hF hPC hU hidem hnm hwt hstar heff

end Thm2Tie

/-! ## Theorem 1's full package on a paper layer -/

namespace Thm1Wit4

/-- **Theorem 1's full package on `prior4`** — a `PaperLayer` whose `eff9` is non-injective
(`eff (m,y) = eff (x,y) = (x,y)`) with every well-typed policy positive — and its conclusion:
no well-typed policy (self-modifying or not) is strictly better than every well-typed
non-modifying one. The N+ witness of record for `thm1_no_strict_selfMod` (the ledger previously
cited `udt-bli-core`'s `ProcLayer` witness, which inhabits `thm1_procLayer`'s package instead).
Source: audit r1 adversarial N3; `main.tex` 149–161
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem thm1_on_prior4 :
    prior4.PolicyFair Λ4.toProcLayer ∧ (∀ π, S9.WellTyped π → 0 < Λ4.procMass π) ∧
    eff9 (pol 2 1) = eff9 (pol 0 1) ∧ pol 2 1 ≠ pol 0 1 ∧ ¬ S9.NonMod (pol 2 1) ∧
    ¬ ∃ π, S9.WellTyped π ∧ ¬ S9.NonMod π ∧
      ∀ π', S9.WellTyped π' → S9.NonMod π' → Λ4.procEU π' < Λ4.procEU π := by
  refine ⟨policyFair4, ndproc9, by simp [eff9_pol], by simp [pol_inj], ?_,
    thm1_no_strict_selfMod S9 Λ4 policyFair4 (fun π => eff9_idem π) (fun π => eff9_nonMod π)
      (fun π h => eff9_wellTyped π h) ndproc9⟩
  intro h
  have := h T1
  simp [S9] at this

end Thm1Wit4

/-! ## The witness of record for the fixed-point form: PC excluding a positive policy, a strict
conclusion, and Policy Fairness with intra-fibre variance (repair round 2) -/

namespace Thm2Six

open Thm2Tie

/-- Chosen policies by index: `0 ↦ (x,x)`, `1 ↦ (x,y)`, `2 ↦ (m,x)`, `3 ↦ (m,y)`, `4 ↦ (z,x)`,
`5 ↦ (z,y)`.
Source: audit r2 adversarial probe `Thm2SixPolicy` (N1)
Kind: D
Fidelity: n/a -/
def chosen₀ : Fin 6 → Policy twoTables (Fin 4)
  | 0 => pol 0 0
  | 1 => pol 0 1
  | 2 => pol 2 0
  | 3 => pol 2 1
  | 4 => pol 3 0
  | 5 => pol 3 1

/-- The utility in state `0`: `20` on `(x,x)`, `10` on `(x,y)`, `5` on `(m,x)`, `15` on `(m,y)`,
`0` on the `z` policies.
Source: audit r2 adversarial probe `Thm2SixPolicy` (N1), split by state (N3)
Kind: D
Fidelity: n/a -/
def U₀ : Fin 6 → ℚ
  | 0 => 20
  | 1 => 10
  | 2 => 5
  | 3 => 15
  | 4 => 0
  | 5 => 0

/-- The utility in state `1`: as `U₀` with `(m,x) ↦ 15`, `(m,y) ↦ 5` (so each has mean `10`).
Source: audit r2 adversarial probe `Thm2SixPolicy` (N1), split by state (N3)
Kind: D
Fidelity: n/a -/
def U₁ : Fin 6 → ℚ
  | 0 => 20
  | 1 => 10
  | 2 => 15
  | 3 => 5
  | 4 => 0
  | 5 => 0

/-- The utility on a world `(state, policy index)`.
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def U (ω : Fin 2 × Fin 6) : ℚ := if ω.1 = 0 then U₀ ω.2 else U₁ ω.2

/-- Twelve worlds of mass `1/12`, `pp = eff9 ∘ chosen₀`.
Source: audit r2 adversarial probe `Thm2SixPolicy` (N1)
Kind: D
Fidelity: n/a -/
def prior : FiniteBLIPrior witIndex 1 twoTables (Fin 4) :=
  handPrior (Fin 2 × Fin 6) (fun _ => 1 / 12) (fun _ => by norm_num)
    (by norm_num [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin])
    (fun ω => twoState ω.1) two_zeroOne (fun ω => eff9 (chosen₀ ω.2)) U

/-- The paper layer. Source: audit r2 adversarial probe. Kind: D. Fidelity: n/a -/
def Λ : PaperLayer prior where
  chosen := fun ω => chosen₀ ω.2
  eff := eff9
  pp_eff := fun _ => rfl

/-- The chosen coordinate. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma Λ_chosen (ω : Fin 2 × Fin 6) : Λ.chosen ω = chosen₀ ω.2 := rfl

/-- `0 ≠ 1` in `Fin 4`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma g01 : (0 : Fin 4) ≠ 1 := by decide
/-- `0 ≠ 2` in `Fin 4`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma g02 : (0 : Fin 4) ≠ 2 := by decide
/-- `0 ≠ 3` in `Fin 4`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma g03 : (0 : Fin 4) ≠ 3 := by decide
/-- `1 ≠ 2` in `Fin 4`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma g12 : (1 : Fin 4) ≠ 2 := by decide
/-- `1 ≠ 3` in `Fin 4`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma g13 : (1 : Fin 4) ≠ 3 := by decide
/-- `2 ≠ 3` in `Fin 4`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma g23 : (2 : Fin 4) ≠ 3 := by decide
/-- `1 ≠ 0` in `Fin 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma s10 : (1 : Fin 2) ≠ 0 := by decide

/-- The positive chosen policies are the six well-typed ones.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pos_cases {π : Policy twoTables (Fin 4)} (h : 0 < Λ.procMass π) :
    π = pol 0 0 ∨ π = pol 0 1 ∨ π = pol 2 0 ∨ π = pol 2 1 ∨ π = pol 3 0 ∨ π = pol 3 1 := by
  rw [PaperLayer.procMass_eq] at h
  obtain ⟨ω, hω, _⟩ := (massOf_pos_iff prior.μ prior.μ_nonneg _).mp h
  rw [Λ_chosen] at hω
  rw [← hω]
  rcases ω with ⟨s, i⟩
  match i with
  | 0 => simp [chosen₀]
  | 1 => simp [chosen₀]
  | 2 => simp [chosen₀]
  | 3 => simp [chosen₀]
  | 4 => simp [chosen₀]
  | 5 => simp [chosen₀]

/-- Each well-typed policy has mass `1/6`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma procMass (a b : Fin 4) (ha : a = 0 ∨ a = 2 ∨ a = 3) (hb : b = 0 ∨ b = 1) :
    Λ.procMass (pol a b) = 1 / 6 := by
  rw [PaperLayer.procMass_eq]
  unfold prior
  rw [handPrior_massOf]
  simp only [handPrior, massOf, Λ_chosen, chosen₀, pol_inj, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_six]
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl <;>
    norm_num [g01, g02, g03, g12, g13, g23, g01.symm, g02.symm, g03.symm, g12.symm, g13.symm, g23.symm]

/-- The values: `(x,x) ↦ 20`, the `(x,y)`-class `↦ 10` (each as a mean), the `z` policies `↦ 0`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma procEU : Λ.procEU (pol 0 0) = 20 ∧ Λ.procEU (pol 0 1) = 10 ∧ Λ.procEU (pol 2 0) = 10 ∧
    Λ.procEU (pol 2 1) = 10 ∧ Λ.procEU (pol 3 0) = 0 ∧ Λ.procEU (pol 3 1) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [PaperLayer.procEU_eq]
    unfold prior
    rw [handPrior_condExp]
    simp only [handPrior, condExp, massOf, integralOf, Λ_chosen, chosen₀, pol_inj, U, U₀, U₁,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_six]
    norm_num [g01, g02, g03, g12, g13, g23, g01.symm, g02.symm, g03.symm, g12.symm, g13.symm,
      g23.symm, s10]

/-- The chosen-point values: at `o`, `x ↦ 15`, `m ↦ 10`, `z ↦ 0`; at `ō`, `x ↦ 10`, `y ↦ 20/3`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma chosenEU : Λ.chosenEU T1 0 = 15 ∧ Λ.chosenEU T1 2 = 10 ∧ Λ.chosenEU T1 3 = 0 ∧
    Λ.chosenEU T2 0 = 10 ∧ Λ.chosenEU T2 1 = 20 / 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · unfold PaperLayer.chosenEU prior
    rw [handPrior_condExp]
    simp only [handPrior, condExp, massOf, integralOf, Λ_chosen, chosen₀, pol_T1, pol_T2, U, U₀,
      U₁, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_six]
    norm_num [g01, g02, g03, g12, g13, g23, g01.symm, g02.symm, g03.symm, g12.symm, g13.symm,
      g23.symm, s10]

/-- The chosen-point masses: `1/3` each at `o`, `1/2` each at `ō`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pointMass : Λ.pointMass T1 0 = 1 / 3 ∧ Λ.pointMass T1 2 = 1 / 3 ∧ Λ.pointMass T1 3 = 1 / 3 ∧
    Λ.pointMass T2 0 = 1 / 2 ∧ Λ.pointMass T2 1 = 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · unfold PaperLayer.pointMass prior
    rw [handPrior_massOf]
    simp only [handPrior, massOf, Λ_chosen, chosen₀, pol_T1, pol_T2, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_six]
    norm_num [g01, g02, g03, g12, g13, g23, g01.symm, g02.symm, g03.symm, g12.symm, g13.symm, g23.symm]

/-- Well-typed policies of `S9z` are `pol a b` with `a ∈ {x, m, z}`, `b ∈ {x, y}`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma wellTyped_iff (π : Policy twoTables (Fin 4)) :
    S9z.WellTyped π ↔ (π T1 = 0 ∨ π T1 = 2 ∨ π T1 = 3) ∧ (π T2 = 0 ∨ π T2 = 1) := by
  constructor
  · intro h
    have h1 := h T1
    have h2 := h T2
    simp [S9z, mRec_ne_mAsk] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩ T
    rcases eq_T1_or_T2 T with rfl | rfl
    · simp only [S9z, if_true]; rcases h1 with h | h | h <;> simp [h]
    · simp only [S9z]; simp [mRec_ne_mAsk]; rcases h2 with h | h <;> simp [h]

/-- Every well-typed policy is positive (`NDPROC`).
Source: audit r2 adversarial probe `Thm2SixPolicy` (N1)
Kind: L
Fidelity: n/a -/
theorem ndproc : ∀ π, S9z.WellTyped π → 0 < Λ.procMass π := by
  intro π hπ
  rw [wellTyped_iff] at hπ
  rw [eq_pol π, procMass _ _ hπ.1 hπ.2]
  norm_num

/-- **Policy Fairness**, the classes `{(x,x)}`, `{(x,y), (m,x), (m,y)}`, `{(z,x)}`, `{(z,y)}` —
with the means equal while `U` varies inside the second class (`intra_fibre_variance`).
Source: audit r2 adversarial probe `Thm2SixPolicy` (N1); `main.tex` 145–147
Kind: N+
Fidelity: n/a -/
theorem policyFair : prior.PolicyFair Λ.toProcLayer := by
  intro p q hpq hp hq
  have hpq' : eff9 p = eff9 q := hpq
  show Λ.procEU p = Λ.procEU q
  obtain ⟨v00, v01, v20, v21, v30, v31⟩ := procEU
  rcases pos_cases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases pos_cases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [eff9_pol, pol_inj] at hpq' <;> simp [v00, v01, v20, v21, v30, v31]

/-- **`U` is not a function of the effective policy, nor of the chosen one**: the two worlds of
the chosen policy `(m,x)` have the same `pp` and `chosen` but utilities `5` and `15`. So Policy
Fairness holds here as the equality of means it is, not because `U = f(pp)` (adversarial r2 N3).
Source: audit r2 adversarial N3
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem intra_fibre_variance :
    prior.pp (0, 2) = prior.pp (1, 2) ∧ Λ.chosen (0, 2) = Λ.chosen (1, 2) ∧
    prior.U (0, 2) ≠ prior.U (1, 2) := by
  refine ⟨rfl, rfl, ?_⟩
  show U (0, 2) ≠ U (1, 2)
  simp [U, U₀, U₁, s10]

/-- **Policy Coordination for `πstar = (m,y)`**: the antecedent excludes the `z` policies (value
`0 < 10`); for the four others the points are pointwise at least `πstar`'s.
Source: audit r2 adversarial probe `Thm2SixPolicy` (N1); `main.tex` 175–180
Kind: N+
Fidelity: n/a -/
theorem pc : PolicyCoordination S9z Λ (pol 2 1) := by
  intro π _ hpos hle o _ _
  obtain ⟨v00, v01, v20, v21, v30, v31⟩ := procEU
  obtain ⟨c10, c12, c13, c20, c21⟩ := chosenEU
  rcases pos_cases hpos with rfl | rfl | rfl | rfl | rfl | rfl
  · rcases eq_T1_or_T2 o with rfl | rfl <;> simp only [pol_T1, pol_T2, c10, c12, c20, c21] <;> norm_num
  · rcases eq_T1_or_T2 o with rfl | rfl <;> simp only [pol_T1, pol_T2, c10, c12, c20, c21] <;> norm_num
  · rcases eq_T1_or_T2 o with rfl | rfl <;> simp only [pol_T1, pol_T2, c10, c12, c20, c21] <;> norm_num
  · exact le_refl _
  · rw [v21, v30] at hle; norm_num at hle
  · rw [v21, v31] at hle; norm_num at hle

/-- **PC does work here**: `(z,y)` is well-typed and positive, strictly worse than `πstar` overall
(so excluded by the antecedent), and its point `z` at `o` is strictly worse than `πstar`'s — the
consequent would fail for it. (In `Thm2Wit` the consequent held for every policy.)
Source: audit r2 adversarial probe `Thm2SixPolicy` (N1)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem pc_excludes : S9z.WellTyped (pol 3 1) ∧ 0 < Λ.procMass (pol 3 1) ∧
    Λ.procEU (pol 3 1) < Λ.procEU (pol 2 1) ∧ 0 < Λ.pointMass T1 3 ∧
    Λ.chosenEU T1 3 < Λ.chosenEU T1 2 := by
  obtain ⟨_, _, _, v21, _, v31⟩ := procEU
  obtain ⟨_, c12, c13, _, _⟩ := chosenEU
  obtain ⟨_, _, p13, _, _⟩ := pointMass
  refine ⟨(wellTyped_iff _).mpr (by simp), ndproc _ ((wellTyped_iff _).mpr (by simp)),
    by rw [v31, v21]; norm_num, by rw [p13]; norm_num, by rw [c13, c12]; norm_num⟩

/-- **The full package of `thm2_udt10_tiling`, every well-typed policy positive, PC excluding a
positive policy, and the conclusion strict at `o`** — the witness of record for the fixed-point
form. `πstar` is not a UDT 1.0 fixed point, as `thm2_forced_tie` requires of a non-tie model.
Source: audit r2 adversarial probe `Thm2SixPolicy` (N1); mandate T7
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem full_package_strict :
    prior.PolicyFair Λ.toProcLayer ∧ PolicyCoordination S9z Λ (pol 2 1) ∧
    Λ.eff (Λ.eff (pol 2 1)) = Λ.eff (pol 2 1) ∧ S9z.NonMod (Λ.eff (pol 2 1)) ∧
    S9z.WellTyped (Λ.eff (pol 2 1)) ∧ 0 < Λ.procMass (pol 2 1) ∧ 0 < Λ.procMass (Λ.eff (pol 2 1)) ∧
    (∀ π, S9z.WellTyped π → 0 < Λ.procMass π) ∧
    (∃ a ∈ S9z.Aof T1, a ∉ S9z.selfMod ∧ 0 < Λ.pointMass T1 a ∧
      Λ.chosenEU T1 2 < Λ.chosenEU T1 a) ∧
    ¬ IsUDT10 S9z Λ (pol 2 1) := by
  have heff : Λ.eff (pol 2 1) = pol 0 1 := by simp [Λ, eff9_pol]
  obtain ⟨c10, c12, _, _, _⟩ := chosenEU
  obtain ⟨p10, _, _, _, _⟩ := pointMass
  refine ⟨policyFair, pc, by rw [heff]; simp [Λ, eff9_pol], ?_, ?_, ?_, ?_, ndproc,
    ⟨0, by simp [S9z], by simp [S9z], by rw [p10]; norm_num, by rw [c12, c10]; norm_num⟩, ?_⟩
  · rw [heff]; intro T; rcases eq_T1_or_T2 T with rfl | rfl <;> simp [S9z]
  · rw [heff]; exact (wellTyped_iff _).mpr (by simp)
  · rw [procMass 2 1 (by simp) (by simp)]; norm_num
  · rw [heff, procMass 0 1 (by simp) (by simp)]; norm_num
  · intro h
    have := (h T1).2 0 (by simp [S9z]) (by rw [p10]; norm_num)
    rw [pol_T1, c10, c12] at this
    norm_num at this

/-- **`thm2_udt10_tiling` applied** on the witness of record.
Source: audit r2 adversarial probe `Thm2SixPolicy` (N1)
Kind: N+
Fidelity: n/a
Hyps: (a) none (every hypothesis discharged by `full_package_strict`) -/
theorem thm2_applies : ∀ o, ∃ a ∈ S9z.Aof o, a ∉ S9z.selfMod ∧ 0 < Λ.pointMass o a ∧
    Λ.chosenEU o (pol 2 1 o) ≤ Λ.chosenEU o a := by
  obtain ⟨hF, hPC, hidem, hnm, hwt, hstar, heff, _, _, _⟩ := full_package_strict
  exact thm2_udt10_tiling S9z Λ hF hPC hidem hnm hwt hstar heff

end Thm2Six

end Cleanroom.Udt.UdtPaperTiling

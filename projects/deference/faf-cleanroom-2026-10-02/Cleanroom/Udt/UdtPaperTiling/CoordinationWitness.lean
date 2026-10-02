import Cleanroom.Udt.UdtPaperTiling.Coordination
import Cleanroom.Bli.UdtBliCore.WitnessCorr

/-!
# `udt-paper-tiling` · CoordinationWitness: Theorem 2 is false under Strict Policy Coordination;
the restricted variants (ii)/(iii) do not prove tiling (T9, T8(c))

**The structure `S9`**: observations `o = T1`, `ō = T2`; actions `x = 0`, `y = 1`, `m = 2`
(`3` unused); `𝒜_o = {x, m}`, `𝒜_ō = {x, y}`, `𝒜^m = {m}`, `m̂ = x`, `mod m = {(ō, y)}`; the
effective policy `eff9` (the paper's `eff` for this structure: `m` at `o` becomes `x` and forces
`y` at `ō`), packaged as an `EffData` with its three properties proved (`E9`).

**The four-policy prior `prior4`** (T9): the four well-typed chosen policies `(x,x)`, `(x,y)`,
`(m,x)`, `(m,y)` each of mass `1/4` (every well-typed policy positive: `ndproc9`), `U = 0` on
`(x,x)` and `10` elsewhere. Policy Fairness holds (`eff (m,·) = (x,y)`, all three have value
`10`); `πstar = (m, y)` is a UDT 1.0 fixed point (`chosenEU o m = 10 > 5 = chosenEU o x`,
`chosenEU ō y = 10 > 5`); Strict Policy Coordination holds **vacuously** (no policy beats `10`);
and `m` is strictly preferred at `o` to the only available non-modifying action. So **Theorem 2
with Strict PC is false**, not merely unproved (bli-paper-072 settled). Consistently, plain PC
fails there (`(x,y)` is as good as `πstar` yet `5 ≥ 10` is demanded).

**The three-policy prior `prior3`** (T8(c)(ii)/(iii)): the same structure with `(m,x)` null and
`(x,x)`, `(x,y)`, `(m,y)` of mass `1/3`: Policy Fairness, the fixed point `(m,y)`, Policy
Coordination with the consequent only at non-modifying points of `πstar` (variant (ii)) and
Policy Coordination compared against `eff πstar` (variant (iii)) all hold, and tiling fails at
`o`. (In this structure both variants force `(m,x)` to be null: with `(m,x)` positive its point
`ō ↦ x` has value `(L+H)/2 < H`, which (ii)/(iii) forbid — see `udt-paper-tiling-findings` F-7.)

Package `udt-paper-tiling` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Udt.UdtPaperTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

namespace CoordWit

/-- `Rec ≠ Ask` (the form `T2 = T1` takes after `simp`). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mRec_ne_mAsk : mRec ≠ mAsk := mAsk_ne_mRec.symm

/-- `(0 : Fin 4) ≠ 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma g01 : (0 : Fin 4) ≠ 1 := by decide
/-- `(0 : Fin 4) ≠ 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma g02 : (0 : Fin 4) ≠ 2 := by decide
/-- `(0 : Fin 4) ≠ 3`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma g03 : (0 : Fin 4) ≠ 3 := by decide
/-- `(1 : Fin 4) ≠ 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma g12 : (1 : Fin 4) ≠ 2 := by decide
/-- `(1 : Fin 4) ≠ 3`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma g13 : (1 : Fin 4) ≠ 3 := by decide
/-- `(2 : Fin 4) ≠ 3`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma g23 : (2 : Fin 4) ≠ 3 := by decide

/-- The two-point policy `o ↦ a`, `ō ↦ b`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def pol (a b : Fin 4) : Policy twoTables (Fin 4) := fun T => if T = T1 then a else b

/-- `pol a b o = a`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma pol_T1 (a b : Fin 4) : pol a b T1 = a := by simp [pol]

/-- `pol a b ō = b`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma pol_T2 (a b : Fin 4) : pol a b T2 = b := by simp [pol, mRec_ne_mAsk]

/-- `pol` is injective in both coordinates. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pol_inj {a b a' b' : Fin 4} : pol a b = pol a' b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    exact ⟨by simpa using congrFun h T1, by simpa using congrFun h T2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Every policy on `twoTables` is a `pol`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma eq_pol (π : Policy twoTables (Fin 4)) : π = pol (π T1) (π T2) := by
  funext T
  rcases eq_T1_or_T2 T with rfl | rfl <;> simp

/-- **The structure `S9`**: `𝒜_o = {x, m}`, `𝒜_ō = {x, y}`, `𝒜^m = {m}`, `m̂ = x`, `mod m = {(ō, y)}`.
Source: mandate T9 (suggested countermodel)
Kind: D
Fidelity: n/a -/
def S9 : PaperStructure twoTables (Fin 4) where
  Aof := fun T => if T = T1 then {0, 2} else {0, 1}
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

/-- **The effective policy of `S9`**: `m` at `o` becomes `x` and forces `y` at `ō` (a
self-modifying value at `ō`, which is ill-typed there, is also replaced).
Source: `main.tex` 95–97 on `S9`
Kind: D
Fidelity: n/a -/
def eff9 (π : Policy twoTables (Fin 4)) : Policy twoTables (Fin 4) :=
  pol (if π T1 = 2 then 0 else π T1) (if π T1 = 2 ∨ π T2 = 2 then 1 else π T2)

/-- `eff9` on a `pol`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma eff9_pol (a b : Fin 4) :
    eff9 (pol a b) = pol (if a = 2 then 0 else a) (if a = 2 ∨ b = 2 then 1 else b) := by
  simp [eff9]

/-- `eff9 π` is non-modifying. Source: `main.tex` 97. Kind: P. Fidelity: n/a. Hyps: (a) none -/
theorem eff9_nonMod (π : Policy twoTables (Fin 4)) : S9.NonMod (eff9 π) := by
  intro T
  obtain ⟨a, b, rfl⟩ : ∃ a b, π = pol a b := ⟨_, _, eq_pol π⟩
  rw [eff9_pol]
  rcases eq_T1_or_T2 T with rfl | rfl <;> simp [S9] <;> split_ifs <;> simp_all

/-- `eff9` is idempotent. Source: `main.tex` 97. Kind: P. Fidelity: n/a. Hyps: (a) none -/
theorem eff9_idem (π : Policy twoTables (Fin 4)) : eff9 (eff9 π) = eff9 π := by
  obtain ⟨a, b, rfl⟩ : ∃ a b, π = pol a b := ⟨_, _, eq_pol π⟩
  fin_cases a <;> fin_cases b <;> simp [eff9_pol]

/-- `eff9` preserves well-typedness. Source: `main.tex` 97. Kind: P. Fidelity: n/a. Hyps: (a) none -/
theorem eff9_wellTyped (π : Policy twoTables (Fin 4)) (h : S9.WellTyped π) :
    S9.WellTyped (eff9 π) := by
  obtain ⟨a, b, rfl⟩ : ∃ a b, π = pol a b := ⟨_, _, eq_pol π⟩
  have h1 := h T1
  have h2 := h T2
  simp [S9, mRec_ne_mAsk] at h1 h2
  intro T
  rw [eff9_pol]
  rcases eq_T1_or_T2 T with rfl | rfl
  · simp only [S9, pol_T1, if_true]
    rcases h1 with rfl | rfl <;> simp
  · simp only [S9, pol_T2]
    simp [mRec_ne_mAsk]
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp

/-- **`eff9` as an `EffData`** on `S9`: the paper's three properties are theorems here.
Source: `main.tex` 97
Kind: D
Fidelity: n/a -/
def E9 : S9.EffData where
  eff := eff9
  eff_nonMod := eff9_nonMod
  eff_idem := eff9_idem
  eff_wellTyped := eff9_wellTyped

/-- Well-typed policies of `S9` are `pol a b` with `a ∈ {x, m}`, `b ∈ {x, y}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wellTyped9_iff (π : Policy twoTables (Fin 4)) :
    S9.WellTyped π ↔ (π T1 = 0 ∨ π T1 = 2) ∧ (π T2 = 0 ∨ π T2 = 1) := by
  constructor
  · intro h
    have h1 := h T1
    have h2 := h T2
    simp [S9, mRec_ne_mAsk] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩ T
    rcases eq_T1_or_T2 T with rfl | rfl
    · simp only [S9, if_true]; rcases h1 with h | h <;> simp [h]
    · simp only [S9]; simp [mRec_ne_mAsk]; rcases h2 with h | h <;> simp [h]

/-! ## The four-policy prior (T9) -/

/-- The chosen policy of the world `(state, m at o?, y at ō?)`.
Source: mandate T9
Kind: D
Fidelity: n/a -/
def chosen4 (ω : Fin 2 × Bool × Bool) : Policy twoTables (Fin 4) :=
  pol (if ω.2.1 then 2 else 0) (if ω.2.2 then 1 else 0)

/-- The utility: `0` on the chosen policy `(x, x)`, `10` elsewhere.
Source: mandate T9
Kind: D
Fidelity: n/a -/
def U4 (ω : Fin 2 × Bool × Bool) : ℚ := if ω.2.1 = false ∧ ω.2.2 = false then 0 else 10

/-- **The four-policy prior**: eight worlds of mass `1/8` (two states × four chosen policies),
`pp = eff9 ∘ chosen4`.
Source: mandate T9
Kind: D
Fidelity: n/a -/
def prior4 : FiniteBLIPrior witIndex 1 twoTables (Fin 4) :=
  handPrior (Fin 2 × Bool × Bool) (fun _ => 1 / 8) (fun _ => by norm_num)
    (by norm_num [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool])
    (fun ω => twoState ω.1) two_zeroOne (fun ω => eff9 (chosen4 ω)) U4

/-- The paper layer of `prior4`.
Source: mandate T9
Kind: D
Fidelity: n/a -/
def Λ4 : PaperLayer prior4 where
  chosen := chosen4
  eff := eff9
  pp_eff := fun _ => rfl

/-- The chosen coordinate. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma Λ4_chosen (ω : Fin 2 × Bool × Bool) : Λ4.chosen ω = chosen4 ω := rfl

/-- The chosen policies of positive mass are the four well-typed ones.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pos_cases4 {π : Policy twoTables (Fin 4)} (h : 0 < Λ4.procMass π) :
    π = pol 0 0 ∨ π = pol 0 1 ∨ π = pol 2 0 ∨ π = pol 2 1 := by
  rw [PaperLayer.procMass_eq] at h
  obtain ⟨ω, hω, _⟩ := (massOf_pos_iff prior4.μ prior4.μ_nonneg _).mp h
  rw [Λ4_chosen] at hω
  rw [← hω]
  rcases ω with ⟨s, b₁, b₂⟩
  cases b₁ <;> cases b₂ <;> simp [chosen4]

/-- The masses of the four policies. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma procMass4 (a b : Fin 4) (ha : a = 0 ∨ a = 2) (hb : b = 0 ∨ b = 1) :
    Λ4.procMass (pol a b) = 1 / 4 := by
  rw [PaperLayer.procMass_eq]
  unfold prior4
  rw [handPrior_massOf]
  simp only [handPrior, massOf, Λ4_chosen, chosen4, pol_inj, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fintype.sum_bool]
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num [g01, g02, g03, g12, g13, g23, g01.symm, g02.symm, g03.symm, g12.symm, g13.symm, g23.symm]

/-- The values of the four policies. Source: mandate T9. Kind: L. Fidelity: n/a -/
lemma procEU4 : Λ4.procEU (pol 0 0) = 0 ∧ Λ4.procEU (pol 0 1) = 10 ∧
    Λ4.procEU (pol 2 0) = 10 ∧ Λ4.procEU (pol 2 1) = 10 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [PaperLayer.procEU_eq]
    unfold prior4
    rw [handPrior_condExp]
    simp only [handPrior, condExp, massOf, integralOf, Λ4_chosen, chosen4, pol_inj, U4,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]
    norm_num [g01, g02, g03, g12, g13, g23, g01.symm, g02.symm, g03.symm, g12.symm, g13.symm, g23.symm]

/-- The chosen-point values. Source: mandate T9. Kind: L. Fidelity: n/a -/
lemma chosenEU4 : Λ4.chosenEU T1 0 = 5 ∧ Λ4.chosenEU T1 2 = 10 ∧
    Λ4.chosenEU T2 0 = 5 ∧ Λ4.chosenEU T2 1 = 10 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · unfold PaperLayer.chosenEU prior4
    rw [handPrior_condExp]
    simp only [handPrior, condExp, massOf, integralOf, Λ4_chosen, chosen4, pol_T1, pol_T2, U4,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]
    norm_num [g01, g02, g03, g12, g13, g23, g01.symm, g02.symm, g03.symm, g12.symm, g13.symm, g23.symm]

/-- The chosen-point masses. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pointMass4 : Λ4.pointMass T1 0 = 1 / 2 ∧ Λ4.pointMass T1 2 = 1 / 2 ∧
    Λ4.pointMass T2 0 = 1 / 2 ∧ Λ4.pointMass T2 1 = 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · unfold PaperLayer.pointMass prior4
    rw [handPrior_massOf]
    simp only [handPrior, massOf, Λ4_chosen, chosen4, pol_T1, pol_T2, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fintype.sum_bool]
    norm_num [g01, g02, g03, g12, g13, g23, g01.symm, g02.symm, g03.symm, g12.symm, g13.symm, g23.symm]

/-- **Every well-typed policy is positive** (`NDPROC`): no verdict below rests on a junk `0`.
Source: mandate §7 (package-wide trap)
Kind: L
Fidelity: n/a -/
theorem ndproc9 : ∀ π, S9.WellTyped π → 0 < Λ4.procMass π := by
  intro π hπ
  rw [wellTyped9_iff] at hπ
  rw [eq_pol π, procMass4 _ _ hπ.1 hπ.2]
  norm_num

/-- **Policy Fairness holds on `prior4`**: `(x,y)`, `(m,x)`, `(m,y)` share `eff = (x,y)` and the
value `10`; `(x,x)` is alone in its class.
Source: mandate T9
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem policyFair4 : prior4.PolicyFair Λ4.toProcLayer := by
  intro p q hpq hp hq
  have hpq' : eff9 p = eff9 q := hpq
  show Λ4.procEU p = Λ4.procEU q
  obtain ⟨v00, v01, v20, v21⟩ := procEU4
  rcases pos_cases4 hp with rfl | rfl | rfl | rfl <;> rcases pos_cases4 hq with rfl | rfl | rfl | rfl <;>
    simp [eff9_pol, pol_inj] at hpq' <;> simp [v00, v01, v20, v21]

/-- **`(m, y)` is a UDT 1.0 fixed point** on `prior4`.
Source: mandate T9
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem isUDT10_4 : IsUDT10 S9 Λ4 (pol 2 1) := by
  obtain ⟨c10, c12, c20, c21⟩ := chosenEU4
  intro o
  rcases eq_T1_or_T2 o with rfl | rfl
  · refine ⟨by simp [S9], fun a ha _ => ?_⟩
    simp only [pol_T1, c12]
    simp [S9] at ha
    rcases ha with rfl | rfl <;> simp [c10, c12] <;> norm_num
  · refine ⟨by simp [S9, mRec_ne_mAsk], fun a ha _ => ?_⟩
    simp only [pol_T2, c21]
    simp [S9, mRec_ne_mAsk] at ha
    rcases ha with rfl | rfl <;> simp [c20, c21] <;> norm_num

/-- **Strict Policy Coordination holds (vacuously) on `prior4`**: no positive policy beats `10`.
Source: mandate T9
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem strictPC4 : StrictPolicyCoordination S9 Λ4 (pol 2 1) := by
  intro π _ hpos hlt
  exfalso
  obtain ⟨v00, v01, v20, v21⟩ := procEU4
  rcases pos_cases4 hpos with rfl | rfl | rfl | rfl <;> norm_num [v00, v01, v20, v21] at hlt

/-- **Plain Policy Coordination fails on `prior4`** (consistent with Theorem 2): `(x,y)` is as good
as `(m,y)`, yet `chosenEU o m = 10 ≤ 5 = chosenEU o x` would be demanded.
Source: mandate T9 ("consistency with Theorem 2")
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem not_pc4 : ¬ PolicyCoordination S9 Λ4 (pol 2 1) := by
  intro h
  obtain ⟨v00, v01, v20, v21⟩ := procEU4
  obtain ⟨c10, c12, c20, c21⟩ := chosenEU4
  obtain ⟨p10, p12, p20, p21⟩ := pointMass4
  have := h (pol 0 1) ((wellTyped9_iff _).mpr (by simp)) (by rw [procMass4 0 1 (by simp) (by simp)]; norm_num)
    (by rw [v01, v21]) T1 (by rw [pol_T1, p12]; norm_num) (by rw [pol_T1, p10]; norm_num)
  rw [pol_T1, pol_T1, c12, c10] at this
  norm_num at this

/-- **Tiling fails on `prior4`**: `m` is strictly preferred at `o` to every available
non-modifying action (`10 > 5`), so Theorem 2's conclusion is false there.
Source: mandate T9
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem tiling_fails4 :
    ¬ ∃ a ∈ S9.Aof T1, a ∉ S9.selfMod ∧ 0 < Λ4.pointMass T1 a ∧
      Λ4.chosenEU T1 2 ≤ Λ4.chosenEU T1 a := by
  rintro ⟨a, ha, hnm, _, hle⟩
  obtain ⟨c10, c12, _, _⟩ := chosenEU4
  simp [S9] at ha hnm
  rcases ha with rfl | rfl
  · rw [c12, c10] at hle; norm_num at hle
  · exact hnm rfl

/-- **Theorem 2 is false under Strict Policy Coordination** (bli-paper-072 settled): on `prior4`,
Policy Fairness, the fixed point `(m,y)`, Strict PC and `NDPROC` hold, and the conclusion of
Theorem 2 fails at `o`; plain PC fails there, as Theorem 2 requires.
Source: [[udt-tiling-working-notes-2025-06-30]] l3 b.26–29 (bli-paper-019(i), 072)
Kind: P
Fidelity: exact (refutation by a finite model)
Hyps: (a) none -/
theorem strictPC_countermodel :
    prior4.PolicyFair Λ4.toProcLayer ∧ IsUDT10 S9 Λ4 (pol 2 1) ∧
    StrictPolicyCoordination S9 Λ4 (pol 2 1) ∧ (∀ π, S9.WellTyped π → 0 < Λ4.procMass π) ∧
    (¬ ∃ a ∈ S9.Aof T1, a ∉ S9.selfMod ∧ 0 < Λ4.pointMass T1 a ∧
      Λ4.chosenEU T1 2 ≤ Λ4.chosenEU T1 a) ∧
    ¬ PolicyCoordination S9 Λ4 (pol 2 1) :=
  ⟨policyFair4, isUDT10_4, strictPC4, ndproc9, tiling_fails4, not_pc4⟩

/-! ## The three-policy prior (T8(c)(ii)/(iii)) -/

/-- The chosen policy of the world `(state, index)`: `0 ↦ (x,x)`, `1 ↦ (x,y)`, `2 ↦ (m,y)`.
Source: mandate T8(c)
Kind: D
Fidelity: n/a -/
def chosen3 (ω : Fin 2 × Fin 3) : Policy twoTables (Fin 4) :=
  pol (if ω.2 = 2 then 2 else 0) (if ω.2 = 0 then 0 else 1)

/-- The utility: `0` on `(x,x)`, `10` elsewhere. Source: mandate T8(c). Kind: D. Fidelity: n/a -/
def U3 (ω : Fin 2 × Fin 3) : ℚ := if ω.2 = 0 then 0 else 10

/-- **The three-policy prior**: six worlds of mass `1/6`; `(m,x)` is null.
Source: mandate T8(c)
Kind: D
Fidelity: n/a -/
def prior3 : FiniteBLIPrior witIndex 1 twoTables (Fin 4) :=
  handPrior (Fin 2 × Fin 3) (fun _ => 1 / 6) (fun _ => by norm_num)
    (by norm_num [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin])
    (fun ω => twoState ω.1) two_zeroOne (fun ω => eff9 (chosen3 ω)) U3

/-- The paper layer of `prior3`. Source: mandate T8(c). Kind: D. Fidelity: n/a -/
def Λ3 : PaperLayer prior3 where
  chosen := chosen3
  eff := eff9
  pp_eff := fun _ => rfl

/-- The chosen coordinate. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma Λ3_chosen (ω : Fin 2 × Fin 3) : Λ3.chosen ω = chosen3 ω := rfl

/-- `(0 : Fin 3) ≠ 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma f3_02 : (0 : Fin 3) ≠ 2 := by decide
/-- `(1 : Fin 3) ≠ 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma f3_12 : (1 : Fin 3) ≠ 2 := by decide
/-- `(1 : Fin 3) ≠ 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma f3_10 : (1 : Fin 3) ≠ 0 := by decide
/-- `(2 : Fin 3) ≠ 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma f3_20 : (2 : Fin 3) ≠ 0 := by decide

/-- The positive chosen policies of `prior3`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pos_cases3 {π : Policy twoTables (Fin 4)} (h : 0 < Λ3.procMass π) :
    π = pol 0 0 ∨ π = pol 0 1 ∨ π = pol 2 1 := by
  rw [PaperLayer.procMass_eq] at h
  obtain ⟨ω, hω, _⟩ := (massOf_pos_iff prior3.μ prior3.μ_nonneg _).mp h
  rw [Λ3_chosen] at hω
  rw [← hω]
  rcases ω with ⟨s, i⟩
  match i with
  | 0 => simp [chosen3]
  | 1 => simp [chosen3, f3_10, f3_12]
  | 2 => simp [chosen3, f3_20]

/-- The masses of the three policies (and the null `(m,x)`).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma procMass3 : Λ3.procMass (pol 0 0) = 1 / 3 ∧ Λ3.procMass (pol 0 1) = 1 / 3 ∧
    Λ3.procMass (pol 2 1) = 1 / 3 ∧ Λ3.procMass (pol 2 0) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [PaperLayer.procMass_eq]
    unfold prior3
    rw [handPrior_massOf]
    simp only [handPrior, massOf, Λ3_chosen, chosen3, pol_inj, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [f3_02, f3_12, f3_10, f3_20, g01, g02, g03, g12, g13, g23, g01.symm, g02.symm, g03.symm, g12.symm, g13.symm, g23.symm]

/-- The values of the three policies. Source: mandate T8(c). Kind: L. Fidelity: n/a -/
lemma procEU3 : Λ3.procEU (pol 0 0) = 0 ∧ Λ3.procEU (pol 0 1) = 10 ∧ Λ3.procEU (pol 2 1) = 10 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [PaperLayer.procEU_eq]
    unfold prior3
    rw [handPrior_condExp]
    simp only [handPrior, condExp, massOf, integralOf, Λ3_chosen, chosen3, pol_inj, U3,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [f3_02, f3_12, f3_10, f3_20, g01, g02, g03, g12, g13, g23, g01.symm, g02.symm, g03.symm, g12.symm, g13.symm, g23.symm]

/-- The chosen-point values. Source: mandate T8(c). Kind: L. Fidelity: n/a -/
lemma chosenEU3 : Λ3.chosenEU T1 0 = 5 ∧ Λ3.chosenEU T1 2 = 10 ∧
    Λ3.chosenEU T2 0 = 0 ∧ Λ3.chosenEU T2 1 = 10 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · unfold PaperLayer.chosenEU prior3
    rw [handPrior_condExp]
    simp only [handPrior, condExp, massOf, integralOf, Λ3_chosen, chosen3, pol_T1, pol_T2, U3,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [f3_02, f3_12, f3_10, f3_20, g01, g02, g03, g12, g13, g23, g01.symm, g02.symm, g03.symm, g12.symm, g13.symm, g23.symm]

/-- The chosen-point masses. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pointMass3 : Λ3.pointMass T1 0 = 2 / 3 ∧ Λ3.pointMass T1 2 = 1 / 3 ∧
    Λ3.pointMass T2 0 = 1 / 3 ∧ Λ3.pointMass T2 1 = 2 / 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · unfold PaperLayer.pointMass prior3
    rw [handPrior_massOf]
    simp only [handPrior, massOf, Λ3_chosen, chosen3, pol_T1, pol_T2, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num [f3_02, f3_12, f3_10, f3_20, g01, g02, g03, g12, g13, g23, g01.symm, g02.symm, g03.symm, g12.symm, g13.symm, g23.symm]

/-- **Policy Fairness holds on `prior3`.**
Source: mandate T8(c)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem policyFair3 : prior3.PolicyFair Λ3.toProcLayer := by
  intro p q hpq hp hq
  have hpq' : eff9 p = eff9 q := hpq
  show Λ3.procEU p = Λ3.procEU q
  obtain ⟨v00, v01, v21⟩ := procEU3
  rcases pos_cases3 hp with rfl | rfl | rfl <;> rcases pos_cases3 hq with rfl | rfl | rfl <;>
    simp [eff9_pol, pol_inj] at hpq' <;> simp [v00, v01, v21]

/-- **`(m, y)` is a UDT 1.0 fixed point** on `prior3`.
Source: mandate T8(c)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem isUDT10_3 : IsUDT10 S9 Λ3 (pol 2 1) := by
  obtain ⟨c10, c12, c20, c21⟩ := chosenEU3
  intro o
  rcases eq_T1_or_T2 o with rfl | rfl
  · refine ⟨by simp [S9], fun a ha _ => ?_⟩
    simp only [pol_T1, c12]
    simp [S9] at ha
    rcases ha with rfl | rfl <;> simp [c10, c12] <;> norm_num
  · refine ⟨by simp [S9, mRec_ne_mAsk], fun a ha _ => ?_⟩
    simp only [pol_T2, c21]
    simp [S9, mRec_ne_mAsk] at ha
    rcases ha with rfl | rfl <;> simp [c20, c21] <;> norm_num

/-- **Variant (ii) holds on `prior3`**: Policy Coordination with the consequent only at
non-modifying points of `πstar = (m,y)` — i.e. only at `ō`, where every policy as good as `πstar`
plays `y`.
Source: bli-paper-073 (second variant)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem pcAtNonMod3 : PolicyCoordinationAtNonMod S9 Λ3 (pol 2 1) := by
  intro π _ hpos hle o hnm _ _
  obtain ⟨v00, v01, v21⟩ := procEU3
  rcases eq_T1_or_T2 o with rfl | rfl
  · exact absurd (by simp [S9]) hnm
  · rcases pos_cases3 hpos with rfl | rfl | rfl
    · rw [v21, v00] at hle; norm_num at hle
    · simp
    · simp

/-- **Variant (iii) holds on `prior3`**: Policy Coordination compared against `eff πstar = (x,y)`.
Source: bli-paper-073 (third variant)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem pcEff3 : PolicyCoordinationEff S9 Λ3 (pol 2 1) := by
  intro π _ hpos hle o _ _
  obtain ⟨v00, v01, v21⟩ := procEU3
  obtain ⟨c10, c12, c20, c21⟩ := chosenEU3
  have heff : Λ3.eff (pol 2 1) = pol 0 1 := by simp [Λ3, eff9_pol]
  rw [heff] at hle ⊢
  rcases pos_cases3 hpos with rfl | rfl | rfl
  · rw [v01, v00] at hle; norm_num at hle
  · exact le_refl _
  · rcases eq_T1_or_T2 o with rfl | rfl
    · simp only [pol_T1, c10, c12]; norm_num
    · simp only [pol_T2, c21]; exact le_refl _

/-- **Tiling fails on `prior3`** at `o`.
Source: mandate T8(c)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem tiling_fails3 :
    ¬ ∃ a ∈ S9.Aof T1, a ∉ S9.selfMod ∧ 0 < Λ3.pointMass T1 a ∧
      Λ3.chosenEU T1 2 ≤ Λ3.chosenEU T1 a := by
  rintro ⟨a, ha, hnm, _, hle⟩
  obtain ⟨c10, c12, _, _⟩ := chosenEU3
  simp [S9] at ha hnm
  rcases ha with rfl | rfl
  · rw [c12, c10] at hle; norm_num at hle
  · exact hnm rfl

/-- **The restricted variants (ii) and (iii) do not prove tiling**: on `prior3` Policy Fairness,
the fixed point `(m,y)`, variant (ii) and variant (iii) hold, and Theorem 2's conclusion fails at
`o`. The three positive policies and the null `(m,x)` are recorded (`procMass3`).
Source: bli-paper-073, 019(iii)
Kind: P
Fidelity: exact (refutation by a finite model; `(m,x)` null — see the findings)
Hyps: (a) none -/
theorem restricted_variants_countermodel :
    prior3.PolicyFair Λ3.toProcLayer ∧ IsUDT10 S9 Λ3 (pol 2 1) ∧
    PolicyCoordinationAtNonMod S9 Λ3 (pol 2 1) ∧ PolicyCoordinationEff S9 Λ3 (pol 2 1) ∧
    ¬ ∃ a ∈ S9.Aof T1, a ∉ S9.selfMod ∧ 0 < Λ3.pointMass T1 a ∧
      Λ3.chosenEU T1 2 ≤ Λ3.chosenEU T1 a :=
  ⟨policyFair3, isUDT10_3, pcAtNonMod3, pcEff3, tiling_fails3⟩

end CoordWit

end Cleanroom.Udt.UdtPaperTiling

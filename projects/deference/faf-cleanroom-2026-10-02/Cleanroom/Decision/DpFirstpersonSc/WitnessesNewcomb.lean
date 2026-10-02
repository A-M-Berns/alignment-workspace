import Cleanroom.Decision.DpFirstpersonSc.WitnessesLicense
import Cleanroom.Decision.DpFirstpersonSc.WitnessesAudit
import Cleanroom.Decision.DpCalibration.Examples
import Cleanroom.Decision.DpCalibration.Limit

/-!
# The Transparent-Newcomb verdict table (T2(c)) and the four-row grade table (T5(e))

Every cell is a rational computation on `dp-core-tree`'s catalogue trees, decided by the
characterizations of `License.lean` and `Grades.lean`:

* **grade (iii) / the license** is `License obs C B d` (T2(a): the stamped strict-OC state passes
  the audit iff `License`);
* **grade (ii), the occurrence D–Z grade** is `μ(occ(d)) ≤ ν(O_d)` (`ocState_boundedDensity_iff`);
* **grade (i)** passes every strict-OC state at every row (`strictClausesAt_reachable`), so it is
  not tabulated.

**T2(c), FP-22′'s TN rows** (`p = ¾`, `L = 4`, `S = 1`): V1 under `(1,2)` (one-box at `d_F`,
two-box at `d_E`): `d_E` passes (`tnV1_E_license`: `occ(d_E) = λ⁻¹O_E` exactly), `d_F` fails
(`tnV1_F_license_fails`: `μ(occ(d_F) ∖ λ⁻¹O_F) = ¼`); V2 under `(1,1)`: both points fail
(`occ = Leaves`, `tnV2_E_license_fails`, `tnV2_F_license_fails`).

**T5(e), AN-8's table** (grade (ii) / grade (iii)): `B₁` matched `d`: fail (`1 > ½`) / fail;
TN-V1 at `m = ½`, `d_E`: pass (`½ ≤ ½`) / pass; `d_F`: fail (`1 > ½`) / fail; Told-You-So under
`C₀^{1/10}`, `d₅`: fail (`1 > 19/20`) / fail.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFaithfulUdt
open Finset

/-- Sums over `Box`. Source: none: infrastructure. Kind: L -/
theorem box_sum_univ {M : Type} [AddCommMonoid M] (f : Box → M) : ∑ x, f x = f .large + f .both := by
  have : (Finset.univ : Finset Box) = {.large, .both} := by ext x; cases x <;> simp
  rw [this, Finset.sum_pair (by decide)]

/-! ## Counts on V1 and V2 -/

section counts

variable (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ)

/-- `#_E` on V1: one on the empty branch, zero on the full branch. Source: none: infrastructure.
Kind: L -/
theorem tnV1_count_E (x : Box) (i : Fin 2) (act : Box) :
    count .E (tnV1 p h0 h1 L S) ⟨x, i, act, ()⟩ = if i = 0 then 0 else 1 := by
  unfold tnV1 tnReal
  simp only [count_decision, count_chance, count_leaf]
  fin_cases i <;> simp

/-- `#_F` on V1: the root plus the full branch. Source: none: infrastructure. Kind: L -/
theorem tnV1_count_F (x : Box) (i : Fin 2) (act : Box) :
    count .F (tnV1 p h0 h1 L S) ⟨x, i, act, ()⟩ = if i = 0 then 2 else 1 := by
  unfold tnV1 tnReal
  simp only [count_decision, count_chance, count_leaf]
  fin_cases i <;> simp

/-- `#_E ≥ 1` on V2 (the root queries `E` hypothetically). Source: none: infrastructure.
Kind: L -/
theorem tnV2_count_E_pos (x y : Box) (i : Fin 2) (act : Box) :
    0 < count .E (tnV2 p h0 h1 L S) ⟨x, y, i, act, ()⟩ := by
  unfold tnV2 tnReal
  simp only [count_decision, count_chance, count_leaf]
  fin_cases i <;> simp

/-- `occ(d_E)` on V2 is every run. Source: [[decision-problems-v2]] Observation 1. Kind: L -/
theorem tnV2_occ_E : occ .E (tnV2 p h0 h1 L S) = Finset.univ := by
  ext ℓ
  rcases ℓ with ⟨x, y, i, act, ⟨⟩⟩
  simp only [mem_occ, Finset.mem_univ, iff_true]
  exact tnV2_count_E_pos p h0 h1 L S x y i act

/-- **`occ(d_E) = λ⁻¹O_E` exactly on V1**: the empty branch is consulted at `d_E` and only there.
Source: `anticipation.md` AN-4 ("TN-V1 … `d_E` — `Occ = O_E`, Prop 3's case")
Kind: L -/
theorem tnV1_occ_E_eq : occ .E (tnV1 p h0 h1 L S) = worldEv (tnV1 p h0 h1 L S) (tnObs .E) := by
  ext ℓ
  rcases ℓ with ⟨x, i, act, ⟨⟩⟩
  simp only [mem_occ, worldEv, Finset.mem_filter, Finset.mem_univ, true_and, tnV1_count_E,
    tnV1_world, tnObs]
  fin_cases i <;> simp

/-- `occ(d_F)` on V1 is every run. Source: none: infrastructure. Kind: L -/
theorem tnV1_occ_F : occ .F (tnV1 p h0 h1 L S) = Finset.univ := by
  ext ℓ
  rcases ℓ with ⟨x, i, act, ⟨⟩⟩
  simp only [mem_occ, Finset.mem_univ, iff_true, tnV1_count_F]
  split_ifs <;> omega

end counts

/-! ## T2(c): the FP-22′ rows -/

section fp22

/-- The pure procedure `(1,2)`: one-box at `d_F`, two-box at `d_E`.
Source: `firstperson.md` FP-22′ ("TN at `p = ¾, L = 4, S = 1`"); `anticipation.md` AN-4
("TN-V1 `(1,2)`")
Kind: D -/
def tnOneTwo : Proc TnPt (fun _ => Box) ℚ := Proc.ofFun fun d => if d = .F then .large else .both

/-- **V1, `d_E` passes**: the license holds for every procedure (`occ(d_E) = λ⁻¹O_E` exactly, so
both null sets are empty). A structural identity rather than a computed cell — the N+ of the
T2(c) row is `tnV1_E_occ_mass` (`¼`) and the three failing cells (audit r2 adversarial N6).
Source: `firstperson.md` FP-22′ ("V1's `d_E` passes (`occ = ¼`)")
Kind: L -/
theorem tnV1_E_license (C : Proc TnPt (fun _ => Box) ℚ) :
    License tnObs C (tnV1 (3/4) (by norm_num) (by norm_num) 4 1) .E := by
  unfold License VeridicalASAt CoversAS
  rw [tnV1_occ_E_eq, Finset.sdiff_self]
  simp [mass]

/-- `μ(occ(d_E)) = ¼` under `(1,2)` at `p = ¾`. Source: `firstperson.md` FP-22′ ("`occ = ¼`").
Kind: L -/
theorem tnV1_E_occ_mass :
    mass tnOneTwo (tnV1 (3/4) (by norm_num) (by norm_num) 4 1) (occ .E _) = 1 / 4 := by
  rw [mass_eq_sum_ite', tnV1_sum]
  simp only [mem_occ, tnV1_count_E, tnV1_leafLaw]
  simp [box_sum_univ, Fin.sum_univ_two, tnOneTwo]
  norm_num

/-- **V1, `d_F` fails**: `μ(occ(d_F) ∖ λ⁻¹O_F) = ¼ ≠ 0` (the hypothetical root query of `d_F`
on empty-box runs).
Source: `firstperson.md` FP-22′ ("V1's `d_F` … fail")
Kind: N+ -/
theorem tnV1_F_license_fails :
    ¬ License tnObs tnOneTwo (tnV1 (3/4) (by norm_num) (by norm_num) 4 1) .F := by
  rintro ⟨h, -⟩
  unfold VeridicalASAt at h
  rw [mass_eq_sum_ite', tnV1_sum] at h
  simp only [Finset.mem_sdiff, mem_occ, worldEv, Finset.mem_filter, Finset.mem_univ, true_and,
    tnV1_count_F, tnV1_world, tnV1_leafLaw, tnObs] at h
  simp [box_sum_univ, Fin.sum_univ_two, tnOneTwo] at h <;> norm_num at h

/-- **V2, `d_E` fails** under `(1,1)`: `occ(d_E) = Leaves` while `ν(O_E) = ¼ < 1`.
Source: `firstperson.md` FP-22′ ("both V2 points fail (`occ = Leaves`)")
Kind: N+ -/
theorem tnV2_E_license_fails :
    ¬ License tnObs procLarge (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) .E := by
  rintro ⟨h, -⟩
  unfold VeridicalASAt at h
  rw [tnV2_occ_E, mass_eq_sum_ite', tnV2_sum] at h
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, worldEv, Finset.mem_filter,
    tnV2_world, tnV2_leafLaw, tnObs] at h
  simp [box_sum_univ, Fin.sum_univ_two, procLarge] at h <;> norm_num at h

/-- **V2, `d_F` fails** under `(1,1)`: `occ(d_F) = Leaves` while `ν(O_F) = ¾ < 1`.
Source: `firstperson.md` FP-22′
Kind: N+ -/
theorem tnV2_F_license_fails :
    ¬ License tnObs procLarge (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) .F := by
  rintro ⟨h, -⟩
  unfold VeridicalASAt at h
  rw [tnV2_occ_F, mass_eq_sum_ite', tnV2_sum] at h
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, worldEv, Finset.mem_filter,
    tnV2_world, tnV2_leafLaw, tnObs] at h
  simp [box_sum_univ, Fin.sum_univ_two, procLarge] at h <;> norm_num at h

end fp22

/-! ## T5(e): the four-row grade table -/

section table

/-- The half-half self-model on the Newcomb points (`m = ½`). Source: `anticipation.md` AN-8
table ("TN-V1, `m = ½`"). Kind: D -/
def tnHalf : Proc TnPt (fun _ => Box) ℚ := fun _ => FinDistr.uniform

/-- `Fintype.card Box = 2`. Source: none: infrastructure. Kind: L -/
theorem box_card : (Fintype.card Box : ℚ) = 2 := by
  rw [Fintype.card_eq_sum_ones, box_sum_univ]; norm_num

/-- **Row `B₁`, `q = q₀`, grade (ii) fails**: `μ(occ(d)) = 1 > ½ = ν(O_T)` (density `2 > 1`).
Source: `anticipation.md` AN-8 table (`B₁`: "`2 > 1` fail")
Kind: N+ -/
theorem mug1_grade2_fails (x y q₀ : ℚ) (h0 : 0 < q₀) (h1 : q₀ < 1) :
    ¬ mass (procQ q₀ h0.le h1.le) (mug1 x y) (occ () (mug1 x y)) ≤
      nu (procQ q₀ h0.le h1.le) (mug1 x y) (mugObs ()) := by
  rw [mug1_occ, mass_univ, mug1_nu_obs]; norm_num

/-- **Row `B₁`, grade (iii) fails**: `μ(occ(d) ∖ λ⁻¹O_T) = ½` (the heads runs).
Source: `anticipation.md` AN-8 table (`B₁`: "fail")
Kind: N+ -/
theorem mug1_grade3_fails (x y q₀ : ℚ) (h0 : 0 < q₀) (h1 : q₀ < 1) :
    ¬ License mugObs (procQ q₀ h0.le h1.le) (mug1 x y) () := by
  rintro ⟨h, -⟩
  unfold VeridicalASAt at h
  rw [mug1_occ, mass_eq_sum_ite', mug1_sum] at h
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, worldEv, Finset.mem_filter] at h
  simp [Fin.sum_univ_two, Act2.sum_univ, mug1, mugWorld1, mugObs, FinDistr.fair, FinDistr.coin,
    procQ, leafLaw_chance, leafLaw_decision, world_chance, world_decision] at h <;> linarith

/-- `ν(O_E) = ½` on V1 under `m = ½`. Source: none: infrastructure. Kind: L -/
theorem tnV1_half_nu_E (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) :
    nu tnHalf (tnV1 p h0 h1 L S) (tnObs .E) = 1 / 2 := by
  rw [nu_eq_sum, tnV1_sum]
  simp only [tnV1_world, tnV1_leafLaw, tnObs]
  simp [box_sum_univ, Fin.sum_univ_two, tnHalf, FinDistr.uniform_w, box_card]
  ring

/-- `ν(O_F) = ½` on V1 under `m = ½`. Source: none: infrastructure. Kind: L -/
theorem tnV1_half_nu_F (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) :
    nu tnHalf (tnV1 p h0 h1 L S) (tnObs .F) = 1 / 2 := by
  rw [nu_eq_sum, tnV1_sum]
  simp only [tnV1_world, tnV1_leafLaw, tnObs]
  simp [box_sum_univ, Fin.sum_univ_two, tnHalf, FinDistr.uniform_w, box_card]
  ring

/-- **Row TN-V1 `d_E` at `m = ½`: grade (ii) passes** (`μ(occ(d_E)) = ν(O_E) = ½`) **and grade
(iii) passes** (`occ(d_E) = λ⁻¹O_E`).
Source: `anticipation.md` AN-8 table ("TN-V1, `m = ½`, `d_E`: `2 ≤ 2` pass / pass")
Kind: N+ -/
theorem tnV1_E_grades (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) :
    mass tnHalf (tnV1 p h0 h1 L S) (occ .E _) ≤ nu tnHalf (tnV1 p h0 h1 L S) (tnObs .E) ∧
    License tnObs tnHalf (tnV1 p h0 h1 L S) .E := by
  constructor
  · rw [tnV1_occ_E_eq]; exact le_rfl
  · unfold License VeridicalASAt CoversAS
    rw [tnV1_occ_E_eq, Finset.sdiff_self]
    simp [mass]

/-- **Row TN-V1 `d_F` at `m = ½`: grade (ii) fails** (`μ(occ(d_F)) = 1 > ½ = ν(O_F)`) **and
grade (iii) fails** (`μ(occ(d_F) ∖ λ⁻¹O_F) = ½`).
Source: `anticipation.md` AN-8 table ("TN-V1, `m = ½`, `d_F`: `2 > 1` fail / fail")
Kind: N+ -/
theorem tnV1_F_grades (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) :
    ¬ mass tnHalf (tnV1 p h0 h1 L S) (occ .F _) ≤ nu tnHalf (tnV1 p h0 h1 L S) (tnObs .F) ∧
    ¬ License tnObs tnHalf (tnV1 p h0 h1 L S) .F := by
  constructor
  · rw [tnV1_occ_F, mass_univ, tnV1_half_nu_F]; norm_num
  · rintro ⟨h, -⟩
    unfold VeridicalASAt at h
    rw [tnV1_occ_F, mass_eq_sum_ite', tnV1_sum] at h
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, worldEv, Finset.mem_filter,
      tnV1_world, tnV1_leafLaw, tnObs] at h
    simp [box_sum_univ, Fin.sum_univ_two, tnHalf, FinDistr.uniform_w, box_card] at h <;> linarith

/-- The tremble `C₀^{1/10}` of Told-You-So's zero-respecting procedure.
Source: `anticipation.md` AN-8 table ("Told-You-So, `C₀^{0.1}`")
Kind: D -/
def tysTremble : Proc Five10 (fun _ => Five10) ℚ :=
  tremble procFiveTen (1/10) (by norm_num) (by norm_num)

/-- `ν(O₅) = 19/20` under `C₀^{1/10}`. Source: `anticipation.md` AN-8 ("`ν(O₅) = 19/20`").
Kind: L -/
theorem tysTremble_nu_O5 : nu tysTremble toldYouSo (tysObs .five) = 19 / 20 := by
  rw [tys_nu]
  simp [tysObs, tysTremble, tremble_w, procFiveTen, five10_card]
  norm_num

/-- Row Told-You-So `d₅` under `C₀^{1/10}`: `s₅ = δ_{(5,5)}` is strict-OC at `d₅`
(`C(d₅)(5) = 19/20 > 0`) — the row's instance of `tys_five_strictOCAt_of_pos`, so grade (i)
passes the row by `strictClausesAt_reachable`.
Source: `anticipation.md` AN-8 table; audit r1 fidelity N10(ii). Kind: N+ -/
theorem tysTremble_five_strictOCAt : StrictOCAt tysState tysObs tysTremble toldYouSo .five :=
  tys_five_strictOCAt_of_pos tysTremble (by
    simp [tysTremble, tremble_w, procFiveTen, five10_card] <;> norm_num)

/-- **Row Told-You-So `d₅` under `C₀^{1/10}`: grade (ii) fails** (`μ(occ(d₅)) = 1 > 19/20`,
density `20/19 > 1`) **and grade (iii) fails** (`μ(occ(d₅) ∖ λ⁻¹O₅) = 1/20`: the selected
observation is caught).
Source: `anticipation.md` AN-8 table ("Told-You-So, `C₀^{0.1}`, `d₅`: `20/19 > 1` fail / fail")
Kind: N+ -/
theorem tys_five_grades :
    ¬ mass tysTremble toldYouSo (occ .five toldYouSo) ≤ nu tysTremble toldYouSo (tysObs .five) ∧
    ¬ License tysObs tysTremble toldYouSo .five := by
  constructor
  · rw [tys_occ_five, mass_univ, tysTremble_nu_O5]; norm_num
  · rintro ⟨h, -⟩
    unfold VeridicalASAt at h
    rw [tys_occ_five, mass_eq_sum_ite', tys_sum] at h
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, worldEv, Finset.mem_filter] at h
    simp [toldYouSo, leafLaw_decision, world_decision, tysObs, tysTremble, tremble_w, procFiveTen,
      five10_card] at h <;> norm_num at h

end table

end Cleanroom.Decision.DpFirstpersonSc

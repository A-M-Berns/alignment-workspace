import Cleanroom.Decision.DpSmokingLesion.General

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

/-!
# T1: Lemma 3 as printed refuted; the repaired lemma; the flipped table

[[dp-smoking-lesion-mandate]] T1 (load-bearing 1), source [[decision-problems-v2]] §7.3 line 256.

* **(a) Coverage-failure refutation** (`lemma3_printed_refuted_coverage`): on counterexample A
  at `π = ρ = ½`, `γ = (99/100, 1/100)`, `C = δ_refrain`, every run meets `d` at most once
  (`cexA_count_le_one`), the printed hypothesis shape holds by construction, yet
  `ν(k ∧ m=1) · ν(m=0) = 99/400 · ¾ ≠ 101/400 · ¼ = ν(k ∧ m=0) · ν(m=1)`, so
  "`m ⊥ (ℓ, k)` under `ν_{B,C}` for every `C`" fails; the `A`-runs satisfy `O_d = ⊤` and meet
  no `d`-node, so coverage — hence recording — fails (`cexA_not_covers`, `cexA_not_recordsFor`).
  The run-level clause (the draw at `d` independent of the lesion on the runs consulting `d`)
  holds there at `C(d) = ½` (`cexA_draw_indep_lesion`): the printed lemma's first clause is true
  and its second false on one tree, as `dp-core-tree`'s overwrite tree shows for the other
  recording failure (action-veridicality). The two trees are the two homes' first appearance.
* **(b) Repaired lemma, shape form** (`lemma3_repaired_shape`): on `slOne` for every `C` and
  every parameter, the `ℓ`-clause, the `k`-clause and the joint clause, from `leafLaw`
  (`slOne_leafLaw`); N+ at interior `C(d)`, `ρ`, `γ` (`lemma3_repaired_shape_instance`).
* **(c) Repaired lemma, predicate form**: `General.lean`'s `postQuery_screening_recorded` /
  `nuFlat_of_recordsFor_postQueryIndep` (the `k`-clause under `RecordsFor` + `PostQueryIndep`)
  and `dp-core-tree`'s `screening_recorded` with `X = evL` (the `ℓ`-clause); instantiated here on
  `slOne` through `slOne_recordsFor` and `slOne_lesionOnlyAt` (`lemma3_repaired_predicate_slOne`).
* **(d) The flipped table** (`slOneCausal_S2_at_strict`): a recorded one-point tree whose
  cancer coin depends on the act has (S2) true at its strictly calibrated state when
  `κ₀ < κ₁` — (S1)'s lesion-only clause is load-bearing even under recording.
-/

namespace Cleanroom.Decision.DpSmokingLesion

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration

/-! ## One-point procedures on `Bool` -/

/-- The one-point procedure `C(d)(smoke) = q`.
Source: none: infrastructure (`q := C(d)(m = 1)` throughout the sources)
Kind: D -/
def procBool (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : Proc Unit (fun _ => Bool) ℚ :=
  fun _ => FinDistr.bool q h0 h1

/-- The deterministic refrainer `δ_refrain`. Source: [[decision-problems-v2]] §7.3. Kind: D -/
def procRefrain : Proc Unit (fun _ => Bool) ℚ := fun _ => FinDistr.pure false

/-- The deterministic smoker `δ_smoke`. Source: [[decision-problems-v2]] §7.3. Kind: D -/
def procSmoke : Proc Unit (fun _ => Bool) ℚ := fun _ => FinDistr.pure true

/-- The weight of refraining is one minus the weight of smoking.
Source: none: infrastructure. Kind: L -/
theorem w_false_eq_one_sub (C : Proc Unit (fun _ => Bool) ℚ) :
    (C ()).w false = 1 - (C ()).w true := by
  have := (C ()).sum_one
  rw [Fintype.sum_bool] at this
  linarith

/-! ## `slOne`: masses, statistics, recording -/

section slOne

variable (L : Lesion) (α β : ℚ)

/-- A sum over the leaves of `slOne` as a triple sum over `(ℓ, m, k)`.
Source: none: infrastructure. Kind: L -/
theorem slOne_sum (f : (slOne L α β).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ∑ m : Bool, ∑ j : Fin 2, f ⟨i, m, j, ()⟩ := by
  unfold slOne kBlock slLeaf at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- **The eight leaf masses of `slOne` from `leafLaw`**: `μ(ℓ, m, k) = P(ℓ) · C(d)(m) · P(k ∣ ℓ)`.
Source: [[decision-problems-v2]] §3.1 Definition 6 on the enumerated instantiation
Kind: P
Fidelity: exact -/
theorem slOne_leafLaw (C : Proc Unit (fun _ => Bool) ℚ) (i : Fin 2) (m : Bool) (j : Fin 2) :
    leafLaw C (slOne L α β) ⟨i, m, j, ()⟩ =
      (if i = 0 then L.ρ else 1 - L.ρ) * (C ()).w m *
        (if i = 0 then (if j = 0 then L.γ₁ else 1 - L.γ₁)
          else (if j = 0 then L.γ₀ else 1 - L.γ₀)) := by
  unfold slOne kBlock slLeaf
  simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf, Lesion.coinL, Lesion.coinK,
    FinDistr.coin, tickleGamma]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The world at a leaf of `slOne`. Source: none: infrastructure. Kind: L -/
theorem slOne_world (i : Fin 2) (m : Bool) (j : Fin 2) :
    world (slOne L α β) ⟨i, m, j, ()⟩ = (decide (i = 0), m, decide (j = 0)) := rfl

/-- The payoff at a leaf of `slOne`. Source: none: infrastructure. Kind: L -/
theorem slOne_payoff (i : Fin 2) (m : Bool) (j : Fin 2) :
    payoff (slOne L α β) ⟨i, m, j, ()⟩ = ticklePay α β (decide (i = 0), m, decide (j = 0)) := rfl

/-- `ν` on `slOne` as an explicit eight-term sum. Source: none: infrastructure. Kind: L -/
theorem slOne_nu (C : Proc Unit (fun _ => Bool) ℚ) (X : Finset TickleW) :
    nu C (slOne L α β) X =
      ∑ i : Fin 2, ∑ m : Bool, ∑ j : Fin 2,
        if (decide (i = 0), m, decide (j = 0)) ∈ X then leafLaw C (slOne L α β) ⟨i, m, j, ()⟩
        else 0 := by
  rw [nu_eq_sum, slOne_sum]
  rfl

/-- `paySum` on `slOne` as an explicit eight-term sum. Source: none: infrastructure. Kind: L -/
theorem slOne_paySum (C : Proc Unit (fun _ => Bool) ℚ) (X : Finset TickleW) :
    paySum C (slOne L α β) X =
      ∑ i : Fin 2, ∑ m : Bool, ∑ j : Fin 2,
        if (decide (i = 0), m, decide (j = 0)) ∈ X then
          leafLaw C (slOne L α β) ⟨i, m, j, ()⟩ * ticklePay α β (decide (i = 0), m, decide (j = 0))
        else 0 := by
  rw [paySum_eq_sum_ite, slOne_sum]
  rfl

variable (C : Proc Unit (fun _ => Bool) ℚ)

/-- `ν(m) = C(d)(m)`: the act statistics are the label (the recording argument, computed).
Source: [[decision-problems-v2]] Remark 3.6
Kind: L -/
theorem slOne_nu_m (m : Bool) : nu C (slOne L α β) (evM m) = (C ()).w m := by
  rw [slOne_nu]
  simp only [Fin.sum_univ_two, Fintype.sum_bool, slOne_leafLaw, mem_evM]
  cases m <;> simp <;> ring

/-- `ν(k ∧ m) = C(d)(m) · (ρ γ₁ + (1−ρ) γ₀)`. Source: dp-sl-008. Kind: L -/
theorem slOne_nu_k_m (m : Bool) :
    nu C (slOne L α β) (evK ∩ evM m) = (C ()).w m * (L.ρ * L.γ₁ + (1 - L.ρ) * L.γ₀) := by
  rw [slOne_nu]
  simp only [Fin.sum_univ_two, Fintype.sum_bool, slOne_leafLaw, Finset.mem_inter, mem_evM, mem_evK]
  cases m <;> simp <;> ring

/-- `ν(ℓ ∧ m) = ρ · C(d)(m)`. Source: dp-sl-008. Kind: L -/
theorem slOne_nu_l_m (m : Bool) : nu C (slOne L α β) (evL ∩ evM m) = L.ρ * (C ()).w m := by
  rw [slOne_nu]
  simp only [Fin.sum_univ_two, Fintype.sum_bool, slOne_leafLaw, Finset.mem_inter, mem_evM, mem_evL]
  cases m <;> simp <;> ring

/-- `ν(ℓ) = ρ`. Source: dp-sl-008. Kind: L -/
theorem slOne_nu_l : nu C (slOne L α β) evL = L.ρ := by
  rw [slOne_nu]
  simp only [Fin.sum_univ_two, Fintype.sum_bool, slOne_leafLaw, mem_evL]
  have := w_false_eq_one_sub C
  simp; rw [this]; ring

/-- `ν(k) = ρ γ₁ + (1−ρ) γ₀`. Source: dp-sl-008. Kind: L -/
theorem slOne_nu_k : nu C (slOne L α β) evK = L.ρ * L.γ₁ + (1 - L.ρ) * L.γ₀ := by
  rw [slOne_nu]
  simp only [Fin.sum_univ_two, Fintype.sum_bool, slOne_leafLaw, mem_evK]
  have := w_false_eq_one_sub C
  simp; rw [this]; ring

/-- `ν(ℓ ∧ k ∧ m) = ρ γ₁ · C(d)(m)`. Source: dp-sl-008. Kind: L -/
theorem slOne_nu_lk_m (m : Bool) :
    nu C (slOne L α β) (evL ∩ evK ∩ evM m) = L.ρ * L.γ₁ * (C ()).w m := by
  rw [slOne_nu]
  simp only [Fin.sum_univ_two, Fintype.sum_bool, slOne_leafLaw, Finset.mem_inter, mem_evM, mem_evK,
    mem_evL]
  cases m <;> simp <;> ring

/-- `ν(ℓ ∧ k) = ρ γ₁`. Source: dp-sl-008. Kind: L -/
theorem slOne_nu_lk : nu C (slOne L α β) (evL ∩ evK) = L.ρ * L.γ₁ := by
  rw [slOne_nu]
  simp only [Fin.sum_univ_two, Fintype.sum_bool, slOne_leafLaw, Finset.mem_inter, mem_evK, mem_evL]
  have := w_false_eq_one_sub C
  simp; rw [this]; ring

/-- **The repaired Lemma 3, shape form**: on the enumerated instantiation `slOne`, for every
procedure `C` and every `ρ, γ₁, γ₀ ∈ [0, 1]`: the lesion is independent of the act
(`ν(ℓ ∧ m) · ν(⊤) = ν(ℓ) · ν(m)`), the act-conditionals of cancer are flat
(`ν(k ∧ m=1) · ν(m=0) = ν(k ∧ m=0) · ν(m=1)`), and jointly `ν(ℓ ∧ k ∧ m) = ν(ℓ ∧ k) · ν(m)` —
all derived from `leafLaw` (the product of the coin weights and `C(d)(m)`), never from stated
leaf masses.
Source: [[decision-problems-v2]] §7.3 Lemma 3 ("under (S1)+(S3), `m ⊥ (ℓ, k)` under
`ν_{B,C}` for every `C`"), read under (S4) = the enumerated shape; `sl-synthesis.md` §1.3
("under (S1)+(S3)+(S4) `m ⊥ (ℓ, k)`"); mandate T1(b)
Kind: C
Fidelity: exact on the enumerated instantiation; weaker: shape family as a claim about
"every instantiation" (the predicate form is `postQuery_screening_recorded`)
Hyps: none -/
theorem lemma3_repaired_shape :
    NuLesionIndep C (slOne L α β) ∧ NuFlat C (slOne L α β) ∧
      ∀ m, nu C (slOne L α β) (evL ∩ evK ∩ evM m) =
        nu C (slOne L α β) (evL ∩ evK) * nu C (slOne L α β) (evM m) := by
  refine ⟨fun m => ?_, ?_, fun m => ?_⟩
  · rw [slOne_nu_l_m, nu_univ, slOne_nu_l, slOne_nu_m]; ring
  · unfold NuFlat
    rw [slOne_nu_k_m, slOne_nu_k_m, slOne_nu_m, slOne_nu_m]; ring
  · rw [slOne_nu_lk_m, slOne_nu_lk, slOne_nu_m]

/-- **N+ for the repaired lemma**: at the FDT numbers and the interior label `C(d) = ½`, the
four masses of the `k`-clause are `ν(k ∧ m=1) = ¼`, `ν(m=0) = ½`, `ν(k ∧ m=0) = ¼`,
`ν(m=1) = ½` (all positive; the identity is `⅛ = ⅛`), and `ν(ℓ ∧ m=1) = ¼ = ν(ℓ) · ν(m=1)`.
Source: mandate T1(b) ("its N+ is the tree at `C(d) = q` interior")
Kind: N+ -/
theorem lemma3_repaired_shape_instance :
    nu (procBool (1/2) (by norm_num) (by norm_num)) (slOne Lesion.fdt 1000 1000000)
        (evK ∩ evM true) = 1/4 ∧
    nu (procBool (1/2) (by norm_num) (by norm_num)) (slOne Lesion.fdt 1000 1000000) (evM false) =
      1/2 ∧
    nu (procBool (1/2) (by norm_num) (by norm_num)) (slOne Lesion.fdt 1000 1000000)
        (evK ∩ evM false) = 1/4 ∧
    nu (procBool (1/2) (by norm_num) (by norm_num)) (slOne Lesion.fdt 1000 1000000) (evM true) =
      1/2 ∧
    nu (procBool (1/2) (by norm_num) (by norm_num)) (slOne Lesion.fdt 1000 1000000)
        (evL ∩ evM true) = 1/4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [slOne_nu_k_m]; simp [procBool, Lesion.fdt]; norm_num
  · rw [slOne_nu_m]; simp [procBool]; norm_num
  · rw [slOne_nu_k_m]; simp [procBool, Lesion.fdt]; norm_num
  · rw [slOne_nu_m]; simp [procBool]
  · rw [slOne_nu_l_m]; simp [procBool, Lesion.fdt]; norm_num

/-- Every run of `slOne` meets `d` exactly once. Source: none: infrastructure. Kind: L -/
theorem slOne_count (ℓ : (slOne L α β).Leaves) : count () (slOne L α β) ℓ = 1 := by
  unfold slOne kBlock slLeaf at ℓ ⊢
  rcases ℓ with ⟨i, m, j, _⟩
  rfl

/-- `occ(d)` on `slOne` is every run. Source: none: infrastructure. Kind: L -/
theorem slOne_occ : occ () (slOne L α β) = Finset.univ := by
  ext ℓ; simp [slOne_count]

/-- `slOne` is almost fair. Source: none: infrastructure. Kind: L -/
theorem slOne_almostFair : AlmostFair (slOne L α β) := by
  intro d ℓ
  cases d
  exact (slOne_count L α β ℓ).le

/-- **`slOne` records at `d` for every procedure** (Definition 7 at `O_d = ⊤`): the unique
`d`-node of each lesion branch is subtree-veridical (trivially, `O_d = ⊤`), its instance is
action-veridical (the leaf's `m` is the draw) and the leaf satisfies only the drawn action's
event.
Source: [[decision-problems-v2]] Definition 7 on the enumerated instantiation ("act `m`" =
(S4)); mandate §3.7 ("`RecordsFor` for every `C` is a theorem")
Kind: N+ -/
theorem slOne_recordsFor : RecordsFor slObs slActEv C (slOne L α β) () := by
  intro ℓ _ _
  refine ⟨slOne_count L α β ℓ, ?_⟩
  unfold slOne kBlock slLeaf at ℓ ⊢
  rcases ℓ with ⟨i, m, j, _⟩
  rintro ⟨i', (_ | ⟨m', ⟨j', e⟩⟩)⟩ hq a ha
  · by_cases hi : i = i'
    · subst hi
      simp only [edgeOf_chance, dite_true, edgeOf_decision_none, Option.some.injEq] at ha
      subst ha
      refine ⟨?_, ?_, ?_⟩
      · intro ℓ' _; simp [slObs]
      · simp [slActEv, evM]
      · intro a' ha'
        simp [slActEv, evM] at ha'
        exact ha'.symm
    · simp [edgeOf_chance, hi] at ha
  · exact e.elim

/-- `slOne` records at `d` for every procedure (the quantifier form `RecordsForAll`).
Source: mandate §3.7
Kind: L -/
theorem slOne_recordsForAll : RecordsForAll slObs slActEv (slOne L α β) () :=
  fun C => slOne_recordsFor L α β C

/-- `H*` holds on `slOne` for every procedure (`O_d = ⊤`).
Source: mandate §3.3
Kind: L -/
theorem slOne_hStar : HStar slObs slActEv C (slOne L α β) () :=
  (hStar_iff_recordsFor_slObs C (slOne L α β) ()).mpr (slOne_recordsFor L α β C)

/-- The edge mass at the `d`-node of lesion branch `i`, restricted to an event.
Source: none: infrastructure. Kind: L -/
theorem slOne_edgeMassIn (i : Fin 2) (X : Finset TickleW) (a : Bool) :
    edgeMassIn C (slOne L α β) X ⟨i, none⟩ a =
      ∑ j : Fin 2, if (decide (i = 0), a, decide (j = 0)) ∈ X then
        leafLaw C (slOne L α β) ⟨i, a, j, ()⟩ else 0 := by
  unfold edgeMassIn
  rw [slOne_sum]
  rw [Finset.sum_eq_single i]
  · rw [Fintype.sum_bool]
    have hne : ∀ m, m ≠ a → (∑ j : Fin 2, if edgeOf (slOne L α β) ⟨i, none⟩ ⟨i, m, j, ()⟩ = some a ∧
        world (slOne L α β) ⟨i, m, j, ()⟩ ∈ X then leafLaw C (slOne L α β) ⟨i, m, j, ()⟩ else 0)
        = 0 := by
      intro m hm
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg]
      rintro ⟨h, -⟩
      unfold slOne kBlock slLeaf at h
      simp [edgeOf_chance, edgeOf_decision_none] at h
      exact hm h
    have hyes : (∑ j : Fin 2, if edgeOf (slOne L α β) ⟨i, none⟩ ⟨i, a, j, ()⟩ = some a ∧
        world (slOne L α β) ⟨i, a, j, ()⟩ ∈ X then leafLaw C (slOne L α β) ⟨i, a, j, ()⟩ else 0)
        = ∑ j : Fin 2, if (decide (i = 0), a, decide (j = 0)) ∈ X then
          leafLaw C (slOne L α β) ⟨i, a, j, ()⟩ else 0 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      have he : edgeOf (slOne L α β) ⟨i, none⟩ ⟨i, a, j, ()⟩ = some a := by
        unfold slOne kBlock slLeaf; simp [edgeOf_chance, edgeOf_decision_none]
      rw [he, slOne_world]
      simp
    cases a
    · rw [hne true (by decide), zero_add, hyes]
    · rw [hne false (by decide), add_zero, hyes]
  · intro i' _ hi'
    apply Finset.sum_eq_zero
    intro m _
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    rintro ⟨h, -⟩
    unfold slOne kBlock slLeaf at h
    simp [edgeOf_chance, hi'] at h
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The lesion is decided at the `d`-node of each branch, and `lesionOf` reads it off.
Source: none: infrastructure. Kind: L -/
theorem slOne_lesionOf (i : Fin 2) :
    DecidedAt (slOne L α β) ⟨i, none⟩ evL ∧ lesionOf (slOne L α β) ⟨i, none⟩ = decide (i = 0) := by
  have hbelow : ∀ ℓ : (slOne L α β).Leaves, ℓ ∈ leavesBelow (slOne L α β) ⟨i, none⟩ →
      (world (slOne L α β) ℓ ∈ evL ↔ i = 0) := by
    intro ℓ hℓ
    rw [mem_leavesBelow] at hℓ
    unfold slOne kBlock slLeaf at ℓ hℓ ⊢
    rcases ℓ with ⟨i', m, j, _⟩
    by_cases hi : i' = i
    · subst hi; simp [mem_evL]
    · simp [edgeOf_chance, hi] at hℓ
  constructor
  · by_cases hi : i = 0
    · left; intro ℓ hℓ; exact (hbelow ℓ hℓ).mpr hi
    · right; intro ℓ hℓ h; exact hi ((hbelow ℓ hℓ).mp h)
  · unfold lesionOf
    by_cases hi : i = 0
    · simp only [hi, decide_true, decide_eq_true_eq]
      intro ℓ hℓ; exact (hbelow ℓ hℓ).mpr hi
    · have hmem : (⟨i, true, 0, ()⟩ : (slOne L α β).Leaves) ∈
          leavesBelow (slOne L α β) ⟨i, none⟩ :=
        (mem_leavesBelow (slOne L α β) ⟨i, none⟩ ⟨i, true, 0, ()⟩).mpr (by
          unfold slOne kBlock slLeaf; simp [edgeOf_chance])
      simp only [hi, decide_false, decide_eq_false_iff_not, not_forall]
      exact ⟨⟨i, true, 0, ()⟩, hmem, fun h => hi ((hbelow _ hmem).mp h)⟩

/-- **`slOne` satisfies the predicate form of (S1)** (`LesionOnlyAt`) for every procedure: at
each `d`-node the lesion is decided and the cancer mass below every action edge is
`γ_{ℓ(q)}` times the edge mass — so the predicate form of the repaired lemma is inhabited on
the enumerated instantiation.
Source: mandate §3.2(ii); T1(c)
Kind: N+ -/
theorem slOne_lesionOnlyAt : LesionOnlyAt L C (slOne L α β) () := by
  rintro ⟨i, (_ | ⟨m', ⟨j', e⟩⟩)⟩ _
  · refine ⟨(slOne_lesionOf L α β i).1, fun a => ?_⟩
    rw [(slOne_lesionOf L α β i).2]
    have hm : edgeMass C (slOne L α β) ⟨i, none⟩ a =
        ∑ j : Fin 2, leafLaw C (slOne L α β) ⟨i, a, j, ()⟩ := by
      have := slOne_edgeMassIn L α β C i Finset.univ a
      unfold edgeMassIn at this
      unfold edgeMass
      simp only [Finset.mem_univ, and_true] at this
      rw [this]
      simp
    rw [hm, slOne_edgeMassIn]
    simp only [Fin.sum_univ_two, slOne_leafLaw, mem_evK, tickleGamma]
    fin_cases i <;> simp <;> ring
  · exact e.elim

/-- **The repaired lemma on `slOne` through the general theorems** (T1(c) instantiated): the
`k`-clause from `nuFlat_of_recordsFor_postQueryIndep` with `slOne_recordsFor` and
`slOne_lesionOnlyAt`, and the `ℓ`-clause from `dp-core-tree`'s `screening_recorded` with
`X = evL` (pre-query on `slOne`).
Source: mandate T1(c)
Kind: C
Fidelity: exact
Hyps: none (recording and the lesion-only clause are theorems on `slOne`) -/
theorem lemma3_repaired_predicate_slOne :
    NuFlat C (slOne L α β) ∧
      ∀ m, nu C (slOne L α β) (evL ∩ evM m ∩ Finset.univ) * nu C (slOne L α β) Finset.univ =
        nu C (slOne L α β) (evL ∩ Finset.univ) * nu C (slOne L α β) (evM m ∩ Finset.univ) := by
  refine ⟨nuFlat_of_recordsFor_postQueryIndep C (slOne L α β) () (slOne_recordsFor L α β C)
    (slOne_lesionOnlyAt L α β C).postQueryIndep, fun m => ?_⟩
  have hpre : PreQuery slObs C (slOne L α β) () evL := by
    intro ℓ _ _ q _ hq
    rcases q with ⟨i, (_ | ⟨m', ⟨j', e⟩⟩)⟩
    · exact (slOne_lesionOf L α β i).1
    · exact e.elim
  exact screening_recorded slObs slActEv (slOne_recordsFor L α β C) hpre m

end slOne

/-! ## Counterexample A: coverage failure refutes the printed lemma -/

section cexA

/-- The parameters of counterexample A: `π = ½`, the FDT lesion, `α = 1000`, `β = 10⁶`.
Source: `adv_l1_counterexamples.py` lines 15–16
Kind: D -/
def cexA₀ : Tree TickleW Unit (fun _ => Bool) ℚ :=
  cexA (1/2) (by norm_num) (by norm_num) Lesion.fdt 1000 1000000

/-- A sum over the leaves of `cexA₀`: the eight `E`-leaves and the four `A`-leaves.
Source: none: infrastructure. Kind: L -/
theorem cexA_sum (f : cexA₀.Leaves → ℚ) :
    ∑ ℓ, f ℓ = (∑ m : Bool, ∑ i : Fin 2, ∑ j : Fin 2, f ⟨0, m, i, j, ()⟩) +
      ∑ i : Fin 2, ∑ j : Fin 2, f ⟨1, i, j, ()⟩ := by
  unfold cexA₀ cexA kBlock slLeaf at f ⊢
  rw [sum_leaves_chance, Fin.sum_univ_two]
  show (∑ ℓ : (Tree.decision () fun m => Tree.chance 2 Lesion.fdt.coinL fun i =>
      Tree.chance 2 (Lesion.fdt.coinK (decide (i = 0))) fun j =>
        Tree.leaf (decide (i = 0), m, decide (j = 0))
          (ticklePay 1000 1000000 (decide (i = 0), m, decide (j = 0))) :
      Tree TickleW Unit (fun _ => Bool) ℚ).Leaves, f ⟨0, ℓ⟩) +
    (∑ ℓ : (Tree.chance 2 Lesion.fdt.coinL fun i =>
      Tree.chance 2 (Lesion.fdt.coinK (decide (i = 0))) fun j =>
        Tree.leaf (decide (i = 0), decide (i = 0), decide (j = 0))
          (ticklePay 1000 1000000 (decide (i = 0), decide (i = 0), decide (j = 0))) :
      Tree TickleW Unit (fun _ => Bool) ℚ).Leaves, f ⟨1, ℓ⟩) = _
  congr 1
  · rw [sum_leaves_decision]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Tree.sum_leaves_leaf _ _ _
  · rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Tree.sum_leaves_leaf _ _ _

/-- The `E`-leaf masses of `cexA₀` under any procedure: `μ(E; m, ℓ, k) = ½ · C(d)(m) · ½ · γ_{ℓ,k}`.
Source: `adv_l1_counterexamples.py` (the tree); Definition 6
Kind: L -/
theorem cexA_leafLaw_E (C : Proc Unit (fun _ => Bool) ℚ) (m : Bool) (i j : Fin 2) :
    leafLaw C cexA₀ ⟨0, m, i, j, ()⟩ =
      (1/2 : ℚ) * (C ()).w m * (1/2) *
        (if i = 0 then (if j = 0 then 99/100 else 1/100) else (if j = 0 then 1/100 else 99/100)) := by
  unfold cexA₀ cexA
  rw [leafLaw_chance]
  show (FinDistr.coin (1/2) _ _).w 0 * leafLaw C (Tree.decision () fun m =>
    Tree.chance 2 Lesion.fdt.coinL fun i => kBlock Lesion.fdt 1000 1000000 (decide (i = 0)) m)
      ⟨m, i, j, ()⟩ = _
  unfold kBlock slLeaf
  simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf, Lesion.coinL, Lesion.coinK,
    FinDistr.coin, tickleGamma, Lesion.fdt]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The `A`-leaf masses of `cexA₀` under any procedure: `μ(A; ℓ, k) = ½ · ½ · γ_{ℓ,k}` (the
automaton's act is the lesion; no draw).
Source: `adv_l1_counterexamples.py` (the tree); Definition 6
Kind: L -/
theorem cexA_leafLaw_A (C : Proc Unit (fun _ => Bool) ℚ) (i j : Fin 2) :
    leafLaw C cexA₀ ⟨1, i, j, ()⟩ =
      (1/2 : ℚ) * (1/2) *
        (if i = 0 then (if j = 0 then 99/100 else 1/100) else (if j = 0 then 1/100 else 99/100)) := by
  unfold cexA₀ cexA
  rw [leafLaw_chance]
  show (FinDistr.coin (1/2) _ _).w 1 * leafLaw C (Tree.chance 2 Lesion.fdt.coinL fun i =>
    kBlock Lesion.fdt 1000 1000000 (decide (i = 0)) (decide (i = 0))) ⟨i, j, ()⟩ = _
  unfold kBlock slLeaf
  simp only [leafLaw_chance, leafLaw_leaf, Lesion.coinL, Lesion.coinK, FinDistr.coin, tickleGamma,
    Lesion.fdt]
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

/-- The worlds at the leaves of `cexA₀`. Source: none: infrastructure. Kind: L -/
theorem cexA_world :
    (∀ (m : Bool) (i j : Fin 2), world cexA₀ ⟨0, m, i, j, ()⟩ = (decide (i = 0), m, decide (j = 0))) ∧
    (∀ (i j : Fin 2), world cexA₀ ⟨1, i, j, ()⟩ = (decide (i = 0), decide (i = 0), decide (j = 0))) :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩

/-- `ν` on `cexA₀` as an explicit sum. Source: none: infrastructure. Kind: L -/
theorem cexA_nu (C : Proc Unit (fun _ => Bool) ℚ) (X : Finset TickleW) :
    nu C cexA₀ X =
      (∑ m : Bool, ∑ i : Fin 2, ∑ j : Fin 2,
        if (decide (i = 0), m, decide (j = 0)) ∈ X then leafLaw C cexA₀ ⟨0, m, i, j, ()⟩
        else 0) +
      ∑ i : Fin 2, ∑ j : Fin 2,
        if (decide (i = 0), decide (i = 0), decide (j = 0)) ∈ X then
          leafLaw C cexA₀ ⟨1, i, j, ()⟩ else 0 := by
  rw [nu_eq_sum, cexA_sum]
  rfl

/-- **The four masses on counterexample A at `δ_refrain`**: `ν(m=1) = ¼`, `ν(k ∧ m=1) = 99/400`,
`ν(m=0) = ¾`, `ν(k ∧ m=0) = 101/400`.
Source: mandate §3.7 (recomputed from the script's tree)
Kind: N+ -/
theorem cexA_nu_values :
    nu procRefrain cexA₀ (evM true) = 1/4 ∧
    nu procRefrain cexA₀ (evK ∩ evM true) = 99/400 ∧
    nu procRefrain cexA₀ (evM false) = 3/4 ∧
    nu procRefrain cexA₀ (evK ∩ evM false) = 101/400 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [cexA_nu]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, cexA_leafLaw_E, cexA_leafLaw_A, Finset.mem_inter,
      mem_evM, mem_evK, procRefrain, FinDistr.pure_w]
    simp; norm_num

/-- Every run of `cexA₀` meets `d` at most once (the `E`-runs once, the `A`-runs never).
Source: [[decision-problems-v2]] §7.3 Lemma 3 ("each run realizes at most one `d`-node")
Kind: L -/
theorem cexA_count_le_one (ℓ : cexA₀.Leaves) : count () cexA₀ ℓ ≤ 1 := by
  unfold cexA₀ cexA kBlock slLeaf at ℓ ⊢
  rcases ℓ with ⟨t, ℓ⟩
  fin_cases t
  · rcases ℓ with ⟨m, i, j, _⟩; exact le_rfl
  · rcases ℓ with ⟨i, j, _⟩; exact zero_le_one

/-- **Coverage fails on counterexample A at `δ_refrain`**: the `A`-leaf `(ℓ=1, m=1, k=1)` has
positive mass `99/400`, its world satisfies `O_d = ⊤`, and it meets no `d`-node.
Source: `sl-synthesis.md` §1.2 ("a one-node, `O_d = ⊤`, coverage-failing tree"); mandate T1(a)
Kind: N− -/
theorem cexA_not_covers : ¬ Covers slObs procRefrain cexA₀ () := by
  intro h
  have hpos : 0 < leafLaw procRefrain cexA₀ ⟨1, 0, 0, ()⟩ := by
    rw [cexA_leafLaw_A]; norm_num
  have := h ⟨1, 0, 0, ()⟩ hpos (Finset.mem_univ _)
  unfold cexA₀ cexA kBlock slLeaf at this
  simp at this

/-- Counterexample A is not Definition-7 recorded at `d` for `δ_refrain` (clause 1 fails by
coverage).
Source: mandate T1(a)
Kind: N− -/
theorem cexA_not_recordsFor : ¬ RecordsFor slObs slActEv procRefrain cexA₀ () :=
  fun h => cexA_not_covers (h.covers slObs slActEv)

/-- The unique `d`-node of counterexample A: the decision node at the root of the `E`-branch.
Source: none: infrastructure
Kind: D -/
def cexANode : cexA₀.DecNode := ⟨0, none⟩

/-- Every decision node of counterexample A is `cexANode`. Source: none: infrastructure. Kind: L -/
theorem cexA_nodes_cases (q : cexA₀.DecNode) : q = cexANode := by
  unfold cexA₀ cexA kBlock slLeaf at q ⊢
  rcases q with ⟨t, q⟩
  fin_cases t
  · rcases q with (_ | ⟨m, i, ⟨j, e⟩⟩)
    · rfl
    · exact e.elim
  · rcases q with ⟨i, ⟨j, e⟩⟩
    exact e.elim

/-- The edges at the `d`-node of counterexample A: an `E`-leaf takes its act's edge, an
`A`-leaf is off the node.
Source: none: infrastructure. Kind: L -/
theorem cexA_edgeOf :
    (∀ (m : Bool) (i j : Fin 2), edgeOf cexA₀ cexANode ⟨0, m, i, j, ()⟩ = some m) ∧
    (∀ (i j : Fin 2), edgeOf cexA₀ cexANode ⟨1, i, j, ()⟩ = none) := by
  constructor
  · intro m i j
    unfold cexANode cexA₀ cexA kBlock slLeaf
    simp [edgeOf_chance, edgeOf_decision_none]
  · intro i j
    unfold cexANode cexA₀ cexA kBlock slLeaf
    simp [edgeOf_chance]

/-- **Cancer is post-query independent of the draw on counterexample A, for every procedure**:
at the `d`-node the `k`-mass below either action edge is `(γ₁ + γ₀)/2 = ½` times the edge
mass — the lesion is drawn *after* `d`, so the constant is the lesion-averaged cancer rate,
not `γ_{ℓ(q)}` (`LesionOnlyAt` fails here, `PostQueryIndep` holds). This is the printed
lemma's second hypothesis under the **subtree-law reading** ("the post-query subtree law below
the `d`-node is a function of the drawn action alone"), machine-checked for the refutation
`lemma3_printed_refuted_coverage`.
Source: [[decision-problems-v2]] §7.3 Lemma 3 (hypothesis); mandate T1(a); audit r1
adversarial N3, fidelity §3.7
Kind: N+ -/
theorem cexA_postQueryIndep (C : Proc Unit (fun _ => Bool) ℚ) : PostQueryIndep C cexA₀ () evK := by
  intro q _ a b
  obtain rfl := cexA_nodes_cases q
  have hin : ∀ a : Bool, edgeMassIn C cexA₀ evK cexANode a = 1/4 * (C ()).w a := by
    intro a
    unfold edgeMassIn
    rw [cexA_sum]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, cexA_edgeOf.1, cexA_edgeOf.2, cexA_leafLaw_E,
      cexA_leafLaw_A, cexA_world.1, cexA_world.2, mem_evK]
    cases a <;> simp <;> ring
  have hm : ∀ a : Bool, edgeMass C cexA₀ cexANode a = 1/2 * (C ()).w a := by
    intro a
    unfold edgeMass
    rw [cexA_sum]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, cexA_edgeOf.1, cexA_edgeOf.2, cexA_leafLaw_E,
      cexA_leafLaw_A]
    cases a <;> simp <;> ring
  rw [hin, hin, hm, hm]; ring

/-- **Lemma 3 as printed is refuted by coverage failure**: on counterexample A at
`C = δ_refrain`, every run meets `d` at most once and the post-query chance depends only on
the drawn action (**subtree-law reading** of the printed hypothesis: the post-query subtree
law below the `d`-node is a function of the drawn action alone — here the lesion is drawn
after `d`, so under a per-node reading "depends on the path only through pre-query chance" the
tree would be out of scope; the subtree-law reading is the one the sl-workflow adopted and the
natural one; its `k`-consequence `PostQueryIndep C cexA₀ () evK` is machine-checked for every
`C` in `cexA_postQueryIndep`), yet
`ν(k ∧ m=1) · ν(m=0) = 99/400 · ¾ ≠ 101/400 · ¼ = ν(k ∧ m=0) · ν(m=1)` — the act coordinate is
not independent of cancer under `ν` (the conditional gap is `99/100 − 101/300 = 49/75`) — and
the tree is not covered, hence not recorded, at `d`. Refuted under the **explicit-hypothesis
reading** (the lemma's two stated clauses as the whole hypothesis, as `dp-core-tree`'s row 43
fixed it); under the **enumerated-shape reading** ("Instantiations: chance `ℓ`; query `d`; act
`m`; chance `k`", i.e. (S4)) the tree is out of scope and the lemma is under-hypothesised
rather than false: this witness shows the shape line is load-bearing. Beside `dp-core-tree`'s
`overwrite_m_not_indep_lesion` (action-veridicality failure) it is the two homes' first
appearance.
Source: [[decision-problems-v2]] §7.3 line 256 ("In any instantiation where each run realizes
at most one `d`-node and post-query chance depends on the path only through pre-query chance
and the drawn action: … under (S1)+(S3), `m ⊥ (ℓ, k)` under `ν_{B,C}` for every `C`"), refuted;
dp-sl-008; `sl-synthesis.md` §1.2 "Register"; mandate T1(a)
Kind: P
Fidelity: exact (the refuted statement is the lemma's second clause, `k`-marginal, at `X = evK`,
cross-multiplied; "(S1) and (S3) hold" is the tree's shape; the post-query hypothesis is
carried as `PostQueryIndep evK` under the subtree-law reading)
Hyps: none -/
theorem lemma3_printed_refuted_coverage :
    (∀ ℓ, count () cexA₀ ℓ ≤ 1) ∧
    PostQueryIndep procRefrain cexA₀ () evK ∧
    nu procRefrain cexA₀ (evK ∩ evM true) * nu procRefrain cexA₀ (evM false) ≠
      nu procRefrain cexA₀ (evK ∩ evM false) * nu procRefrain cexA₀ (evM true) ∧
    ¬ Covers slObs procRefrain cexA₀ () ∧ ¬ RecordsFor slObs slActEv procRefrain cexA₀ () := by
  obtain ⟨h1, h2, h3, h4⟩ := cexA_nu_values
  refine ⟨cexA_count_le_one, cexA_postQueryIndep procRefrain, ?_, cexA_not_covers,
    cexA_not_recordsFor⟩
  rw [h1, h2, h3, h4]; norm_num

/-- The conditional gap on counterexample A: `ν(k ∣ m=1) − ν(k ∣ m=0) = 99/100 − 101/300 = 49/75`.
Source: `sl-synthesis.md` §1.2 ("gap `49/75`"); mandate §3.7
Kind: N+ -/
theorem cexA_gap :
    nu procRefrain cexA₀ (evK ∩ evM true) / nu procRefrain cexA₀ (evM true) -
      nu procRefrain cexA₀ (evK ∩ evM false) / nu procRefrain cexA₀ (evM false) = 49/75 := by
  obtain ⟨h1, h2, h3, h4⟩ := cexA_nu_values
  rw [h1, h2, h3, h4]; norm_num

/-- `μ` on `cexA₀` of a run event at `C(d) = ½` as an explicit sum.
Source: none: infrastructure. Kind: L -/
theorem cexA_mass_half (P : cexA₀.Leaves → Prop) [DecidablePred P] :
    mass (procBool (1/2) (by norm_num) (by norm_num)) cexA₀ (Finset.univ.filter P) =
      (∑ m : Bool, ∑ i : Fin 2, ∑ j : Fin 2, if P ⟨0, m, i, j, ()⟩ then
        leafLaw (procBool (1/2) (by norm_num) (by norm_num)) cexA₀ ⟨0, m, i, j, ()⟩ else 0) +
      ∑ i : Fin 2, ∑ j : Fin 2, if P ⟨1, i, j, ()⟩ then
        leafLaw (procBool (1/2) (by norm_num) (by norm_num)) cexA₀ ⟨1, i, j, ()⟩ else 0 := by
  rw [mass_filter, cexA_sum]

/-- **The printed lemma's first clause holds on counterexample A** (run level, `C(d) = ½`):
the draw at `d` is independent of the lesion on the runs consulting `d`:
`μ({ℓ=1} ∩ drew₁) · μ(occ) = ⅛ · ½ = ¼ · ¼ = μ({ℓ=1} ∩ occ) · μ(drew₁)` — while the world-level
second clause fails on the same tree (`lemma3_printed_refuted_coverage`). This is the
draw/coordinate gap of `dp-core-tree`'s findings F1 on the coverage-failure side (the lesion
is drawn *after* `d` here, so `screening_draw`'s pre-query hypothesis does not apply and the
identity is computed directly).
Source: [[decision-problems-v2]] §7.3 Lemma 3, first clause; `dp-core-tree` findings F1; mandate
T1(a) trap ("`screening_draw` holds on `cexA` too — state that as the contrast")
Kind: N+ -/
theorem cexA_draw_indep_lesion :
    mass (procBool (1/2) (by norm_num) (by norm_num)) cexA₀
        (worldEv cexA₀ evL ∩ drew () true cexA₀) *
      mass (procBool (1/2) (by norm_num) (by norm_num)) cexA₀ (occ () cexA₀) =
    mass (procBool (1/2) (by norm_num) (by norm_num)) cexA₀
        (worldEv cexA₀ evL ∩ occ () cexA₀) *
      mass (procBool (1/2) (by norm_num) (by norm_num)) cexA₀ (drew () true cexA₀) := by
  have e1 : worldEv cexA₀ evL ∩ drew () true cexA₀ = Finset.univ.filter fun ℓ =>
      world cexA₀ ℓ ∈ evL ∧ (⟨(), true⟩ : Σ d : Unit, Bool) ∈ draws cexA₀ ℓ := by
    ext ℓ; simp [worldEv, drew]
  have e2 : worldEv cexA₀ evL ∩ occ () cexA₀ = Finset.univ.filter fun ℓ =>
      world cexA₀ ℓ ∈ evL ∧ 0 < count () cexA₀ ℓ := by
    ext ℓ; simp [worldEv, occ]
  have e3 : drew () true cexA₀ = Finset.univ.filter fun ℓ =>
      (⟨(), true⟩ : Σ d : Unit, Bool) ∈ draws cexA₀ ℓ := by
    ext ℓ; simp [drew]
  rw [e1, e2, e3, occ, cexA_mass_half, cexA_mass_half, cexA_mass_half, cexA_mass_half]
  simp only [Fin.sum_univ_two, Fintype.sum_bool, cexA_leafLaw_E, cexA_leafLaw_A, procBool,
    FinDistr.bool_true, FinDistr.bool_false]
  unfold cexA₀ cexA kBlock slLeaf
  simp [mem_evL, Sigma.mk.injEq, heq_eq_eq]
  norm_num

end cexA

/-! ## The flipped table: (S2) at a recorded strict state -/

section causal

variable (κ₁ : ℚ) (k10 : 0 ≤ κ₁) (k11 : κ₁ ≤ 1) (κ₀ : ℚ) (k00 : 0 ≤ κ₀) (k01 : κ₀ ≤ 1) (α β : ℚ)

/-- A sum over the leaves of `slOneCausal`. Source: none: infrastructure. Kind: L -/
theorem slOneCausal_sum (f : (slOneCausal κ₁ k10 k11 κ₀ k00 k01 α β).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ m : Bool, ∑ j : Fin 2, f ⟨m, j, ()⟩ := by
  unfold slOneCausal slLeaf at f ⊢
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- The leaf masses of `slOneCausal`: `μ(m, k) = C(d)(m) · κ_{m,k}`.
Source: Definition 6 on the flipped table
Kind: L -/
theorem slOneCausal_leafLaw (C : Proc Unit (fun _ => Bool) ℚ) (m : Bool) (j : Fin 2) :
    leafLaw C (slOneCausal κ₁ k10 k11 κ₀ k00 k01 α β) ⟨m, j, ()⟩ =
      (C ()).w m * (if m then (if j = 0 then κ₁ else 1 - κ₁) else (if j = 0 then κ₀ else 1 - κ₀)) := by
  unfold slOneCausal slLeaf
  simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf, FinDistr.coin]
  fin_cases j <;> cases m <;> simp

/-- `ν` on `slOneCausal` as an explicit sum. Source: none: infrastructure. Kind: L -/
theorem slOneCausal_nu (C : Proc Unit (fun _ => Bool) ℚ) (X : Finset TickleW) :
    nu C (slOneCausal κ₁ k10 k11 κ₀ k00 k01 α β) X =
      ∑ m : Bool, ∑ j : Fin 2, if (false, m, decide (j = 0)) ∈ X then
        leafLaw C (slOneCausal κ₁ k10 k11 κ₀ k00 k01 α β) ⟨m, j, ()⟩ else 0 := by
  rw [nu_eq_sum, slOneCausal_sum]
  rfl

/-- The four masses on the flipped table: `ν(m) = C(d)(m)`, `ν(k ∧ m) = C(d)(m) · κ_m`.
Source: `sl-defensible-claims.md` S3 (the flipped CGTA table)
Kind: L -/
theorem slOneCausal_nu_values (C : Proc Unit (fun _ => Bool) ℚ) :
    (∀ m, nu C (slOneCausal κ₁ k10 k11 κ₀ k00 k01 α β) (evM m) = (C ()).w m) ∧
    (∀ m, nu C (slOneCausal κ₁ k10 k11 κ₀ k00 k01 α β) (evK ∩ evM m) =
      (C ()).w m * (if m then κ₁ else κ₀)) := by
  constructor <;> intro m <;>
  · rw [slOneCausal_nu]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, slOneCausal_leafLaw, Finset.mem_inter, mem_evM,
      mem_evK]
    cases m <;> simp <;> ring

/-- The flipped table records at `d` for every procedure (one `d`-node, `O_d = ⊤`, the leaf's
`m` is the draw).
Source: mandate T1(d)
Kind: L -/
theorem slOneCausal_recordsFor (C : Proc Unit (fun _ => Bool) ℚ) :
    RecordsFor slObs slActEv C (slOneCausal κ₁ k10 k11 κ₀ k00 k01 α β) () := by
  intro ℓ _ _
  unfold slOneCausal slLeaf at ℓ ⊢
  rcases ℓ with ⟨m, j, _⟩
  refine ⟨rfl, ?_⟩
  rintro (_ | ⟨m', ⟨j', e⟩⟩) hq a ha
  · simp only [edgeOf_decision_none, Option.some.injEq] at ha
    subst ha
    refine ⟨?_, ?_, ?_⟩
    · intro ℓ' _; simp [slObs]
    · simp [slActEv, evM]
    · intro a' ha'; simp [slActEv, evM] at ha'; exact ha'.symm
  · exact e.elim

/-- **The flipped table: (S2) holds at a recorded, strictly calibrated state** whenever
`κ₀ < κ₁` and the label is interior: the strictly calibrated state at `O_d = ⊤` for `C(d) = q`
satisfies (S2) — `P(k ∣ m=1) = κ₁ > κ₀ = P(k ∣ m=0)` — and the tree records for every procedure.
So (S1)'s lesion-only clause, not recording, is what makes Lemma 3's `k`-conclusion true; at
the source's numbers `κ = (11/20, 97/200)` the conditionals are `11/20 > 97/200`.
Source: `sl-defensible-claims.md` S3 ("a flipped CGTA table (chewing causally protects) makes
(S2) hold at a *recorded* point (`11/20 > 97/200`)"); dp-sl-010's last sentence; mandate T1(d)
Kind: N−
Fidelity: exact (the source's parameters `(11/20, 97/200)` are the conditionals themselves; a
generating table was not located in the sources, so the rates are taken as the conditionals) -/
theorem slOneCausal_S2_at_strict (hlt : κ₀ < κ₁) (q : ℚ) (h0 : 0 < q) (h1 : q < 1) :
    RecordsFor slObs slActEv (procBool q h0.le h1.le) (slOneCausal κ₁ k10 k11 κ₀ k00 k01 α β) () ∧
    StrictOCAt (fun _ => calibratedState (procBool q h0.le h1.le)
        (slOneCausal κ₁ k10 k11 κ₀ k00 k01 α β) Finset.univ (nu_univ_pos _ _))
      slObs (procBool q h0.le h1.le) (slOneCausal κ₁ k10 k11 κ₀ k00 k01 α β) () ∧
    S2 (calibratedState (procBool q h0.le h1.le) (slOneCausal κ₁ k10 k11 κ₀ k00 k01 α β)
      Finset.univ (nu_univ_pos _ _)) := by
  obtain ⟨hm, hkm⟩ := slOneCausal_nu_values κ₁ k10 k11 κ₀ k00 k01 α β (procBool q h0.le h1.le)
  refine ⟨slOneCausal_recordsFor κ₁ k10 k11 κ₀ k00 k01 α β _,
    strictOCAt_calibratedState slObs _ _ _ () _ rfl, ?_⟩
  unfold S2
  simp only [calibratedState_pr, Finset.inter_univ, nu_univ, div_one, hm, hkm]
  simp only [procBool, FinDistr.bool_true, FinDistr.bool_false]
  refine ⟨h0, by linarith, ?_⟩
  simp only [Bool.false_eq_true, if_false, if_true]
  have hq : 0 < q * (1 - q) := mul_pos h0 (sub_pos.mpr h1)
  nlinarith [mul_pos hq (sub_pos.mpr hlt)]

/-- The source's numbers on the flipped table at `C(d) = ½`: `P(k ∣ m=1) = 11/20 > 97/200 =
P(k ∣ m=0)` at the strict state.
Source: `sl-defensible-claims.md` S3
Kind: N+ -/
theorem slOneCausal_instance :
    S2 (calibratedState (procBool (1/2) (by norm_num) (by norm_num))
      (slOneCausal (11/20) (by norm_num) (by norm_num) (97/200) (by norm_num) (by norm_num) 1 1)
      Finset.univ (nu_univ_pos _ _)) :=
  (slOneCausal_S2_at_strict (11/20) (by norm_num) (by norm_num) (97/200) (by norm_num)
    (by norm_num) 1 1 (by norm_num) (1/2) (by norm_num) (by norm_num)).2.2

end causal

end Cleanroom.Decision.DpSmokingLesion

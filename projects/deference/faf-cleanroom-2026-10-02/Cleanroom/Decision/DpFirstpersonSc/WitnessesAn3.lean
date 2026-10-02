import Cleanroom.Decision.DpFirstpersonSc.WitnessesLicense

/-!
# Witnesses for T3(c): AN-3′'s three trees in one shape

`anTree wL rL wR rR`: a fair coin; the left branch (index `0`) queries `d` and ends in the world
`wL act` with payoff `rL act`; the right branch (index `1`) is an unconsulted leaf `(wR, rR)` placed
below the dummy point `e` (the `coverFail` trick: both edges to one leaf, so the two chance children
share one shape). `occ(d)` is the left branch, `μ(occ(d)) = ½`.

* **(i) the instance-blind tree** (`blindTree`, `C = δ_a`): every leaf has the one world `false`;
  left `a ↦ r = 1`, `b ↦ r = 0`, right `r = 0`. The per-run state and the strict-OC state at `⊤`
  have the same `P` (`δ_false`, `blind_P_agree`) and different `V` (`1` vs `½`:
  `blind_V_occ`, `blind_V_strict`) — Remark 3.5's non-supervenient payoffs, not anthropics; the
  `V`-criterion of AN-3′ fails at `w = false` (`blind_V_criterion_fails`: `½ · 1 ≠ ½ · ½`).
* **(ii) right-leaf payoff `1`** (`blindTree'`): non-expressible (`blind'_not_occExpressible`:
  every world is `false`, so no world event separates the branches) yet per-run SSC = strict OC
  at `⊤` in both clauses (`blind'_agree`: `State.Agree` of the per-run state and the strict state
  at `⊤` — `P` equal, `V` equal on every positive event; `blind'_V_agree` is the `V(⊤)` cell
  alone) — AN-3's dead converse ("non-expressible ⟹ not a `ν`-conditional") refuted, as the
  source says (Dead 1). Repair round 1 (audit r1 fidelity B1): the round-0 lemma stated the `V(⊤)`
  cell only; the `P`-clause, which Dead 1 is about, is now stated.
* **F5's witness** (`anThree_priorState_not_clause1`, with `Lift.lean`'s
  `lambdaCI_compatible_model_exists`): the trivial-evidence clause of `liftModelB_iff` is
  load-bearing — on `anThree` a `λ`-compatible model from the prior state to `μ(· | occ(d))`
  exists while the prior state fails per-run clause 1.
* **(iii)** (`anThree`, `C = (½, ½)`): left `a ↦ (c = 0, r = 1)`, `b ↦ (c = 1, r = 0)`, right
  `(c = 0, r = 0)`: `ν = (¾, ¼)`, the per-run `P = (½, ½)`, ratios `⅔, 2` — not a
  `ν`-conditional for any event (`three_no_nuCond`, by `occState_P_eq_nuCondDistr_iff`'s right
  side failing: `¼ · ¼ ≠ ¼ · ¾`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFaithfulUdt
open Finset

/-- **AN-3′'s tree shape**: fair coin; left (index `0`) a `d`-node with leaf world `wL act` and
payoff `rL act`; right (index `1`) the unconsulted leaf `(wR, rR)` below the dummy point `e`.
Source: `anticipation.md` AN-3′ (i)–(iii) ("root coin; left a `d`-node → …; right leaf …")
Kind: D
Fidelity: variant: the right leaf sits below a dummy point `e` (one child shape); nothing about
`d` changes -/
def anTree (wL : Act2 → Bool) (rL : Act2 → ℚ) (wR : Bool) (rR : ℚ) :
    Tree Bool CfPt (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i => .decision (if i = 0 then CfPt.d else CfPt.e) fun act =>
    .leaf (if i = 0 then wL act else wR) (if i = 0 then rL act else rR)

section shape

variable (wL : Act2 → Bool) (rL : Act2 → ℚ) (wR : Bool) (rR : ℚ)

/-- Leaf sums. Source: none: infrastructure. Kind: L -/
theorem anTree_sum {M : Type} [AddCommMonoid M] (f : (anTree wL rL wR rR).Leaves → M) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ∑ act : Act2, f ⟨i, act, ()⟩ := by
  unfold anTree at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun act _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- The leaf law. Source: none: infrastructure. Kind: L -/
theorem anTree_leafLaw (C : Proc CfPt (fun _ => Act2) ℚ) (i : Fin 2) (act : Act2) :
    leafLaw C (anTree wL rL wR rR) ⟨i, act, ()⟩ =
      FinDistr.fair.w i * ((C (if i = 0 then .d else .e)).w act * 1) := by
  unfold anTree
  simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf]

/-- The world. Source: none: infrastructure. Kind: L -/
theorem anTree_world (i : Fin 2) (act : Act2) :
    world (anTree wL rL wR rR) ⟨i, act, ()⟩ = if i = 0 then wL act else wR := by
  unfold anTree; simp [world_chance, world_decision, world_leaf]

/-- The payoff. Source: none: infrastructure. Kind: L -/
theorem anTree_payoff (i : Fin 2) (act : Act2) :
    payoff (anTree wL rL wR rR) ⟨i, act, ()⟩ = if i = 0 then rL act else rR := by
  unfold anTree; simp [payoff_chance, payoff_decision, payoff_leaf]

/-- `#_d`: one on the left branch, zero on the right. Source: none: infrastructure. Kind: L -/
theorem anTree_count_d (i : Fin 2) (act : Act2) :
    count .d (anTree wL rL wR rR) ⟨i, act, ()⟩ = if i = 0 then 1 else 0 := by
  unfold anTree
  simp only [count_chance, count_decision, count_leaf]
  fin_cases i <;> simp

end shape

/-- `C = (½, ½)` at both points. Source: `anticipation.md` AN-3′ (iii). Kind: D -/
def cfProcHalf : Proc CfPt (fun _ => Act2) ℚ := fun _ => FinDistr.act2 (1/2) (by norm_num) (by norm_num)

/-! ## (i) The instance-blind tree -/

/-- **The instance-blind tree**: one world `false`; left `a ↦ 1`, `b ↦ 0`; right `0`.
Source: `anticipation.md` AN-3′ (i) ("the notes' instance-blind tree (root coin; left a `d`-node →
`(w₀,1)/(w₀,0)`; right leaf `(w₀,0)`; `C` = answer 1)")
Kind: D -/
def blindTree : Tree Bool CfPt (fun _ => Act2) ℚ :=
  anTree (fun _ => false) (fun a => if a = .a then 1 else 0) false 0

/-- `ν = δ_false`. Source: none: infrastructure. Kind: L -/
theorem blind_nu (X : Finset Bool) : nu cfProcA blindTree X = if false ∈ X then 1 else 0 := by
  rw [nu_eq_sum, blindTree, anTree_sum]
  simp only [anTree_world, anTree_leafLaw, Fin.sum_univ_two, Act2.sum_univ]
  simp [cfProcA, FinDistr.fair, FinDistr.coin] <;> split_ifs <;> norm_num

/-- `paySum X = ½ · 1[false ∈ X]`. Source: none: infrastructure. Kind: L -/
theorem blind_paySum (X : Finset Bool) :
    paySum cfProcA blindTree X = if false ∈ X then 1 / 2 else 0 := by
  rw [paySum_eq_sum_ite, blindTree, anTree_sum]
  simp only [anTree_world, anTree_leafLaw, anTree_payoff, Fin.sum_univ_two, Act2.sum_univ]
  simp [cfProcA, FinDistr.fair, FinDistr.coin] <;> split_ifs <;> norm_num

/-- `μ(occEv X) = ½ · 1[false ∈ X]`. Source: none: infrastructure. Kind: L -/
theorem blind_mass_occEv (X : Finset Bool) :
    mass cfProcA blindTree (occEv blindTree .d X) = if false ∈ X then 1 / 2 else 0 := by
  rw [mass_eq_sum_ite', blindTree, anTree_sum]
  simp only [occEv, Finset.mem_inter, worldEv, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_occ, anTree_world, anTree_leafLaw, anTree_count_d, Fin.sum_univ_two, Act2.sum_univ]
  simp [cfProcA, FinDistr.fair, FinDistr.coin] <;> split_ifs <;> norm_num

/-- `occPay X = ½ · 1[false ∈ X]`. Source: none: infrastructure. Kind: L -/
theorem blind_occPay (X : Finset Bool) :
    occPay cfProcA blindTree .d X = if false ∈ X then 1 / 2 else 0 := by
  unfold occPay
  rw [sum_eq_sum_ite_mem (occEv blindTree .d X), blindTree, anTree_sum]
  simp only [occEv, Finset.mem_inter, worldEv, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_occ, anTree_world, anTree_leafLaw, anTree_payoff, anTree_count_d, Fin.sum_univ_two,
    Act2.sum_univ]
  simp [cfProcA, FinDistr.fair, FinDistr.coin] <;> split_ifs <;> norm_num

/-- `μ(occ(d)) = ½ > 0`. Source: none: infrastructure. Kind: L -/
theorem blind_occ_pos : 0 < Tree.mass cfProcA blindTree (occ .d blindTree) := by
  have := blind_mass_occEv Finset.univ
  rw [occEv_univ] at this
  rw [this]; simp

/-- **(i), `P` agrees**: the per-run state and the strict-OC state at `⊤` are both `δ_false`.
Source: `anticipation.md` AN-3′ (i) ("SSC `(δ_{w₀}, 1)`, strict OC at `⊤` `(δ_{w₀}, ½)` — `P`
agrees")
Kind: N+ -/
theorem blind_P_agree :
    (occState cfProcA blindTree .d blind_occ_pos).P =
      (calibratedState cfProcA blindTree Finset.univ (nu_univ_pos _ _)).P := by
  have hocc := blind_mass_occEv Finset.univ
  rw [occEv_univ] at hocc
  apply FinDistr.ext'
  intro ω
  have h1 : (calibratedState cfProcA blindTree Finset.univ (nu_univ_pos _ _)).P.w ω =
      nu cfProcA blindTree ({ω} ∩ Finset.univ) / nu cfProcA blindTree Finset.univ := by
    have := calibratedState_pr cfProcA blindTree Finset.univ (nu_univ_pos _ _) {ω}
    simpa only [State.pr, probOf_singleton] using this
  have h2 : (occState cfProcA blindTree .d blind_occ_pos).P.w ω =
      Tree.mass cfProcA blindTree (occEv blindTree .d {ω}) /
        Tree.mass cfProcA blindTree (occ .d blindTree) := by
    have := occState_pr cfProcA blindTree .d blind_occ_pos {ω}
    simpa only [State.pr, probOf_singleton] using this
  rw [h1, h2, blind_mass_occEv, hocc, blind_nu, blind_nu, Finset.inter_univ]
  cases ω <;> simp

/-- **(i), the per-run value is `1`**: `V_{SSC}(⊤) = 1`.
Source: `anticipation.md` AN-3′ (i) ("SSC `(δ_{w₀}, 1)`")
Kind: N+ -/
theorem blind_V_occ : (occState cfProcA blindTree .d blind_occ_pos).V Finset.univ = 1 := by
  rw [occState_V, blind_occPay, blind_mass_occEv]; simp

/-- **(i), the strict-OC value is `½`**: `V_{OC}(⊤) = ½` — `V` differs from the per-run state's.
Source: `anticipation.md` AN-3′ (i) ("strict OC at `⊤` `(δ_{w₀}, ½)` — … `V` differs by Remark
3.5's non-supervenient payoffs")
Kind: N+ -/
theorem blind_V_strict :
    (calibratedState cfProcA blindTree Finset.univ (nu_univ_pos _ _)).V Finset.univ = 1 / 2 := by
  rw [calibratedState_V, Finset.inter_univ, blind_paySum, blind_nu]; simp

/-- **(i), AN-3′'s `V`-criterion fails at `w = false`**: the `μ`-mean payoff over the occ-leaves of
`w` (`1`) differs from the mean over all leaves of `w` (`½`), in the multiplicative form
`occPay{w} · ν{w} ≠ paySum{w} · μ(occEv{w})` (`½ · 1 ≠ ½ · ½`).
Source: `anticipation.md` AN-3′ (`V`-clause: "for every world `w` realized on occ-leaves, the
`μ`-mean payoff over the occ-leaves of `w` equals the `μ`-mean over all leaves of `w`")
Kind: N+ -/
theorem blind_V_criterion_fails :
    occPay cfProcA blindTree .d {false} * nu cfProcA blindTree {false} ≠
      paySum cfProcA blindTree {false} * Tree.mass cfProcA blindTree (occEv blindTree .d {false}) := by
  rw [blind_occPay, blind_nu, blind_paySum, blind_mass_occEv]; simp

/-! ## (ii) Right-leaf payoff `1` -/

/-- **AN-3′ (ii)**: the instance-blind tree with the right leaf's payoff `1`.
Source: `anticipation.md` AN-3′ (ii) ("right leaf payoff `1`: non-expressible, SSC = OC at `⊤` in
both clauses")
Kind: D -/
def blindTree' : Tree Bool CfPt (fun _ => Act2) ℚ :=
  anTree (fun _ => false) (fun a => if a = .a then 1 else 0) false 1

/-- `ν = δ_false`. Source: none: infrastructure. Kind: L -/
theorem blind'_nu (X : Finset Bool) : nu cfProcA blindTree' X = if false ∈ X then 1 else 0 := by
  rw [nu_eq_sum, blindTree', anTree_sum]
  simp only [anTree_world, anTree_leafLaw, Fin.sum_univ_two, Act2.sum_univ]
  simp [cfProcA, FinDistr.fair, FinDistr.coin] <;> split_ifs <;> norm_num

/-- `paySum X = 1[false ∈ X]`. Source: none: infrastructure. Kind: L -/
theorem blind'_paySum (X : Finset Bool) :
    paySum cfProcA blindTree' X = if false ∈ X then 1 else 0 := by
  rw [paySum_eq_sum_ite, blindTree', anTree_sum]
  simp only [anTree_world, anTree_leafLaw, anTree_payoff, Fin.sum_univ_two, Act2.sum_univ]
  simp [cfProcA, FinDistr.fair, FinDistr.coin] <;> split_ifs <;> norm_num

/-- `μ(occEv X) = ½ · 1[false ∈ X]`. Source: none: infrastructure. Kind: L -/
theorem blind'_mass_occEv (X : Finset Bool) :
    mass cfProcA blindTree' (occEv blindTree' .d X) = if false ∈ X then 1 / 2 else 0 := by
  rw [mass_eq_sum_ite', blindTree', anTree_sum]
  simp only [occEv, Finset.mem_inter, worldEv, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_occ, anTree_world, anTree_leafLaw, anTree_count_d, Fin.sum_univ_two, Act2.sum_univ]
  simp [cfProcA, FinDistr.fair, FinDistr.coin] <;> split_ifs <;> norm_num

/-- `occPay X = ½ · 1[false ∈ X]`. Source: none: infrastructure. Kind: L -/
theorem blind'_occPay (X : Finset Bool) :
    occPay cfProcA blindTree' .d X = if false ∈ X then 1 / 2 else 0 := by
  unfold occPay
  rw [sum_eq_sum_ite_mem (occEv blindTree' .d X), blindTree', anTree_sum]
  simp only [occEv, Finset.mem_inter, worldEv, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_occ, anTree_world, anTree_leafLaw, anTree_payoff, anTree_count_d, Fin.sum_univ_two,
    Act2.sum_univ]
  simp [cfProcA, FinDistr.fair, FinDistr.coin] <;> split_ifs <;> norm_num

/-- `μ(occ(d)) = ½ > 0`. Source: none: infrastructure. Kind: L -/
theorem blind'_occ_pos : 0 < Tree.mass cfProcA blindTree' (occ .d blindTree') := by
  have := blind'_mass_occEv Finset.univ
  rw [occEv_univ] at this
  rw [this]; simp

/-- **(ii), the `V(⊤)` cell**: `V(⊤) = 1` on both sides. One value of one clause; the agreement
of both clauses (Dead 1's content) is `blind'_agree` below.
Source: `anticipation.md` AN-3′ (ii) ("SSC = OC at `⊤` in both clauses" — the `V(⊤)` value)
Kind: L -/
theorem blind'_V_agree :
    (occState cfProcA blindTree' .d blind'_occ_pos).V Finset.univ =
      (calibratedState cfProcA blindTree' Finset.univ (nu_univ_pos _ _)).V Finset.univ := by
  rw [occState_V, calibratedState_V, Finset.inter_univ, blind'_occPay, blind'_mass_occEv,
    blind'_paySum, blind'_nu]
  simp

/-- **(ii), both clauses agree**: the per-run state at `d` and the strict-OC state at `⊤` agree
as states (`State.Agree`) — `P` is `δ_false` on both sides and `V` is `1` on both sides on every
positive event. This is the clause Dead 1 is about: `blindTree'` is not occurrence-expressible
(`blind'_not_occExpressible`), yet `λ_*μ(· | occ(d))` *is* `ν(· | ⊤)`, in both clauses.
Source: `anticipation.md` AN-3′ (ii) ("SSC = OC at `⊤` in both clauses"); Dead 1 ("AN-3's
converse")
Kind: N+
Fidelity: exact -/
theorem blind'_agree :
    State.Agree (occState cfProcA blindTree' .d blind'_occ_pos)
      (calibratedState cfProcA blindTree' Finset.univ (nu_univ_pos _ _)) := by
  have hocc := blind'_mass_occEv Finset.univ
  rw [occEv_univ] at hocc
  refine ⟨?_, fun X hX => ?_⟩
  · apply FinDistr.ext'
    intro ω
    have h1 : (calibratedState cfProcA blindTree' Finset.univ (nu_univ_pos _ _)).P.w ω =
        nu cfProcA blindTree' ({ω} ∩ Finset.univ) / nu cfProcA blindTree' Finset.univ := by
      have := calibratedState_pr cfProcA blindTree' Finset.univ (nu_univ_pos _ _) {ω}
      simpa only [State.pr, probOf_singleton] using this
    have h2 : (occState cfProcA blindTree' .d blind'_occ_pos).P.w ω =
        Tree.mass cfProcA blindTree' (occEv blindTree' .d {ω}) /
          Tree.mass cfProcA blindTree' (occ .d blindTree') := by
      have := occState_pr cfProcA blindTree' .d blind'_occ_pos {ω}
      simpa only [State.pr, probOf_singleton] using this
    rw [h1, h2, blind'_mass_occEv, hocc, blind'_nu, blind'_nu, Finset.inter_univ]
    cases ω <;> simp
  · have hX' : false ∈ X := by
      by_contra hc
      have := occState_pr cfProcA blindTree' .d blind'_occ_pos X
      simp only [State.pr] at this hX
      rw [this, blind'_mass_occEv, hocc] at hX
      simp [hc] at hX
    rw [occState_V, calibratedState_V, Finset.inter_univ, blind'_occPay, blind'_mass_occEv,
      blind'_paySum, blind'_nu]
    simp [hX']

/-- `μ(occ \ λ⁻¹X)` and `μ(λ⁻¹X \ occ)` on `blindTree'`. Source: none: infrastructure. Kind: L -/
theorem blind'_mass_sdiff (X : Finset Bool) :
    Tree.mass cfProcA blindTree' (occ .d blindTree' \ worldEv blindTree' X) =
        (if false ∈ X then 0 else 1 / 2) ∧
      Tree.mass cfProcA blindTree' (worldEv blindTree' X \ occ .d blindTree') =
        (if false ∈ X then 1 / 2 else 0) := by
  constructor <;>
  · rw [mass_eq_sum_ite', blindTree', anTree_sum]
    simp only [Finset.mem_sdiff, worldEv, Finset.mem_filter, Finset.mem_univ, true_and, mem_occ,
      anTree_world, anTree_leafLaw, anTree_count_d, Fin.sum_univ_two, Act2.sum_univ]
    simp [cfProcA, FinDistr.fair, FinDistr.coin] <;> split_ifs <;> norm_num

/-- **(ii) is not occurrence-expressible**: every world is `false`, so no world event is a.s.
`occ(d)` — yet SSC = OC at `⊤` in both clauses (`blind'_agree`): AN-3's dead converse
("non-expressible ⟹ not a `ν`-conditional") refuted, as the source says.
Source: `anticipation.md` AN-3′ (ii); Dead 1 ("AN-3's converse")
Kind: N+ -/
theorem blind'_not_occExpressible : ¬ OccExpressible cfProcA blindTree' .d := by
  rintro ⟨X, h1, h2⟩
  obtain ⟨e1, e2⟩ := blind'_mass_sdiff X
  rw [e1] at h1; rw [e2] at h2
  by_cases hX : false ∈ X
  · simp [hX] at h2
  · simp [hX] at h1

/-! ## (iii) `ν = (¾, ¼)`, per-run `P = (½, ½)` -/

/-- **AN-3′ (iii)**: left `a ↦ (c = 0, r = 1)`, `b ↦ (c = 1, r = 0)`; right `(c = 0, r = 0)`;
worlds `c` as `Bool` (`false` = `c = 0`).
Source: `anticipation.md` AN-3′ (iii)
Kind: D -/
def anThree : Tree Bool CfPt (fun _ => Act2) ℚ :=
  anTree (fun a => if a = .a then false else true) (fun a => if a = .a then 1 else 0) false 0

/-- `ν = (¾, ¼)`. Source: `anticipation.md` AN-3′ (iii) (`ν = (¾, ¼)`). Kind: L -/
theorem three_nu (X : Finset Bool) :
    nu cfProcHalf anThree X = (if false ∈ X then 3 / 4 else 0) + (if true ∈ X then 1 / 4 else 0) := by
  rw [nu_eq_sum, anThree, anTree_sum]
  simp only [anTree_world, anTree_leafLaw, Fin.sum_univ_two, Act2.sum_univ]
  simp [cfProcHalf, FinDistr.fair, FinDistr.coin] <;> split_ifs <;> norm_num

/-- `μ(occEv X) = ¼ · 1[false ∈ X] + ¼ · 1[true ∈ X]`. Source: none: infrastructure. Kind: L -/
theorem three_mass_occEv (X : Finset Bool) :
    Tree.mass cfProcHalf anThree (occEv anThree .d X) =
      (if false ∈ X then 1 / 4 else 0) + (if true ∈ X then 1 / 4 else 0) := by
  rw [mass_eq_sum_ite', anThree, anTree_sum]
  simp only [occEv, Finset.mem_inter, worldEv, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_occ, anTree_world, anTree_leafLaw, anTree_count_d, Fin.sum_univ_two, Act2.sum_univ]
  simp [cfProcHalf, FinDistr.fair, FinDistr.coin] <;> split_ifs <;> norm_num

/-- `μ(occ(d)) = ½ > 0`. Source: none: infrastructure. Kind: L -/
theorem three_occ_pos : 0 < Tree.mass cfProcHalf anThree (occ .d anThree) := by
  have := three_mass_occEv Finset.univ
  rw [occEv_univ] at this
  rw [this]; simp

/-- **(iii), the per-run `P` is `(½, ½)`**.
Source: `anticipation.md` AN-3′ (iii) ("SSC `P = (½, ½)`")
Kind: N+ -/
theorem three_occState_P :
    (occState cfProcHalf anThree .d three_occ_pos).P.w false = 1 / 2 ∧
      (occState cfProcHalf anThree .d three_occ_pos).P.w true = 1 / 2 := by
  have hocc := three_mass_occEv Finset.univ
  rw [occEv_univ] at hocc
  have hw : ∀ ω, (occState cfProcHalf anThree .d three_occ_pos).P.w ω =
      Tree.mass cfProcHalf anThree (occEv anThree .d {ω}) /
        Tree.mass cfProcHalf anThree (occ .d anThree) := fun _ => rfl
  rw [hw, hw, hocc, three_mass_occEv, three_mass_occEv]
  simp; norm_num

/-- **(iii), not a `ν`-conditional**: the per-run `P` is `ν(· | X)` for no event `X` — AN-3′'s
`P`-criterion fails (`μ(occEv{0}) ν{1} = ¼ · ¼ ≠ ¼ · ¾ = μ(occEv{1}) ν{0}`; the ratios `P/ν` are
`⅔` and `2`).
Source: `anticipation.md` AN-3′ (iii) ("ratios `⅔, 2` — no `ν`-conditional, non-expressible")
Kind: N+ -/
theorem three_no_nuCond :
    ¬ ∃ (X : Finset Bool) (hX : 0 < nu cfProcHalf anThree X),
      (occState cfProcHalf anThree .d three_occ_pos).P = nuCondDistr cfProcHalf anThree X hX := by
  rw [occState_P_eq_nuCondDistr_iff]
  intro h
  have := h false true (by rw [three_mass_occEv]; simp) (by rw [three_mass_occEv]; simp)
  rw [three_mass_occEv, three_mass_occEv, three_nu, three_nu] at this
  simp at this
  norm_num at this

/-! ## F5's Lean witness: the trivial-evidence clause of `liftModelB_iff` is load-bearing -/

set_option maxHeartbeats 400000 in
/-- **On `anThree` under `(½, ½)` the prior state fails per-run clause 1 at `d`**
(`ν{false} = ¾ ≠ ½ = P_{occ}{false}`). With `lambdaCI_compatible_model_exists` (every tree: the
model `(Leaves, μ, λ, id, occ(d))` is `λ`-compatible from the prior state to `μ(· | occ(d))`, with
evidence of mass `μ(occ(d)) = ½ < 1` here) this is F5's witness: `λ`-compatibility alone does not
give clause 1, so `liftModelB_iff`'s `⟹` needs its clause `mass m.μ m.ev = 1`. The conjunction is
not stated at `anThree`'s concrete types (`condOn (runPMF cfProcHalf anThree) …` hits the
package's `whnf` limit, report §Elaboration notes); the `example` below checks the application.
Source: `anticipation.md` AN-1 reading (b); findings F5; audit r1 adversarial N9
Kind: N+
Fidelity: exact -/
theorem anThree_priorState_not_clause1 :
    ¬ PerRunClause1At (fun _ => priorState cfProcHalf anThree) cfProcHalf anThree .d := by
  rw [← P_eq_occState_iff_perRunClause1At cfProcHalf anThree .d _ three_occ_pos]
  intro hP
  have := congrArg (fun P : FinDistr ℚ Bool => P.w false) hP
  rw [three_occState_P.1] at this
  have hp : (priorState cfProcHalf anThree).P.w false = nu cfProcHalf anThree {false} := by
    have := priorState_pr cfProcHalf anThree {false}
    simp only [State.pr, probOf_singleton] at this
    exact this
  rw [hp, three_nu] at this
  norm_num [Finset.mem_singleton] at this

set_option maxHeartbeats 400000 in
/-- The `λ`-compatible model from the prior state to `μ(· | occ(d))`, applied at `anThree` (its
type is inferred from the term; see `anThree_priorState_not_clause1`). -/
example := lambdaCI_compatible_model_exists cfProcHalf anThree .d three_occ_pos

end Cleanroom.Decision.DpFirstpersonSc

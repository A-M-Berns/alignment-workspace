import Cleanroom.Decision.DpEdtUdtFair.Theorem3
import Cleanroom.Decision.DpLocalOpt.Assignments
import Cleanroom.Decision.DpEdtUdtFair.FairWitnesses

/-!
# The fair-tree assignment lemma (T5): on strongly fair trees the assignment optimum is attained
by a deterministic procedure

* `exists_pointwise_best` — **the leaves-up argmax exists**: on a strongly fair tree some
  deterministic `σ` is a pointwise best response in `Q_{σ}` at every queried point. Built by strong
  induction on the set `R` of points still free to be chosen: at the `R`-node with the smallest
  subtree no `R`-point is queried below it, so the values `V_{c₀ a}(σ)` of its children are
  already fixed, and `σ(d)` is set to their argmax (`Classical.choice` through
  `Finset.exists_max_image`; no `LinearOrder` on `acts d`).
* `valueAssign_le_of_pointwise_best` — **assignments cannot beat a pointwise best `σ`**:
  structural induction on the tree; at a decision node the assignment's root action `π(q)` is
  dominated by `σ(d)` because every child value is `σ`'s.
* `stronglyFair_assignment` — **T5**: `StronglyFair B → ∃ σ, ∀ π, V_B(π) ≤ V_B(ofFun σ)`;
  `stronglyFair_assignment_max` adds optimality among procedures, so `max_π V_B(π) = max_C V_B(C)`
  is attained deterministically (Proposition 5(d) / A25 on the fair class).
* Witness: `dupPay 1 0` (two-member fiber, `ra ≠ rb`): every assignment is at most `δ_a`'s value
  `1`, and the assignment playing `a` at one copy and `b` at the other has value `½`
  (`dupPay_assignment_witness`).

Theorem 3 as routed in `Theorem3.lean` does not use this lemma (GR-10 says the same).
-/

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace Cleanroom.Decision.DpEdtUdtFair

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt
open Cleanroom.Decision.DpCalibration

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-! ### The leaves-up argmax -/

section argmax

omit [Fintype Ω] [DecidableEq Ω] in
/-- **The leaves-up fiber-constant argmax exists** on a strongly fair tree: some deterministic
`σ` has, at every queried `d`, `Q_{σ}(d, a) ≤ Q_{σ}(d, σ d)` for every `a`. Proof: strong
induction on the finite set `R` of points still free; at the `R`-node `q₀` with the smallest
subtree no `R`-point is queried below `q₀` (`exists_node_lt_of_mem_queried_child'`), so
`V_{c₀ a}(ofFun σ)` is independent of how `R` is later filled, and `σ(d_{q₀})` is set to an argmax
of these values; `Q` is fiber-constant (`stronglyFair_value_eq_Q`), so the choice at `q₀` serves
every `d_{q₀}`-node. The argmax is chosen by `Finset.exists_max_image` (`Classical.choice`); no
`LinearOrder` on `acts d` is assumed.
Source: `fair-repair.md` after FR-11 ("Fair-tree assignment lemma": "leaves-up, choosing at each
point a fiber-constant argmax"); `calibration.md` CA-3′ (the leaves-up order); mandate T5
Kind: P
Fidelity: exact
Hyps: (a) `StronglyFair B` -/
theorem exists_pointwise_best [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (hB : StronglyFair B) :
    ∃ σ : (d : ι) → acts d, ∀ d ∈ queried B, ∀ a,
      Q (Proc.ofFun σ) B d a ≤ Q (Proc.ofFun σ) B d (σ d) := by
  classical
  have key : ∀ R : Finset ι, ∀ σ₀ : (d : ι) → acts d, ∃ σ : (d : ι) → acts d,
      (∀ e, e ∉ R → σ e = σ₀ e) ∧
      ∀ d ∈ queried B, d ∈ R → ∀ a, Q (Proc.ofFun σ) B d a ≤ Q (Proc.ofFun σ) B d (σ d) := by
    intro R
    induction R using Finset.strongInduction with
    | H R ih =>
      intro σ₀
      by_cases hN : (Finset.univ.filter fun q : B.DecNode => pt B q ∈ R).Nonempty
      · obtain ⟨q₀, hq₀mem, hq₀min⟩ := Finset.exists_min_image
          (Finset.univ.filter fun q : B.DecNode => pt B q ∈ R) (fun q => size (subtreeAt B q)) hN
        obtain ⟨d, hq₀⟩ : ∃ d, pt B q₀ = d := ⟨_, rfl⟩
        have hdR : d ∈ R := hq₀ ▸ (Finset.mem_filter.mp hq₀mem).2
        obtain ⟨c₀, hc₀⟩ := subtreeAt_eq_decision' B q₀ d hq₀
        -- no `R`-point is queried below `q₀`
        have hbelow : ∀ a, ∀ e ∈ queried (c₀ a), e ∉ R := by
          intro a e he heR
          obtain ⟨q, hq, hlt⟩ := exists_node_lt_of_mem_queried_child' B q₀ d hq₀ c₀ hc₀ a e he
          have := hq₀min q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq ▸ heR⟩)
          omega
        obtain ⟨a₀, -, ha₀⟩ := Finset.exists_max_image (Finset.univ : Finset (acts d))
          (fun a => value (Proc.ofFun σ₀) (c₀ a)) Finset.univ_nonempty
        obtain ⟨σ, hσ, hgood⟩ :=
          ih (R.erase d) (Finset.erase_ssubset hdR) (Function.update σ₀ d a₀)
        have hσd : σ d = a₀ := by
          rw [hσ d (Finset.notMem_erase d R), Function.update_self]
        have hσ' : ∀ e, e ∉ R → σ e = σ₀ e := by
          intro e he
          have hne : e ≠ d := fun h => he (h ▸ hdR)
          rw [hσ e (fun h => he (Finset.mem_of_mem_erase h)), Function.update_of_ne hne]
        have hval : ∀ a, value (Proc.ofFun σ) (c₀ a) = value (Proc.ofFun σ₀) (c₀ a) := by
          intro a
          apply value_congr_queried
          intro e he
          show FinDistr.pure (σ e) = FinDistr.pure (σ₀ e)
          rw [hσ' e (hbelow a e he)]
        have hd_good : ∀ a, Q (Proc.ofFun σ) B d a ≤ Q (Proc.ofFun σ) B d (σ d) := by
          intro a
          rw [← stronglyFair_value_eq_Q hB (Proc.ofFun σ) hc₀ a,
            ← stronglyFair_value_eq_Q hB (Proc.ofFun σ) hc₀ (σ d), hval a, hval (σ d), hσd]
          exact ha₀ a (Finset.mem_univ a)
        refine ⟨σ, hσ', fun d' hd' hd'R a => ?_⟩
        by_cases hdd : d' = d
        · subst hdd
          exact hd_good a
        · exact hgood d' hd' (Finset.mem_erase.mpr ⟨hdd, hd'R⟩) a
      · refine ⟨σ₀, fun _ _ => rfl, fun d hd hdR a => ?_⟩
        exfalso
        obtain ⟨q, hq⟩ := exists_decNode_of_mem_queried B d hd
        exact hN ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq ▸ hdR⟩⟩
  obtain ⟨σ, -, hσ⟩ := key (queried B) (fun _ => Classical.arbitrary _)
  exact ⟨σ, fun d hd a => hσ d hd hd a⟩

end argmax

/-! ### Assignments against a pointwise best deterministic procedure -/

section assignments

omit [Fintype Ω] [DecidableEq Ω] in
/-- `∑_a δ_{b}(a) · f a = f b`. Source: none: infrastructure. Kind: L -/
theorem sum_pure_w_mul {α : Type} [Fintype α] [DecidableEq α] (b : α) (f : α → K) :
    ∑ a, (FinDistr.pure b : FinDistr K α).w a * f a = f b := by
  rw [Finset.sum_eq_single b]
  · simp [FinDistr.pure_w]
  · intro a _ ha; simp [FinDistr.pure_w, ha]
  · intro h; exact absurd (Finset.mem_univ b) h

omit [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] in
/-- **No assignment beats a pointwise best deterministic procedure**: if at every decision node
`decision d c` of `T` the action `σ d` maximises `a ↦ V_{c a}(ofFun σ)`, then every assignment
`π` of `T` has `V_T(π) ≤ V_T(ofFun σ)`. Structural induction: at a decision node the assignment
plays some `π(q)` at the root and an assignment of the `π(q)`-child below, dominated by the
induction hypothesis and then by `σ d`.
Source: `fair-repair.md` after FR-11 ("Fair-tree assignment lemma"); [[decision-problems-v2]]
Proposition 5(b) (the backward-induction shape of `exists_assign_ge`)
Kind: P
Fidelity: exact
Hyps: (a) pointwise best response at every decision node of `T` -/
theorem valueAssign_le_of_pointwise_best (σ : (d : ι) → acts d) :
    (T : Tree Ω ι acts K) →
      (∀ (q : T.DecNode) (d : ι) (c : acts d → Tree Ω ι acts K), subtreeAt T q = .decision d c →
        ∀ a, value (Proc.ofFun σ) (c a) ≤ value (Proc.ofFun σ) (c (σ d))) →
      ∀ π : Assign T, valueAssign T π ≤ value (Proc.ofFun σ) T
  | leaf ω r, _, π => by
      unfold valueAssign
      rw [valueNode_leaf, DpLocalOpt.value_leaf]
  | chance n β child, hbest, π => by
      unfold valueAssign
      rw [valueNode_chance, DpLocalOpt.value_chance]
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (β.nonneg i)
      exact valueAssign_le_of_pointwise_best σ (child i)
        (fun q d c hc a => hbest ⟨i, q⟩ d c (by simpa using hc) a) (fun q => π ⟨i, q⟩)
  | decision d child, hbest, π => by
      unfold valueAssign
      rw [valueNode_decision, DpLocalOpt.value_decision]
      have hroot : ∑ a, (NodePolicy.ofAssign π none).w a *
          valueNode (child a) ((NodePolicy.ofAssign π).restrictDecision a) =
          valueAssign (child (π none)) (fun q => π (some ⟨π none, q⟩)) := by
        change ∑ a, (FinDistr.pure (π none)).w a *
          valueNode (child a) (NodePolicy.ofAssign fun q => π (some ⟨a, q⟩)) = _
        rw [sum_pure_w_mul]
        rfl
      have hσ : ∑ a, (Proc.ofFun σ d).w a * value (Proc.ofFun σ) (child a) =
          value (Proc.ofFun σ) (child (σ d)) := by
        change ∑ a, (FinDistr.pure (σ d)).w a * value (Proc.ofFun σ) (child a) = _
        rw [sum_pure_w_mul]
      rw [hroot, hσ]
      calc valueAssign (child (π none)) (fun q => π (some ⟨π none, q⟩))
          ≤ value (Proc.ofFun σ) (child (π none)) :=
            valueAssign_le_of_pointwise_best σ (child (π none))
              (fun q d' c hc a => hbest (some ⟨π none, q⟩) d' c (by simpa using hc) a) _
        _ ≤ value (Proc.ofFun σ) (child (σ d)) := hbest none d child rfl (π none)

end assignments

/-! ### T5 -/

section t5

omit [Fintype Ω] [DecidableEq Ω] in
/-- **T5, the fair-tree assignment lemma**: on a strongly fair tree some deterministic
procedure is at least as good as every assignment, so `max_π V_B(π) = max_C V_B(C)` is attained
deterministically (`value_le_valueAssign` gives the other inequality). Route: the leaves-up
fiber-constant argmax `exists_pointwise_best`, then `valueAssign_le_of_pointwise_best` with the
pointwise-best hypothesis transported to every node by `stronglyFair_value_eq_Q`. The argmax is
chosen by `Classical.choice`; no `LinearOrder` on `acts d` is assumed.
Source: `fair-repair.md` after FR-11 ("Fair-tree assignment lemma"); A25; Proposition 5(d);
dp-cf-021
Kind: P
Fidelity: exact
Hyps: (a) `StronglyFair B` -/
theorem stronglyFair_assignment [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (hB : StronglyFair B) :
    ∃ σ : (d : ι) → acts d, ∀ π : Assign B, valueAssign B π ≤ value (Proc.ofFun σ) B := by
  obtain ⟨σ, hσ⟩ := exists_pointwise_best hB
  refine ⟨σ, valueAssign_le_of_pointwise_best σ B fun q d c hc a => ?_⟩
  have hd : d ∈ queried B := (pt_eq_of_subtreeAt_eq hc) ▸ pt_mem_queried B q
  rw [stronglyFair_value_eq_Q hB _ hc a, stronglyFair_value_eq_Q hB _ hc (σ d)]
  exact hσ d hd a

omit [Fintype Ω] [DecidableEq Ω] in
/-- **`max_π V_B(π) = max_C V_B(C)` on strongly fair trees, attained deterministically**: the
`σ` of T5 is optimal among all (mixed) procedures and dominates every assignment.
Source: `fair-repair.md` after FR-11 ("`max_π V_B(π) = max_C V_B(C)`"); A25;
[[decision-problems-v2]] Proposition 5(d)
Kind: C
Fidelity: exact
Hyps: (a) `StronglyFair B` -/
theorem stronglyFair_assignment_max [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (hB : StronglyFair B) :
    ∃ σ : (d : ι) → acts d, IsOptimal (Proc.ofFun σ) B ∧
      ∀ π : Assign B, valueAssign B π ≤ value (Proc.ofFun σ) B := by
  obtain ⟨σ, hσ⟩ := stronglyFair_assignment hB
  obtain ⟨π, hπ⟩ := exists_assign_max B
  exact ⟨σ, fun C => (value_le_valueAssign B π hπ C).trans (hσ π), hσ⟩

omit [Fintype Ω] [DecidableEq Ω] in
/-- A strongly fair tree has a deterministic optimal procedure (the `UDT_B` of Remark 6.2 without
injectivity of `q ↦ d_q`).
Source: [[decision-problems-v2]] Remark 6.2; `fair-repair.md` after FR-11
Kind: C -/
theorem stronglyFair_exists_isOptimal_ofFun [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (hB : StronglyFair B) : ∃ σ : (d : ι) → acts d, IsOptimal (Proc.ofFun σ) B :=
  let ⟨σ, h, _⟩ := stronglyFair_assignment_max hB
  ⟨σ, h⟩

end t5

/-! ### Witness: `dupPay 1 0` -/

section dupPayWitness

open Cleanroom.Found.DpCoreTree.Catalogue

/-- The assignment on `dupPay 1 0` playing `a` at the first copy and `b` at the second (not
fiber-constant).
Source: mandate T5 ("Witness: `dupPay 1 0` (two members, one action per point forced)")
Kind: D -/
def dupMixAssign : Assign (dupPay 1 0) := fun q => if q.1 = 0 then Act2.a else Act2.b

/-- **T5's witness on the two-member fiber `dupPay 1 0`**: every assignment is at most `δ_a`'s
value `1`, while the non-fiber-constant assignment `dupMixAssign` has value `½` — the
assignment optimum is attained by the deterministic procedure `δ_a`, and assignments genuinely
range beyond procedures' fiber-constant plays.
Source: mandate T5
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem dupPay_assignment_witness :
    (∀ π : Assign (dupPay 1 0), valueAssign (dupPay 1 0) π ≤
      value (Proc.ofFun fun _ => Act2.a) (dupPay 1 0)) ∧
    value (Proc.ofFun fun _ => Act2.a) (dupPay 1 0) = 1 ∧
    valueAssign (dupPay 1 0) dupMixAssign = 1 / 2 := by
  refine ⟨fun π => ?_, ?_, ?_⟩
  · apply valueAssign_le_of_pointwise_best
    intro q d c hc a
    rw [dupPay_subtree] at hc
    cases d
    unfold dupNode at hc
    simp only [Tree.decision.injEq, heq_eq_eq, true_and] at hc
    subst hc
    cases a <;> simp [DpLocalOpt.value_leaf]
  · have hpa : (Proc.ofFun fun _ => Act2.a : Proc Unit (fun _ => Act2) ℚ) =
        procQ 1 zero_le_one le_rfl := by
      funext d; apply FinDistr.ext'; intro x; cases x <;> simp [Proc.ofFun, procQ, FinDistr.act2]
    rw [hpa, dupPay_value]; norm_num
  · unfold valueAssign dupMixAssign dupPay dupNode
    rw [valueNode_chance, Fin.sum_univ_two]
    simp only [NodePolicy.restrictChance, valueNode_decision, Act2.sum_univ, valueNode_leaf,
      NodePolicy.ofAssign, FinDistr.pure_w, FinDistr.fair, FinDistr.coin]
    simp

end dupPayWitness

end Cleanroom.Decision.DpEdtUdtFair

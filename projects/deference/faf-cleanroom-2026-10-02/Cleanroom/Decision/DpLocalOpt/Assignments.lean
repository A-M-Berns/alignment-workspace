import Cleanroom.Decision.DpLocalOpt.AmdWitness

/-!
# `dp-local-opt`: Proposition 5 — procedures versus assignments (T1)

An *assignment* is a pure node-level policy `π : (q : B.DecNode) → acts (pt B q)` (v2
Proposition 5(a)); `V_B(π) := valueNode B (q ↦ δ_{π q})`. This file proves:

* (a) an optimal assignment exists (`exists_assign_max`);
* (b) `V_B(C) ≤ max_π V_B(π)` for every procedure — by **backward induction** on the tree: every
  node-level policy is dominated by an assignment that picks, at each node, the best child's
  assignment (`exists_assign_ge`); equality when some optimal assignment is constant on the
  fibers of `q ↦ d_q` (`isOptimal_ofFun_of_fiberConstant`), in particular when `pt` is
  injective (`exists_isOptimal_ofFun_of_injective`, Remark 6.2's `UDT_B`);
* (c) strictness on the AMD: the assignment `(b, a)` reaches `4`, deterministic procedures get
  `0` or `1`, the best procedure gets `4/3` (`amd_assign_gap`).

v2's proof of (b) goes through "the realized node-action profile is a random assignment with
product law, so `V_B(C)` is an average of assignment values" (the node-level interpolation
identity). The inequality is proved here directly by backward induction; the interpolation
identity itself is not shipped (see the report, T1).
-/

namespace Cleanroom.Decision.DpLocalOpt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]

/-! ### Node equations for `valueNode` -/

section valueNodeEqns

/-- `valueNode` at a leaf is its payoff.
Source: none: infrastructure
Kind: L -/
@[simp] theorem valueNode_leaf (ω : Ω) (r : K) (p : NodePolicy (leaf ω r : Tree Ω ι acts K)) :
    valueNode (leaf ω r) p = r := by
  show ∑ _ℓ : Unit, (1 : K) * r = r
  simp

/-- `valueNode` at a chance node.
Source: none: infrastructure
Kind: L -/
theorem valueNode_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K)
    (p : NodePolicy (chance n β child)) :
    valueNode (chance n β child) p = ∑ i, β.w i * valueNode (child i) (p.restrictChance i) := by
  unfold valueNode
  rw [sum_leaves_chance]
  simp only [leafLawNode_chance, payoff_chance, Finset.mul_sum, mul_assoc]

/-- `valueNode` at a decision node.
Source: none: infrastructure
Kind: L -/
theorem valueNode_decision (d : ι) (child : acts d → Tree Ω ι acts K)
    (p : NodePolicy (decision d child)) :
    valueNode (decision d child) p =
      ∑ a, (p none).w a * valueNode (child a) (p.restrictDecision a) := by
  unfold valueNode
  rw [sum_leaves_decision]
  simp only [leafLawNode_decision, payoff_decision, Finset.mul_sum, mul_assoc]
  rfl

end valueNodeEqns

/-! ### Assignments -/

section assign

/-- **An assignment** (v2 Proposition 5(a)): one action per decision node.
Source: [[decision-problems-v2]] Proposition 5(a) (line 203, "a map `π` from decision nodes to
actions with `π(q) ∈ A_{d_q}`")
Kind: D -/
def Assign (B : Tree Ω ι acts K) : Type := (q : B.DecNode) → acts (pt B q)

/-- Assignments of a finite tree form a finite type.
Source: none: infrastructure
Kind: D -/
instance (B : Tree Ω ι acts K) : Fintype (Assign B) :=
  inferInstanceAs (Fintype ((q : B.DecNode) → acts (pt B q)))

/-- The pure node-level policy of an assignment.
Source: [[decision-problems-v2]] Proposition 5(a) ("`V_B` extends to assignments")
Kind: D -/
def NodePolicy.ofAssign {B : Tree Ω ι acts K} (π : Assign B) : NodePolicy B :=
  fun q => FinDistr.pure (π q)

/-- The assignment on a decision node built from a root action and one assignment per child.
Source: none: infrastructure
Kind: D -/
def Assign.decisionMk {d : ι} {child : acts d → Tree Ω ι acts K} (b₀ : acts d)
    (π : (b : acts d) → Assign (child b)) : Assign (decision d child) :=
  fun q => match (q : Option (Σ b : acts d, (child b).DecNode)) with
    | none => b₀
    | some ⟨b, q'⟩ => π b q'

/-- `V_B(π)`, the value of an assignment.
Source: [[decision-problems-v2]] Proposition 5(a)
Kind: D -/
def valueAssign (B : Tree Ω ι acts K) (π : Assign B) : K := valueNode B (NodePolicy.ofAssign π)

/-- **Proposition 5(a)**: `max_π V_B(π)` is attained.
Source: [[decision-problems-v2]] Proposition 5(a) ("`max_π V_B(π)` is attained")
Kind: L -/
theorem exists_assign_max [∀ d, Nonempty (acts d)] (B : Tree Ω ι acts K) :
    ∃ π : Assign B, ∀ π', valueAssign B π' ≤ valueAssign B π := by
  haveI : Nonempty (Assign B) := ⟨fun q => Classical.arbitrary _⟩
  obtain ⟨π, -, h⟩ := Finset.exists_max_image (Finset.univ : Finset (Assign B)) (valueAssign B)
    Finset.univ_nonempty
  exact ⟨π, fun π' => h π' (Finset.mem_univ _)⟩

/-- **Backward induction**: every node-level policy is dominated by an assignment (pick at each
node the child whose dominating assignment is best).
Source: [[decision-problems-v2]] Proposition 5(b) (the inequality `max_C V_B(C) ≤ max_π V_B(π)`)
Kind: P
Fidelity: exact (the inequality; v2's route through the product-law interpolation is not taken)
Hyps: (a) all -/
theorem exists_assign_ge :
    (B : Tree Ω ι acts K) → ∀ p : NodePolicy B, ∃ π : Assign B, valueNode B p ≤ valueAssign B π
  | leaf ω r, p => ⟨fun q => q.elim, by unfold valueAssign; rw [valueNode_leaf, valueNode_leaf]⟩
  | chance n β child, p => by
      choose π hπ using fun i => exists_assign_ge (child i) (p.restrictChance i)
      refine ⟨fun q => π q.1 q.2, ?_⟩
      unfold valueAssign
      rw [valueNode_chance, valueNode_chance]
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hπ i) (β.nonneg i)
  | decision d child, p => by
      choose π hπ using fun b => exists_assign_ge (child b) (p.restrictDecision b)
      haveI : Nonempty (acts d) := FinDistr.nonempty_of_finDistr (p none)
      obtain ⟨b₀, -, hb₀⟩ := Finset.exists_max_image (Finset.univ : Finset (acts d))
        (fun b => valueAssign (child b) (π b)) Finset.univ_nonempty
      refine ⟨Assign.decisionMk b₀ π, ?_⟩
      unfold valueAssign
      rw [valueNode_decision, valueNode_decision]
      have hsum : ∑ a, (NodePolicy.ofAssign (Assign.decisionMk b₀ π) none).w a *
          valueNode (child a) ((NodePolicy.ofAssign (Assign.decisionMk b₀ π)).restrictDecision a) =
          valueAssign (child b₀) (π b₀) := by
        refine (Finset.sum_eq_single b₀ (fun c _ hc => ?_)
          (fun h => absurd (Finset.mem_univ b₀) h)).trans ?_
        · show (FinDistr.pure b₀).w c * _ = 0
          simp [FinDistr.pure_w, hc]
        · show (FinDistr.pure b₀).w b₀ * valueNode (child b₀) (NodePolicy.ofAssign (π b₀)) = _
          simp [FinDistr.pure_w, valueAssign]
      rw [hsum]
      calc ∑ a, (p none).w a * valueNode (child a) (p.restrictDecision a)
          ≤ ∑ a, (p none).w a * valueAssign (child b₀) (π b₀) := by
            apply Finset.sum_le_sum
            intro a _
            exact mul_le_mul_of_nonneg_left ((hπ a).trans (hb₀ a (Finset.mem_univ a)))
              ((p none).nonneg a)
        _ = valueAssign (child b₀) (π b₀) := by rw [← Finset.sum_mul, (p none).sum_one, one_mul]

/-- **Proposition 5(b), the inequality**: `V_B(C) ≤ max_π V_B(π)` for **every** procedure, on
every tree (self-succession included).
Source: [[decision-problems-v2]] Proposition 5(b) (line 203, "`max_C V_B(C) ≤ max_π V_B(π)`") |
dp-core-030
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem value_le_valueAssign (B : Tree Ω ι acts K) (π : Assign B)
    (hmax : ∀ π', valueAssign B π' ≤ valueAssign B π) (C : Proc ι acts K) :
    value C B ≤ valueAssign B π := by
  obtain ⟨π', h⟩ := exists_assign_ge B (NodePolicy.ofProc C B)
  rw [valueNode_ofProc] at h
  exact h.trans (hmax π')

/-- An assignment is *fiber-constant* with witness `σ` if it plays `σ(d_q)` at every node `q`.
Source: [[decision-problems-v2]] Proposition 5(b) ("constant on the fibers of `q ↦ d_q`")
Kind: D -/
def Assign.FiberConstant {B : Tree Ω ι acts K} (π : Assign B) (σ : (d : ι) → acts d) : Prop :=
  ∀ q, π q = σ (pt B q)

/-- A fiber-constant assignment is the tied policy of the deterministic procedure `σ`.
Source: [[decision-problems-v2]] Proposition 5(b)
Kind: L -/
theorem valueAssign_eq_of_fiberConstant {B : Tree Ω ι acts K} {π : Assign B}
    {σ : (d : ι) → acts d} (h : π.FiberConstant σ) :
    valueAssign B π = value (Proc.ofFun σ) B := by
  unfold valueAssign
  rw [← valueNode_ofProc]
  congr 1
  funext q
  simp only [NodePolicy.ofAssign, NodePolicy.ofProc, Proc.ofFun, h q]

/-- **Proposition 5(b), equality clause**: if some optimal assignment is constant on the fibers,
the deterministic procedure it defines is optimal (`max_C V_B(C) = max_π V_B(π)`).
Source: [[decision-problems-v2]] Proposition 5(b) ("with equality whenever some optimal assignment
is constant on the fibers of `q ↦ d_q`") | dp-core-030
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem isOptimal_ofFun_of_fiberConstant (B : Tree Ω ι acts K) (π : Assign B)
    (hmax : ∀ π', valueAssign B π' ≤ valueAssign B π) {σ : (d : ι) → acts d}
    (h : π.FiberConstant σ) : IsOptimal (Proc.ofFun σ) B := by
  intro C'
  rw [← valueAssign_eq_of_fiberConstant h]
  exact value_le_valueAssign B π hmax C'

/-- When `q ↦ d_q` is injective every assignment is fiber-constant.
Source: [[decision-problems-v2]] Proposition 5(b) ("in particular whenever that map is
injective")
Kind: L -/
theorem exists_fiberConstant_of_injective [∀ d, Nonempty (acts d)] (B : Tree Ω ι acts K)
    (hinj : Function.Injective (pt B)) (π : Assign B) :
    ∃ σ : (d : ι) → acts d, π.FiberConstant σ := by
  classical
  refine ⟨fun d => if h : ∃ q, pt B q = d then cast (congrArg acts h.choose_spec) (π h.choose)
    else Classical.arbitrary _, ?_⟩
  intro q
  have hex : ∃ q', pt B q' = pt B q := ⟨q, rfl⟩
  have key : ∀ (q' : B.DecNode) (e : q' = q) (s : pt B q' = pt B q),
      cast (congrArg acts s) (π q') = π q := by
    intro q' e s; subst e; rfl
  show π q = (if h : ∃ q', pt B q' = pt B q then cast (congrArg acts h.choose_spec) (π h.choose)
    else Classical.arbitrary _)
  rw [dif_pos hex]
  exact (key hex.choose (hinj hex.choose_spec) hex.choose_spec).symm

/-- **Remark 6.2 (`UDT_B`)**: when `q ↦ d_q` is injective, some deterministic procedure is
optimal on `B` — the procedure agreeing with an optimal assignment.
Source: [[decision-problems-v2]] Remark 6.2 (line 209, "when `q ↦ d_q` is injective on queried
nodes, `UDT_B` is optimal on `B`") | Proposition 5(b) | dp-core-031
Kind: C
Fidelity: exact (every node carries a queried point, so "injective on queried nodes" is
injectivity of `pt B`)
Hyps: (a) all -/
theorem exists_isOptimal_ofFun_of_injective [∀ d, Nonempty (acts d)] (B : Tree Ω ι acts K)
    (hinj : Function.Injective (pt B)) : ∃ σ : (d : ι) → acts d, IsOptimal (Proc.ofFun σ) B := by
  obtain ⟨π, hmax⟩ := exists_assign_max B
  obtain ⟨σ, hσ⟩ := exists_fiberConstant_of_injective B hinj π
  exact ⟨σ, isOptimal_ofFun_of_fiberConstant B π hmax hσ⟩

end assign

/-! ### T1(c): strictness on the AMD -/

section amdAssign

/-- The (unique) assignment on a leaf.
Source: none: infrastructure
Kind: D -/
def Assign.ofLeaf {ω : Ω} {r : K} : Assign (leaf ω r : Tree Ω ι acts K) := fun q => Empty.elim q

/-- The AMD assignment `(b, a)`: continue at the first node, exit at the second.
Source: [[decision-problems-v2]] Proposition 5(c) ("assignments reach `4`")
Kind: D -/
def amdAssign : Assign amd :=
  Assign.decisionMk .b fun b => match b with
    | .a => Assign.ofLeaf
    | .b => Assign.decisionMk .a fun c => match c with
      | .a => Assign.ofLeaf
      | .b => Assign.ofLeaf

/-- `ofAssign` of `decisionMk` at the node is the point mass on the root action.
Source: none: infrastructure
Kind: L -/
@[simp] theorem ofAssign_decisionMk_none {d : ι} {child : acts d → Tree Ω ι acts K} (b₀ : acts d)
    (π : (b : acts d) → Assign (child b)) :
    NodePolicy.ofAssign (Assign.decisionMk b₀ π) none = FinDistr.pure b₀ := rfl

/-- `ofAssign` of `decisionMk` restricted to a child is `ofAssign` of that child's assignment.
Source: none: infrastructure
Kind: L -/
@[simp] theorem ofAssign_decisionMk_restrict {d : ι} {child : acts d → Tree Ω ι acts K}
    (b₀ : acts d) (π : (b : acts d) → Assign (child b)) (b : acts d) :
    (NodePolicy.ofAssign (Assign.decisionMk b₀ π)).restrictDecision b =
      NodePolicy.ofAssign (π b) := rfl

/-- `V_{amd}(b, a) = 4`.
Source: [[decision-problems-v2]] Proposition 5(c) ("assignments reach `4`")
Kind: N+ -/
theorem amd_valueAssign : valueAssign amd amdAssign = 4 := by
  unfold valueAssign amdAssign amd
  simp only [valueNode_decision, valueNode_leaf, Act2.sum_univ, ofAssign_decisionMk_none,
    ofAssign_decisionMk_restrict, FinDistr.pure_w]
  norm_num
  all_goals decide

/-- Every deterministic one-point procedure on the AMD is worth `0` or `1`.
Source: [[decision-problems-v2]] Proposition 5(c) ("deterministic procedures get `0` or `1`")
Kind: N+ -/
theorem amd_value_ofFun (σ : Unit → Act2) :
    value (Proc.ofFun σ) amd = 0 ∨ value (Proc.ofFun σ) amd = 1 := by
  cases h : σ ()
  · left
    have : Proc.ofFun σ = procQ 1 zero_le_one le_rfl := by
      funext u; cases u; simp [Proc.ofFun, h, procQ, pure_a_eq_act2]
    rw [this, amd_value]; norm_num
  · right
    have : Proc.ofFun σ = procQ 0 le_rfl zero_le_one := by
      funext u; cases u; simp [Proc.ofFun, h, procQ, pure_b_eq_act2]
    rw [this, amd_value]; norm_num

/-- **Proposition 5(c), strictness**: on the AMD every procedure is worth at most `4/3`
(attained at `C(d)(a) = 1/3`), deterministic procedures `0` or `1`, and the assignment `(b, a)`
`4`: `max_C V_B(C) = 4/3 < 4 = max_π V_B(π)`.
Source: [[decision-problems-v2]] Proposition 5(c) (line 203) | Remark 6.1 | dp-core-030
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem amd_assign_gap :
    (∀ C : Proc Unit (fun _ => Act2) ℚ, value C amd ≤ 4/3) ∧
    value (procQ (1/3) (by norm_num) (by norm_num)) amd = 4/3 ∧
    valueAssign amd amdAssign = 4 := by
  refine ⟨fun C => ?_, by rw [amd_value]; norm_num, amd_valueAssign⟩
  have h := (amd_isOptimal_iff (1/3) (by norm_num) (by norm_num)).mpr rfl C
  rw [amd_value] at h
  norm_num at h
  exact h

end amdAssign

end Cleanroom.Decision.DpLocalOpt

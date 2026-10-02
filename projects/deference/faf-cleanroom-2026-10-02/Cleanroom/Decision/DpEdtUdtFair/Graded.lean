import Cleanroom.Decision.DpEdtUdtFair.Limit

/-!
# The graded FR-11 (GR-10 / A37): loss at most `2 · H · D` under a fiber value-disagreement bound
(T9)

No strong fairness: only almost fairness, `FRec`, pruned chance and realized observations
(`FRecPR`), plus a bound `D` on the fiber value-disagreement of every small tremble. Then
event-tremble-EDT-consistency gives `∀ C', V_B(C') ≤ V_B(C) + 2 · decDepth B · D`.

* `FiberValueBound C B D` (D, representation decision 5): every two `d`-nodes' `a`-children have
  values within `D`, for every `d`, `a`. `decDepth` (D): the maximum number of decision nodes on a
  path.
* `sandwich` (P): the leaf-sum engine. For a world event `X`, when every `d`-node's `a`-branch
  either lies entirely inside `X` or entirely outside it, and every `d`-node's `a`-child value lies
  in `[L, U]`, the `X ∧ ⟨d, a⟩`-draw payoff mass lies between `L` and `U` times the corresponding
  probability mass — by structural recursion, no fairness.
* `FRecPR.live_dichotomy` (P): under recording, every `d`-node is *live* (all its `a`-leaves
  satisfy `a ∧ O_d`) or *dead* (none does) — GR-D2′(i): predictor nodes carry no `O_d`-leaf.
* `FRecPR.condExp_bounds` (P) and `FRecPR.value_le_value_add_of_eventTremble` (P): Steps (1)–(2)
  of GR-10: the calibrated act value is a convex combination of live members' values, hence within
  `D` of any member's; D2 then gives `Q_q(C, b) ≤ Q_q(C, a) + 2D` at every `d`-node for every
  supported `a`, first at every small `ε`, then at `ε = 0`.
* `value_le_value_add_of_pointwise` (P): Step (3), structural recursion on the tree with procedure
  optima; no assignment lemma; no almost-fairness needed in this step.
* **`graded_fr11`** (C): the theorem. Corollary `corner_eventTrembleEdt_isOptimal` (C): at
  `D = 0` with value-fairness, FR-11 on GR-11's corner.

**Findings recorded here.** (i) No evented-chance hypothesis is used (GR-10 lists EC, A37 does
not). (ii) The `ε = 0` endpoint of the value-disagreement bound is not needed: the bound is
assumed only for `0 < ε < ε₀`. (iii) GR-13's classification: strong fairness is the one hypothesis
that grades (into `D`); recording, realized observations and non-nesting stay binary here.
-/

set_option linter.unusedSectionVars false

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

/-! ### Definitions -/

section defs

omit [Fintype Ω] [DecidableEq Ω] [∀ d, DecidableEq (acts d)] [DecidableEq ι] in
/-- **Decision depth**: the maximum number of decision nodes on a root-to-leaf path (GR-10's `H`).
Source: `grounding.md` GR-10 ("`H` = maximum number of decision nodes on a root–leaf path")
Kind: D -/
def decDepth : Tree Ω ι acts K → ℕ
  | .leaf _ _ => 0
  | .chance _ _ child => Finset.univ.sup fun i => decDepth (child i)
  | .decision _ child => 1 + Finset.univ.sup fun a => decDepth (child a)

omit [Fintype Ω] [DecidableEq Ω] [∀ d, DecidableEq (acts d)] [DecidableEq ι] in
/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem decDepth_leaf (ω : Ω) (r : K) : decDepth (leaf ω r : Tree Ω ι acts K) = 0 := rfl

omit [Fintype Ω] [DecidableEq Ω] [∀ d, DecidableEq (acts d)] [DecidableEq ι] in
/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem decDepth_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K) :
    decDepth (chance n β child) = Finset.univ.sup fun i => decDepth (child i) := rfl

omit [Fintype Ω] [DecidableEq Ω] [∀ d, DecidableEq (acts d)] [DecidableEq ι] in
/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem decDepth_decision (d : ι) (child : acts d → Tree Ω ι acts K) :
    decDepth (decision d child) = 1 + Finset.univ.sup fun a => decDepth (child a) := rfl

omit [Fintype Ω] [DecidableEq Ω] [∀ d, DecidableEq (acts d)] [DecidableEq ι] in
/-- **Fiber value-disagreement bounded by `D`**: for every point `d`, every two `d`-nodes (with
subtrees `decision d c`, `decision d c'`) and every action `a`, `|V_{c a}(C) − V_{c' a}(C)| ≤ D`
(GR-10's `D_V(B, C) ≤ D`, stated cast-free through the subtree equations).
Source: `grounding.md` Definitions carried ("`D_V(B,C) := max_d max_{q,q' ∈ F_d} max_a |Q_q(C,a)
− Q_{q'}(C,a)|`"); mandate representation decision 5
Kind: D
Fidelity: exact on almost-fair trees (a bound rather than the `max`; GR-9's `Q_q(C,a) :=
V_{T_q}(C[d ↦ a])` is the deviated-subtree value, which agrees with the child value `V_{c a}(C)`
used here exactly when no `d`-node lies below the `d`-node `q` — `value_deviatePure_decision_eq`,
`almostFair_child_not_queried`; every consumer assumes `AlmostFair`); on almost-fair trees
`ValueFair` is the `D = 0` bound for every procedure, `valueFair_iff_fiberValueBound_zero` -/
def FiberValueBound (C : Proc ι acts K) (B : Tree Ω ι acts K) (D : K) : Prop :=
  ∀ (d : ι) (q q' : B.DecNode) (c c' : acts d → Tree Ω ι acts K),
    subtreeAt B q = .decision d c → subtreeAt B q' = .decision d c' →
    ∀ a, |value C (c a) - value C (c' a)| ≤ D

end defs

/-! ### Almost fairness: no `d`-node below a `d`-node -/

section almostFair

omit [Fintype Ω] [DecidableEq Ω] in
/-- On an almost-fair tree the children of a `d`-node contain no `d`-node.
Source: `fair-repair.md` FR-1(i) (non-nesting); `grounding.md` GR-10 ("no `d`-nodes below
(non-nesting)")
Kind: L -/
theorem almostFair_child_not_queried [∀ d, Nonempty (acts d)] :
    (B : Tree Ω ι acts K) → AlmostFair B → ∀ (q : B.DecNode) (d : ι)
      (c : acts d → Tree Ω ι acts K), subtreeAt B q = .decision d c → ∀ a, d ∉ queried (c a)
  | leaf _ _, _, q, _, _, _, _ => q.elim
  | chance _ β child, hAF, ⟨i, q⟩, d, c, hc, a =>
      almostFair_child_not_queried (child i) (fun e ℓ => by simpa using hAF e ⟨i, ℓ⟩) q d c hc a
  | decision d' child, hAF, none, d, c, hc, a => by
      change Tree.decision d' child = Tree.decision d c at hc
      simp only [Tree.decision.injEq] at hc
      obtain ⟨rfl, hc⟩ := hc
      have hc' : child = c := eq_of_heq hc
      subst hc'
      intro hq
      obtain ⟨ℓ, hℓ⟩ := (mem_queried_iff d' (child a)).mp hq
      have := hAF d' ⟨a, ℓ⟩
      simp only [count_decision, if_true] at this
      omega
  | decision d' child, hAF, some ⟨b, q⟩, d, c, hc, a =>
      almostFair_child_not_queried (child b) (fun e ℓ => by
        have := hAF e ⟨b, ℓ⟩; simp only [count_decision] at this; omega) q d c hc a

omit [Fintype Ω] [DecidableEq Ω] in
/-- On an almost-fair tree, `V_{decision d c}(C[d ↦ a]) = V_{c a}(C)`.
Source: `grounding.md` Definitions carried ("under non-nesting the honest one-step deviation value")
Kind: L -/
theorem value_deviatePure_decision_eq [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (hAF : AlmostFair B) (C : Proc ι acts K) {q : B.DecNode} {d : ι}
    {c : acts d → Tree Ω ι acts K} (hc : subtreeAt B q = .decision d c) (a : acts d) :
    value (C.deviatePure d a) (.decision d c) = value C (c a) := by
  rw [DpLocalOpt.value_decision]
  have hno : ∀ b, value (C.deviatePure d a) (c b) = value C (c b) := fun b => by
    apply value_congr_queried
    intro e he
    have hed : e ≠ d := fun h => almostFair_child_not_queried B hAF q d c hc b (h ▸ he)
    exact Proc.deviate_ne C _ hed
  simp only [hno, Proc.deviatePure, Proc.deviate_same, FinDistr.pure_w]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ a) h

omit [Fintype Ω] [DecidableEq Ω] in
/-- **Value-fairness is the `D = 0` bound for every procedure** on almost-fair trees.
Source: `grounding.md` GR-9 ("value-fair (`D_V(B,C) = 0` for every `C`)"); mandate representation
decision 5
Kind: L
Fidelity: exact on almost-fair trees (`AlmostFair` is needed to read `V_{T_q}(C[d ↦ a])` as
`V_{c a}(C)`) -/
theorem valueFair_iff_fiberValueBound_zero [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (hAF : AlmostFair B) : ValueFair B ↔ ∀ C : Proc ι acts K, FiberValueBound C B 0 := by
  constructor
  · intro hVF C d q q' c c' hc hc' a
    have h := hVF d q ((mem_fiber B d q).mpr (pt_eq_of_subtreeAt_eq hc)) q'
      ((mem_fiber B d q').mpr (pt_eq_of_subtreeAt_eq hc')) C a
    rw [hc, hc', value_deviatePure_decision_eq hAF C hc, value_deviatePure_decision_eq hAF C hc'] at h
    rw [h, sub_self, abs_zero]
  · intro hFV d q hq q' hq' C a
    obtain ⟨c, hc⟩ := subtreeAt_eq_decision' B q d ((mem_fiber B d q).mp hq)
    obtain ⟨c', hc'⟩ := subtreeAt_eq_decision' B q' d ((mem_fiber B d q').mp hq')
    have := hFV C d q q' c c' hc hc' a
    rw [abs_nonpos_iff, sub_eq_zero] at this
    rw [hc, hc', value_deviatePure_decision_eq hAF C hc, value_deviatePure_decision_eq hAF C hc', this]

end almostFair

/-! ### Tagged edges through the recursion -/

section edgeS

omit [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] in
/-- `edgeS` at a chance node's descendant, read on a leaf under the same child.
Source: none: infrastructure
Kind: L -/
theorem edgeS_chance_same {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K)
    (i : Fin n) (q : (child i).DecNode) (ℓ : (child i).Leaves) :
    edgeS (chance n β child) ⟨i, q⟩ ⟨i, ℓ⟩ = edgeS (child i) q ℓ := by
  unfold edgeS
  rw [edgeOf_chance_same]
  rfl

omit [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] in
/-- `edgeS` at a decision node's descendant, read on a leaf under the same child.
Source: none: infrastructure
Kind: L -/
theorem edgeS_decision_some_same (d : ι) (child : acts d → Tree Ω ι acts K) (b : acts d)
    (q : (child b).DecNode) (ℓ : (child b).Leaves) :
    edgeS (decision d child) (some ⟨b, q⟩) ⟨b, ℓ⟩ = edgeS (child b) q ℓ := by
  unfold edgeS
  rw [edgeOf_decision_some_same]
  rfl

omit [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] in
/-- `edgeS` at a decision node's root: the tagged edge is the action taken.
Source: none: infrastructure
Kind: L -/
theorem edgeS_decision_none (d : ι) (child : acts d → Tree Ω ι acts K) (b : acts d)
    (ℓ : (child b).Leaves) :
    edgeS (decision d child) none ⟨b, ℓ⟩ = some ⟨d, b⟩ := rfl

end edgeS

/-! ### The sandwich: leaf sums between `L` and `U` times the mass -/

section sandwich

omit [Fintype Ω] in
/-- **The sandwich**: for a world event `X`, a point `d`, an action `a`, and bounds `L ≤ U`, if
`#_d ≤ 1` on every path, every `d`-node's `a`-branch lies entirely inside or entirely outside `X`
(live / dead), and every `d`-node's `a`-child value lies in `[L, U]`, then the payoff mass of the
leaves satisfying `X` and drawing `⟨d, a⟩` lies between `L` and `U` times their probability mass.
By structural recursion; at a `d`-node only the `a`-child contributes (no `d`-node below it),
either fully (live: mass `C(d)(a)`, payoff mass `C(d)(a) · V_{child a}(C)`) or not at all (dead).
Source: `grounding.md` GR-10 proof (1) ("a convex combination of live members' `Q`-values, hence
within `D_V` of every member's")
Kind: P
Fidelity: exact -/
theorem sandwich (C : Proc ι acts K) (d : ι) (a : acts d) (X : Finset Ω) (L U : K) :
    (B : Tree Ω ι acts K) →
      (∀ ℓ, count d B ℓ ≤ 1) →
      (∀ q : B.DecNode, pt B q = d →
        (∀ ℓ, edgeS B q ℓ = some ⟨d, a⟩ → world B ℓ ∈ X) ∨
        (∀ ℓ, edgeS B q ℓ = some ⟨d, a⟩ → world B ℓ ∉ X)) →
      (∀ (q : B.DecNode) (c : acts d → Tree Ω ι acts K), subtreeAt B q = .decision d c →
        L ≤ value C (c a) ∧ value C (c a) ≤ U) →
      L * (∑ ℓ, if world B ℓ ∈ X ∧ (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ then leafLaw C B ℓ else 0)
          ≤ (∑ ℓ, if world B ℓ ∈ X ∧ (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ then
              leafLaw C B ℓ * payoff B ℓ else 0) ∧
      (∑ ℓ, if world B ℓ ∈ X ∧ (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ then
          leafLaw C B ℓ * payoff B ℓ else 0)
        ≤ U * (∑ ℓ, if world B ℓ ∈ X ∧ (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ then leafLaw C B ℓ
            else 0)
  | leaf _ _, _, _, _ => by simp
  | chance _ β child, hc, hdich, hb => by
      have ih : ∀ i,
          L * (∑ ℓ, if world (child i) ℓ ∈ X ∧ (⟨d, a⟩ : Σ d, acts d) ∈ draws (child i) ℓ then
              leafLaw C (child i) ℓ else 0)
            ≤ (∑ ℓ, if world (child i) ℓ ∈ X ∧ (⟨d, a⟩ : Σ d, acts d) ∈ draws (child i) ℓ then
                leafLaw C (child i) ℓ * payoff (child i) ℓ else 0) ∧
          (∑ ℓ, if world (child i) ℓ ∈ X ∧ (⟨d, a⟩ : Σ d, acts d) ∈ draws (child i) ℓ then
              leafLaw C (child i) ℓ * payoff (child i) ℓ else 0)
            ≤ U * (∑ ℓ, if world (child i) ℓ ∈ X ∧ (⟨d, a⟩ : Σ d, acts d) ∈ draws (child i) ℓ then
                leafLaw C (child i) ℓ else 0) := fun i =>
        sandwich C d a X L U (child i) (fun ℓ => by simpa using hc ⟨i, ℓ⟩)
          (fun q hq => by
            rcases hdich ⟨i, q⟩ (by simpa using hq) with h | h
            · left; intro ℓ he
              simpa using h ⟨i, ℓ⟩ (by rw [edgeS_chance_same]; exact he)
            · right; intro ℓ he
              simpa using h ⟨i, ℓ⟩ (by rw [edgeS_chance_same]; exact he))
          (fun q c hq => hb ⟨i, q⟩ c (by simpa using hq))
      have hS : (∑ ℓ, if world (chance _ β child) ℓ ∈ X ∧
          (⟨d, a⟩ : Σ d, acts d) ∈ draws (chance _ β child) ℓ then
            leafLaw C (chance _ β child) ℓ else 0) =
          ∑ i, β.w i * ∑ ℓ, (if world (child i) ℓ ∈ X ∧
            (⟨d, a⟩ : Σ d, acts d) ∈ draws (child i) ℓ then leafLaw C (child i) ℓ else 0) := by
        rw [sum_leaves_chance]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        simp only [world_chance, draws_chance, leafLaw_chance]
        split_ifs <;> ring
      have hP : (∑ ℓ, if world (chance _ β child) ℓ ∈ X ∧
          (⟨d, a⟩ : Σ d, acts d) ∈ draws (chance _ β child) ℓ then
            leafLaw C (chance _ β child) ℓ * payoff (chance _ β child) ℓ else 0) =
          ∑ i, β.w i * ∑ ℓ, (if world (child i) ℓ ∈ X ∧
            (⟨d, a⟩ : Σ d, acts d) ∈ draws (child i) ℓ then
              leafLaw C (child i) ℓ * payoff (child i) ℓ else 0) := by
        rw [sum_leaves_chance]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        simp only [world_chance, draws_chance, leafLaw_chance, payoff_chance]
        split_ifs <;> ring
      rw [hS, hP, Finset.mul_sum, Finset.mul_sum]
      constructor
      · refine Finset.sum_le_sum fun i _ => ?_
        have := mul_le_mul_of_nonneg_left (ih i).1 (β.nonneg i)
        linarith [this]
      · refine Finset.sum_le_sum fun i _ => ?_
        have := mul_le_mul_of_nonneg_left (ih i).2 (β.nonneg i)
        linarith [this]
  | decision d' child, hc, hdich, hb => by
      by_cases hd : d' = d
      · subst hd
        -- only the `a`-child contributes: no `d'`-node below the root
        have hzero : ∀ b, b ≠ a → ∀ ℓ : (child b).Leaves,
            ¬ (world (decision d' child) ⟨b, ℓ⟩ ∈ X ∧
              (⟨d', a⟩ : Σ d, acts d) ∈ draws (decision d' child) ⟨b, ℓ⟩) := by
          intro b hb ℓ ⟨_, hmem⟩
          simp only [draws_decision, List.mem_cons] at hmem
          rcases hmem with heq | hmem
          · exact hb (eq_of_heq (Sigma.mk.inj_iff.mp heq).2).symm
          · have h1 := count_pos_of_mem_draws hmem
            have h2 := hc ⟨b, ℓ⟩
            simp only [count_decision, if_true] at h2
            omega
        have hmem_a : ∀ ℓ : (child a).Leaves,
            (⟨d', a⟩ : Σ d, acts d) ∈ draws (decision d' child) ⟨a, ℓ⟩ := fun ℓ => by
          simp [draws_decision]
        obtain ⟨hL, hU⟩ := hb none child rfl
        have hw := (C d').nonneg a
        rw [sum_leaves_decision, sum_leaves_decision, Finset.sum_eq_single a, Finset.sum_eq_single a]
        · rcases hdich none rfl with hlive | hdead
          · -- live: the `a`-branch is inside `X`
            have hin : ∀ ℓ : (child a).Leaves, world (child a) ℓ ∈ X :=
              fun ℓ => hlive ⟨a, ℓ⟩ (edgeS_decision_none d' child a ℓ)
            simp only [world_decision, hin, hmem_a, and_self, if_true, leafLaw_decision,
              payoff_decision]
            have h1 : (∑ x, (C d').w a * (leafLaw C (child a) x * payoff (child a) x)) =
                (C d').w a * value C (child a) := by
              rw [← Finset.mul_sum]; rfl
            have h2 : (∑ x, (C d').w a * leafLaw C (child a) x) = (C d').w a := by
              rw [← Finset.mul_sum, sum_leafLaw, mul_one]
            simp only [mul_assoc]
            rw [h1, h2]
            constructor <;> nlinarith
          · have hout : ∀ ℓ : (child a).Leaves, world (child a) ℓ ∉ X :=
              fun ℓ => hdead ⟨a, ℓ⟩ (edgeS_decision_none d' child a ℓ)
            simp [world_decision, hout]
        · intro b _ hb'
          exact Finset.sum_eq_zero fun ℓ _ => if_neg (hzero b hb' ℓ)
        · intro h; exact absurd (Finset.mem_univ a) h
        · intro b _ hb'
          exact Finset.sum_eq_zero fun ℓ _ => if_neg (hzero b hb' ℓ)
        · intro h; exact absurd (Finset.mem_univ a) h
      · have ih : ∀ b,
            L * (∑ ℓ, if world (child b) ℓ ∈ X ∧ (⟨d, a⟩ : Σ d, acts d) ∈ draws (child b) ℓ then
                leafLaw C (child b) ℓ else 0)
              ≤ (∑ ℓ, if world (child b) ℓ ∈ X ∧ (⟨d, a⟩ : Σ d, acts d) ∈ draws (child b) ℓ then
                  leafLaw C (child b) ℓ * payoff (child b) ℓ else 0) ∧
            (∑ ℓ, if world (child b) ℓ ∈ X ∧ (⟨d, a⟩ : Σ d, acts d) ∈ draws (child b) ℓ then
                leafLaw C (child b) ℓ * payoff (child b) ℓ else 0)
              ≤ U * (∑ ℓ, if world (child b) ℓ ∈ X ∧ (⟨d, a⟩ : Σ d, acts d) ∈ draws (child b) ℓ
                  then leafLaw C (child b) ℓ else 0) := fun b =>
          sandwich C d a X L U (child b)
            (fun ℓ => by have := hc ⟨b, ℓ⟩; simp only [count_decision] at this; omega)
            (fun q hq => by
              rcases hdich (some ⟨b, q⟩) (by simpa using hq) with h | h
              · left; intro ℓ he
                simpa using h ⟨b, ℓ⟩ (by rw [edgeS_decision_some_same]; exact he)
              · right; intro ℓ he
                simpa using h ⟨b, ℓ⟩ (by rw [edgeS_decision_some_same]; exact he))
            (fun q c hq => hb (some ⟨b, q⟩) c (by simpa using hq))
        have hne : ∀ b, ¬ ((⟨d, a⟩ : Σ d, acts d) = ⟨d', b⟩) :=
          fun b heq => hd (Sigma.mk.inj_iff.mp heq).1.symm
        have hS : (∑ ℓ, if world (decision d' child) ℓ ∈ X ∧
            (⟨d, a⟩ : Σ d, acts d) ∈ draws (decision d' child) ℓ then
              leafLaw C (decision d' child) ℓ else 0) =
            ∑ b, (C d').w b * ∑ ℓ, (if world (child b) ℓ ∈ X ∧
              (⟨d, a⟩ : Σ d, acts d) ∈ draws (child b) ℓ then leafLaw C (child b) ℓ else 0) := by
          rw [sum_leaves_decision]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          simp only [world_decision, draws_decision, leafLaw_decision, List.mem_cons, hne b,
            false_or]
          split_ifs <;> ring
        have hP : (∑ ℓ, if world (decision d' child) ℓ ∈ X ∧
            (⟨d, a⟩ : Σ d, acts d) ∈ draws (decision d' child) ℓ then
              leafLaw C (decision d' child) ℓ * payoff (decision d' child) ℓ else 0) =
            ∑ b, (C d').w b * ∑ ℓ, (if world (child b) ℓ ∈ X ∧
              (⟨d, a⟩ : Σ d, acts d) ∈ draws (child b) ℓ then
                leafLaw C (child b) ℓ * payoff (child b) ℓ else 0) := by
          rw [sum_leaves_decision]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          simp only [world_decision, draws_decision, leafLaw_decision, payoff_decision,
            List.mem_cons, hne b, false_or]
          split_ifs <;> ring
        rw [hS, hP, Finset.mul_sum, Finset.mul_sum]
        constructor
        · refine Finset.sum_le_sum fun b _ => ?_
          have := mul_le_mul_of_nonneg_left (ih b).1 ((C d').nonneg b)
          linarith [this]
        · refine Finset.sum_le_sum fun b _ => ?_
          have := mul_le_mul_of_nonneg_left (ih b).2 ((C d').nonneg b)
          linarith [this]

end sandwich

/-! ### Steps (1)–(2): the calibrated act value is within `D` of every member's value -/

section steps12

variable {obs : ι → Finset Ω} {actEv : (d : ι) → acts d → Finset Ω}

/-- Under `FRec` on a pruned tree with a full-support procedure, a leaf whose world satisfies
`a ∧ O_d` draws `⟨d, a⟩` (the (→) half of the set identity; no fairness needed).
Source: `fair-repair.md` FR-11 Step 1; `grounding.md` GR-10 proof (1)
Kind: L -/
theorem FRecPR.mem_draws_of_mem_actEv_inter_obs {B : Tree Ω ι acts K}
    (h : FRecPR obs actEv B) {C' : Proc ι acts K} (hC' : C'.FullSupport) {d : ι}
    (hd : d ∈ queried B) (a : acts d) (ℓ : B.Leaves) (hw : world B ℓ ∈ actEv d a ∩ obs d) :
    (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ := by
  rw [Finset.mem_inter] at hw
  obtain ⟨hcount, hnodes⟩ := h.frec d hd C' ℓ (pruned_leafLaw_pos h.pruned hC' ℓ) hw.2
  obtain ⟨q, hq, hme⟩ := exists_dNode_of_count_pos d B ℓ (by omega)
  subst hq
  obtain ⟨a₀, ha₀⟩ := Option.isSome_iff_exists.mp hme
  obtain ⟨-, -, huniq⟩ := hnodes q rfl a₀ ha₀
  have haa : a = a₀ := huniq a hw.1
  subst haa
  exact (mem_draws_iff_exists_edgeS B ℓ _).mpr ⟨q, (edgeS_eq_some_iff B q ℓ a).mpr ha₀⟩

/-- **Live or dead (GR-D2′(i))**: under `FRec` on a pruned tree with a full-support procedure,
every `d`-node's `a`-branch lies entirely inside `a ∧ O_d` (the node is subtree-veridical) or
entirely outside it (no `O_d`-leaf below it takes the `a`-edge). Proof: if some `a`-leaf below `q`
satisfies `O_d`, recording at that leaf makes `q` subtree-veridical, and then every `a`-leaf below
`q` satisfies `O_d` and, by recording again, `a`.
Source: `grounding.md` GR-D2′(i) ("every non-live `d`-node has *no* `O_d`-leaf below it");
GR-10 proof (1)
Kind: P
Fidelity: exact -/
theorem FRecPR.live_dichotomy {B : Tree Ω ι acts K} (h : FRecPR obs actEv B)
    {C' : Proc ι acts K} (hC' : C'.FullSupport) {d : ι} (hd : d ∈ queried B) (q : B.DecNode)
    (hq : pt B q = d) (a : acts d) :
    (∀ ℓ, edgeS B q ℓ = some ⟨d, a⟩ → world B ℓ ∈ actEv d a ∩ obs d) ∨
    (∀ ℓ, edgeS B q ℓ = some ⟨d, a⟩ → world B ℓ ∉ actEv d a ∩ obs d) := by
  subst hq
  by_cases hex : ∃ ℓ, edgeS B q ℓ = some ⟨pt B q, a⟩ ∧ world B ℓ ∈ obs (pt B q)
  · left
    obtain ⟨ℓ₀, he₀, ho₀⟩ := hex
    have he₀' := (edgeS_eq_some_iff B q ℓ₀ a).mp he₀
    have hsv : SubtreeVeridical obs B q :=
      ((h.frec _ hd C' ℓ₀ (pruned_leafLaw_pos h.pruned hC' ℓ₀) ho₀).2 q rfl a he₀').1
    intro ℓ he
    have he' := (edgeS_eq_some_iff B q ℓ a).mp he
    have ho : world B ℓ ∈ obs (pt B q) :=
      hsv ℓ ((mem_leavesBelow B q ℓ).mpr (by rw [he']; rfl))
    exact Finset.mem_inter.mpr
      ⟨((h.frec _ hd C' ℓ (pruned_leafLaw_pos h.pruned hC' ℓ) ho).2 q rfl a he').2.1, ho⟩
  · right
    intro ℓ he hin
    exact hex ⟨ℓ, he, (Finset.mem_inter.mp hin).2⟩

/-- **GR-10 Step (1)**: on `FRecPR` trees that are almost fair, under a full-support procedure
whose fiber value-disagreement is at most `D`, the calibrated act value `𝔼_{C'}[r ∣ a ∧ O_d]` lies
within `D` of every `d`-node's `a`-child value.
Source: `grounding.md` GR-10 proof (1) ("a convex combination of live members' `Q`-values, hence
within `D_V` of *every* member's (live or predictor)")
Kind: P
Fidelity: exact
Hyps: (a) `AlmostFair`, (a) `FRecPR`, (a) full support, (a) `FiberValueBound C' B D` -/
theorem FRecPR.condExp_bounds [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FRecPR obs actEv B) (hAF : AlmostFair B) {C' : Proc ι acts K} (hC' : C'.FullSupport)
    {D : K} (hFV : FiberValueBound C' B D) {d : ι} (hd : d ∈ queried B) (q : B.DecNode)
    (c : acts d → Tree Ω ι acts K) (hc : subtreeAt B q = .decision d c) (a : acts d) :
    value C' (c a) - D ≤ condExp C' B (actEv d a ∩ obs d) ∧
    condExp C' B (actEv d a ∩ obs d) ≤ value C' (c a) + D := by
  have hnu : nu C' B (actEv d a ∩ obs d) = ∑ ℓ, if world B ℓ ∈ actEv d a ∩ obs d ∧
      (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ then leafLaw C' B ℓ else 0 := by
    rw [nu_eq_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    by_cases hw : world B ℓ ∈ actEv d a ∩ obs d
    · rw [if_pos hw, if_pos ⟨hw, h.mem_draws_of_mem_actEv_inter_obs hC' hd a ℓ hw⟩]
    · rw [if_neg hw, if_neg (fun h' => hw h'.1)]
  have hpay : paySum C' B (actEv d a ∩ obs d) = ∑ ℓ, if world B ℓ ∈ actEv d a ∩ obs d ∧
      (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ then leafLaw C' B ℓ * payoff B ℓ else 0 := by
    rw [paySum_eq_sum_ite]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    by_cases hw : world B ℓ ∈ actEv d a ∩ obs d
    · rw [if_pos hw, if_pos ⟨hw, h.mem_draws_of_mem_actEv_inter_obs hC' hd a ℓ hw⟩]
    · simp [hw]
  have hpos : 0 < nu C' B (actEv d a ∩ obs d) := h.nu_actEv_inter_obs_pos hC' hd a
  have hbnd : ∀ (q' : B.DecNode) (c' : acts d → Tree Ω ι acts K), subtreeAt B q' = .decision d c' →
      value C' (c a) - D ≤ value C' (c' a) ∧ value C' (c' a) ≤ value C' (c a) + D := by
    intro q' c' hc'
    have := hFV d q' q c' c hc' hc a
    rw [abs_le] at this
    constructor <;> linarith [this.1, this.2]
  have hs := sandwich C' d a (actEv d a ∩ obs d) (value C' (c a) - D) (value C' (c a) + D) B
    (hAF d) (fun q' hq' => h.live_dichotomy hC' hd q' hq' a) hbnd
  obtain ⟨hL, hU⟩ := hs
  rw [← hnu, ← hpay] at hL hU
  unfold condExp
  constructor
  · rw [le_div_iff₀ hpos]; exact hL
  · rw [div_le_iff₀ hpos]; exact hU

/-- **GR-10 Steps (1)–(2)**: on an almost-fair `FRecPR` tree, if every small tremble of `C` has
fiber value-disagreement at most `D` and `C` is event-tremble-EDT-consistent, then at every
`d`-node, every supported action `a` and every `b`, `V_{c b}(C) ≤ V_{c a}(C) + 2D`. (At each small
`ε`: D2 compares the calibrated values, each within `D` of the node's own child value; the
polynomial-limit lemma passes the weak inequality to `ε = 0`.)
Source: `grounding.md` GR-10 proof (2) ("`Q_q(C^ε, a*) ≥ Q_q(C^ε, a) − 2D_V` at every member; …
passes to `ε → 0`")
Kind: P
Fidelity: exact
Hyps: (a) `AlmostFair`, (a) `FRecPR`, (a) the tremble bound on `(0, ε₀)`, (a) D2 -/
theorem FRecPR.value_le_value_add_of_eventTremble [∀ d, Nonempty (acts d)]
    {B : Tree Ω ι acts K} (h : FRecPR obs actEv B) (hAF : AlmostFair B) {C : Proc ι acts K}
    {D ε₀ : K} (hε₀ : 0 < ε₀)
    (hFV : ∀ ε, ∀ (h0 : 0 < ε) (h1 : ε ≤ 1), ε < ε₀ → FiberValueBound (tremble C ε h0.le h1) B D)
    (hC : EventTrembleEdtConsistent obs actEv C B) {d : ι} (q : B.DecNode)
    (c : acts d → Tree Ω ι acts K) (hc : subtreeAt B q = .decision d c) (a : acts d)
    (ha : 0 < (C d).w a) (b : acts d) : value C (c b) ≤ value C (c a) + 2 * D := by
  obtain ⟨ε₁, hε₁, hD2⟩ := hC
  have hd : d ∈ queried B := (pt_eq_of_subtreeAt_eq hc) ▸ pt_mem_queried B q
  obtain ⟨Ra, Ma, hMa, hRa⟩ := value_tremble_eq C (c a)
  obtain ⟨Rb, Mb, hMb, hRb⟩ := value_tremble_eq C (c b)
  have key : ∀ ε, 0 < ε → ε ≤ 1 → ε < min ε₀ ε₁ →
      0 ≤ (value C (c a) + 2 * D - value C (c b)) + ε * (Ra ε - Rb ε) := by
    intro ε h0 h1 hlt
    have hfull := tremble_fullSupport C ε h0 h1
    obtain ⟨-, hle⟩ := hD2 ε h0 h1 (lt_of_lt_of_le hlt (min_le_right _ _)) d hd
      (h.nuPoly_obs_ne_zero C hd) (h.escape_never_fires C ε h0 h1 hd) a ha
    have hb := hle b (h.nu_actEv_inter_obs_pos hfull hd b)
    have hbound := hFV ε h0 h1 (lt_of_lt_of_le hlt (min_le_left _ _))
    obtain ⟨-, hua⟩ := h.condExp_bounds hAF hfull hbound hd q c hc a
    obtain ⟨hlb, -⟩ := h.condExp_bounds hAF hfull hbound hd q c hc b
    rw [hRa ε h0.le h1] at hua
    rw [hRb ε h0.le h1] at hlb
    linarith
  have := nonneg_of_nonneg_near_zero (R := fun ε => Ra ε - Rb ε) (M := Ma + Mb)
    (fun ε h0 h1 => (abs_sub _ _).trans (add_le_add (hMa ε h0 h1) (hMb ε h0 h1)))
    (lt_min hε₀ hε₁) key
  linarith

end steps12

/-! ### Step (3): the height induction with procedure optima -/

section step3

omit [Fintype Ω] [DecidableEq Ω] [∀ d, DecidableEq (acts d)] [DecidableEq ι] in
/-- **GR-10 Step (3)**: if at every decision node every supported action is within `2D` of every
other action's continuation value, then every procedure's value is at most `V_T(C) + 2D ·
decDepth T`. Structural recursion: at a chance node the bound averages; at a decision node
`V_T(C') ≤ max_b V_{child b}(C) + 2D · h` and `V_T(C) ≥ max_b V_{child b}(C) − 2D`.
Source: `grounding.md` GR-10 proof (3) ("induction on height with *procedure* optima")
Kind: P
Fidelity: exact (no assignment lemma; no almost-fairness in this step)
Hyps: (a) `0 ≤ D`, (a) the pointwise `2D`-condition at every node -/
theorem value_le_value_add_of_pointwise [∀ d, Nonempty (acts d)] (C : Proc ι acts K) {D : K}
    (hD : 0 ≤ D) :
    (T : Tree Ω ι acts K) →
      (∀ (q : T.DecNode) (d : ι) (c : acts d → Tree Ω ι acts K), subtreeAt T q = .decision d c →
        ∀ a, 0 < (C d).w a → ∀ b, value C (c b) ≤ value C (c a) + 2 * D) →
      ∀ C' : Proc ι acts K, value C' T ≤ value C T + 2 * D * (decDepth T : K)
  | leaf ω r, _, C' => by simp [DpLocalOpt.value_leaf]
  | chance n β child, hb, C' => by
      have ih : ∀ i, value C' (child i) ≤ value C (child i) + 2 * D * (decDepth (child i) : K) :=
        fun i => value_le_value_add_of_pointwise C hD (child i) (fun q d c hq => hb ⟨i, q⟩ d c hq) C'
      have hdep : ∀ i, (decDepth (child i) : K) ≤ (decDepth (chance n β child) : K) := fun i => by
        rw [decDepth_chance]
        exact_mod_cast Finset.le_sup (f := fun i => decDepth (child i)) (Finset.mem_univ i)
      rw [DpLocalOpt.value_chance, DpLocalOpt.value_chance]
      calc ∑ i, β.w i * value C' (child i)
          ≤ ∑ i, β.w i * (value C (child i) + 2 * D * (decDepth (chance n β child) : K)) := by
            refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (β.nonneg i)
            have := mul_le_mul_of_nonneg_left (hdep i) (by linarith : (0 : K) ≤ 2 * D)
            linarith [ih i]
        _ = ∑ i, β.w i * value C (child i) + 2 * D * (decDepth (chance n β child) : K) := by
            simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, β.sum_one, one_mul]
  | decision d child, hb, C' => by
      have ih : ∀ b, value C' (child b) ≤ value C (child b) + 2 * D * (decDepth (child b) : K) :=
        fun b => value_le_value_add_of_pointwise C hD (child b)
          (fun q e c hq => hb (some ⟨b, q⟩) e c hq) C'
      set H : K := ((Finset.univ.sup fun a => decDepth (child a) : ℕ) : K) with hH
      have hdep : ∀ b, (decDepth (child b) : K) ≤ H := fun b => by
        rw [hH]
        exact_mod_cast Finset.le_sup (f := fun a => decDepth (child a)) (Finset.mem_univ b)
      have hdepT : (decDepth (decision d child) : K) = 1 + H := by
        rw [decDepth_decision, hH]; push_cast; rfl
      obtain ⟨bs, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun b => value C (child b))
        Finset.univ_nonempty
      obtain ⟨as', has'⟩ := FinDistr.exists_pos_w' (C d)
      have hroot : ∀ a, 0 < (C d).w a → ∀ b, value C (child b) ≤ value C (child a) + 2 * D :=
        fun a ha b => hb none d child rfl a ha b
      -- upper bound on `C'`
      have hup : value C' (decision d child) ≤ value C (child bs) + 2 * D * H := by
        rw [DpLocalOpt.value_decision]
        calc ∑ b, (C' d).w b * value C' (child b)
            ≤ ∑ b, (C' d).w b * (value C (child bs) + 2 * D * H) := by
              refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ ((C' d).nonneg b)
              have h1 := hmax b (Finset.mem_univ b)
              have h2 := mul_le_mul_of_nonneg_left (hdep b) (by linarith : (0 : K) ≤ 2 * D)
              linarith [ih b]
          _ = value C (child bs) + 2 * D * H := by
              rw [← Finset.sum_mul, (C' d).sum_one, one_mul]
      -- lower bound on `C`
      have hlow : value C (child bs) - 2 * D ≤ value C (decision d child) := by
        rw [DpLocalOpt.value_decision]
        calc value C (child bs) - 2 * D = ∑ a, (C d).w a * (value C (child bs) - 2 * D) := by
              rw [← Finset.sum_mul, (C d).sum_one, one_mul]
          _ ≤ ∑ a, (C d).w a * value C (child a) := by
              refine Finset.sum_le_sum fun a _ => ?_
              rcases ((C d).nonneg a).lt_or_eq with ha | ha
              · exact mul_le_mul_of_nonneg_left (by linarith [hroot a ha bs]) ha.le
              · rw [← ha]; simp
      rw [hdepT]
      linarith

end step3

/-! ### The theorem and the corner corollary -/

section theorem9

variable {obs : ι → Finset Ω} {actEv : (d : ι) → acts d → Finset Ω}

/-- **GR-10 / A37, the graded FR-11.** On an almost-fair tree that records at every queried point
for every procedure, is pruned, and realizes every queried observation, if every tremble `C^ε`
(`0 < ε < ε₀`) has fiber value-disagreement at most `D ≥ 0` and `C` is event-tremble-EDT-consistent,
then `V_B(C') ≤ V_B(C) + 2 · decDepth B · D` for every `C'`. No evented-chance hypothesis (GR-10
lists one; A37 does not; the proof uses none — finding F6); the bound at `ε = 0` is not needed.
GR-13: strong fairness is the one hypothesis of Theorem 3 that grades (into `D`); recording,
realized observations and non-nesting stay binary here (recording: `toldYouSo` has `D = 0` and
fails by selection, `Necessity.lean`).
Source: `grounding.md` GR-10 ("`V_B(C) ≥ max_{C'} V_B(C') − 2HD_V`"); `v2-amendments.md` A37;
dp-cf-029, dp-cf-2-027
Kind: P
Fidelity: stronger: no EC; the disagreement bound on `(0, ε₀)` only
Hyps: (a) all -/
theorem graded_fr11 [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K} (hAF : AlmostFair B)
    (h : FRecPR obs actEv B) {C : Proc ι acts K} {D ε₀ : K} (hD : 0 ≤ D) (hε₀ : 0 < ε₀)
    (hFV : ∀ ε, ∀ (h0 : 0 < ε) (h1 : ε ≤ 1), ε < ε₀ → FiberValueBound (tremble C ε h0.le h1) B D)
    (hC : EventTrembleEdtConsistent obs actEv C B) :
    ∀ C' : Proc ι acts K, value C' B ≤ value C B + 2 * (decDepth B : K) * D := by
  intro C'
  have := value_le_value_add_of_pointwise C hD B
    (fun q d c hc a ha b => h.value_le_value_add_of_eventTremble hAF hε₀ hFV hC q c hc a ha b) C'
  linarith [this]

/-- **FR-11 on GR-11's corner** (`D = 0`): on a value-fair, almost-fair, `FRec`, pruned, realized
tree, event-tremble-EDT-consistency implies optimality — a strictly weaker hypothesis than
Theorem 3's (`cornerTree` is in the corner and not strongly fair, `Corner.lean`).
Source: `grounding.md` GR-10 ("at `D_V = 0` this is FR-11 under value-fairness"), GR-11
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem corner_eventTrembleEdt_isOptimal [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : Corner obs actEv B) {C : Proc ι acts K}
    (hC : EventTrembleEdtConsistent obs actEv C B) : IsOptimal C B := by
  intro C'
  have hFV : ∀ ε, ∀ (h0 : 0 < ε) (h1 : ε ≤ 1), ε < 1 →
      FiberValueBound (tremble C ε h0.le h1) B 0 := fun ε h0 h1 _ =>
    (valueFair_iff_fiberValueBound_zero h.almostFair).mp h.valueFair _
  have := graded_fr11 h.almostFair h.frecPR le_rfl one_pos hFV hC C'
  simpa using this

end theorem9

end Cleanroom.Decision.DpEdtUdtFair

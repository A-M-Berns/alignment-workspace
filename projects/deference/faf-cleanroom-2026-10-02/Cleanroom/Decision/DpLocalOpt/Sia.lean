import Cleanroom.Found.DpCoreTree

/-!
# `dp-local-opt`: Theorem 1's functional and the local-optimality predicates

Package `dp-local-opt` (area `decision`), over `dp-core-tree`'s definitions of record. This
file defines Theorem 1's fiber functional `siaSum C B d a` (`= ∑_{q : d_q = d} R_q(C) G_q(C, a)`,
the single-instance-forced payoff mass summed over the fiber of `d`, without normalisation, as
v2 §8 writes it), proves the bridge to `dp-core-tree`'s `forcedBelow`, the identity
`∑_{q : d_q = d} R_q = 𝔼[#_d]`, and defines the predicates the package compares: `Thm1At` /
`Thm1` (Theorem 1's support condition), `CoherentAt` / `Coherent` (Definition 22 of record,
mixed deviations, amendment A30), `CoherentPureAt` / `CoherentPure` (v2 line 279 as written),
and `IsOptimal` (Definition 21).

Conventions: `Definition 6` semantics (independent redraws) throughout unless a name carries a
prime; scalars are `dp-core-tree`'s linearly ordered field `K`
(`Fidelity: variant: payoffs in a linearly ordered field`).
-/

namespace Cleanroom.Decision.DpLocalOpt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)]

/-! ### Node equations for `value` -/

section valueEqns

variable (C : Proc ι acts K)

/-- `V_B` at a leaf is its payoff.
Source: none: infrastructure
Kind: L -/
@[simp] theorem value_leaf (ω : Ω) (r : K) : value C (leaf ω r : Tree Ω ι acts K) = r := by
  show ∑ _ℓ : Unit, (1 : K) * r = r
  simp

/-- `V_B` at a chance node is the `β`-average of the children's values.
Source: none: infrastructure
Kind: L -/
theorem value_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K) :
    value C (chance n β child) = ∑ i, β.w i * value C (child i) := by
  unfold value
  rw [sum_leaves_chance]
  simp only [leafLaw_chance, payoff_chance, Finset.mul_sum, mul_assoc]

/-- `V_B` at a decision node carrying `d` is the `C(d)`-average of the children's values.
Source: none: infrastructure
Kind: L -/
theorem value_decision (d : ι) (child : acts d → Tree Ω ι acts K) :
    value C (decision d child) = ∑ a, (C d).w a * value C (child a) := by
  unfold value
  rw [sum_leaves_decision]
  simp only [leafLaw_decision, payoff_decision, Finset.mul_sum, mul_assoc]

end valueEqns

/-! ### Node equations for `forcedBelow` -/

section forcedEqns

/-- The edge at a chance node's descendant, read on a leaf under the same child.
Source: none: infrastructure
Kind: L -/
theorem edgeOf_chance_same [∀ d, DecidableEq (acts d)] {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) (i : Fin n) (q : (child i).DecNode) (ℓ : (child i).Leaves) :
    edgeOf (chance n β child) ⟨i, q⟩ ⟨i, ℓ⟩ = edgeOf (child i) q ℓ := by
  rw [edgeOf_chance, dif_pos rfl]

/-- The edge at a decision node's descendant, read on a leaf under the same child.
Source: none: infrastructure
Kind: L -/
theorem edgeOf_decision_some_same [∀ d, DecidableEq (acts d)] (d : ι)
    (child : acts d → Tree Ω ι acts K) (b : acts d) (q : (child b).DecNode) (ℓ : (child b).Leaves) :
    edgeOf (decision d child) (some ⟨b, q⟩) ⟨b, ℓ⟩ = edgeOf (child b) q ℓ := by
  rw [edgeOf_decision_some, dif_pos rfl]

/-- `forcedBelow` at a chance node's child.
Source: none: infrastructure
Kind: L -/
theorem forcedBelow_chance [∀ d, DecidableEq (acts d)] {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) (p : NodePolicy (chance n β child)) (i : Fin n)
    (q : (child i).DecNode) (a : acts (pt (child i) q)) :
    forcedBelow (chance n β child) p ⟨i, q⟩ a =
      β.w i * forcedBelow (child i) (p.restrictChance i) q a := by
  unfold forcedBelow leavesBelow
  rw [Finset.sum_filter, Finset.sum_filter, sum_leaves_chance, Finset.sum_eq_single i]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp only [edgeOf_chance_same, leafLawNode_chance, payoff_chance,
      NodePolicy.update_restrictChance_same, mul_ite, mul_zero, mul_assoc]
    rfl
  · intro j _ hj
    apply Finset.sum_eq_zero
    intro ℓ _
    simp [edgeOf_chance, hj]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- `forcedBelow` at a decision node itself: forcing `a` there is the `a`-child's value under
the restricted policy.
Source: none: infrastructure
Kind: L -/
theorem forcedBelow_decision_none [∀ d, DecidableEq (acts d)] (d : ι)
    (child : acts d → Tree Ω ι acts K) (p : NodePolicy (decision d child)) (a : acts d) :
    forcedBelow (decision d child) p none a = valueNode (child a) (p.restrictDecision a) := by
  unfold forcedBelow leavesBelow valueNode
  rw [Finset.sum_filter, sum_leaves_decision, Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp only [edgeOf_decision_none, if_true, leafLawNode_decision,
      NodePolicy.update_self, FinDistr.pure_w, NodePolicy.update_none_restrictDecision,
      payoff_decision]
    simp
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro ℓ _
    simp [edgeOf_decision_none, leafLawNode_decision, NodePolicy.update_self, FinDistr.pure_w, hb]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- `forcedBelow` at a decision node's descendant: the edge weight times the child's.
Source: none: infrastructure
Kind: L -/
theorem forcedBelow_decision_some [∀ d, DecidableEq (acts d)] (d : ι)
    (child : acts d → Tree Ω ι acts K) (p : NodePolicy (decision d child)) (b : acts d)
    (q : (child b).DecNode) (a : acts (pt (child b) q)) :
    forcedBelow (decision d child) p (some ⟨b, q⟩) a =
      (p none).w b * forcedBelow (child b) (p.restrictDecision b) q a := by
  unfold forcedBelow leavesBelow
  rw [Finset.sum_filter, Finset.sum_filter, sum_leaves_decision, Finset.sum_eq_single b]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp only [edgeOf_decision_some_same, leafLawNode_decision, payoff_decision,
      NodePolicy.update_some_none, NodePolicy.update_some_restrictDecision_same, mul_ite, mul_zero,
      mul_assoc]
    rfl
  · intro c _ hc
    apply Finset.sum_eq_zero
    intro ℓ _
    simp [edgeOf_decision_some, hc]
  · intro h; exact absurd (Finset.mem_univ b) h

end forcedEqns

/-! ### Theorem 1's functional -/

section sia

variable [DecidableEq ι]

/-- **Theorem 1's fiber functional** `Φ_d(C, a) := ∑_{q : d_q = d} R_q(C) · G_q(C, a)`, by
structural recursion: the payoff mass obtained by forcing `a` at one `d`-node while every other
node (including the other `d`-nodes) draws from `C`, summed over the `d`-nodes weighted by their
reach. `leaf ↦ 0`; `chance β child ↦ ∑_i β_i Φ(child i)`; `decision d' child ↦
∑_b C(d')(b) Φ(child b) + [d' = d] V_{child a}(C)`. Unnormalised, as v2's SIA is (the bridge
`siaSum_eq_sum_fiber_forcedBelow` identifies it with `∑_q forcedBelow`; the normaliser
`∑_q R_q = 𝔼[#_d]` is `sum_reach_fiber_eq_expCount`).
Source: [[decision-problems-v2]] §8 Theorem 1 (line 266, `∑_{q : d_q = d} R_q(C) G_q(C, a)`)
Kind: D
Fidelity: exact (unnormalised fiber sum; `R_q G_q` rendered as `forcedBelow`, no division) -/
def siaSum (C : Proc ι acts K) : (B : Tree Ω ι acts K) → (d : ι) → acts d → K
  | leaf _ _, _, _ => 0
  | chance _ β child, d, a => ∑ i, β.w i * siaSum C (child i) d a
  | decision d' child, d, a =>
      (∑ b, (C d').w b * siaSum C (child b) d a) +
        (if h : d' = d then value C (child (h ▸ a)) else 0)

variable (C : Proc ι acts K)

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem siaSum_leaf (ω : Ω) (r : K) (d : ι) (a : acts d) :
    siaSum C (leaf ω r : Tree Ω ι acts K) d a = 0 := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem siaSum_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K)
    (d : ι) (a : acts d) :
    siaSum C (chance n β child) d a = ∑ i, β.w i * siaSum C (child i) d a := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem siaSum_decision (d' : ι) (child : acts d' → Tree Ω ι acts K) (d : ι) (a : acts d) :
    siaSum C (decision d' child) d a =
      (∑ b, (C d').w b * siaSum C (child b) d a) +
        (if h : d' = d then value C (child (h ▸ a)) else 0) := rfl

/-- At a `d`-node the functional adds the forced-instance value `V_{child a}(C)`.
Source: none: infrastructure
Kind: L -/
@[simp] theorem siaSum_decision_self (d : ι) (child : acts d → Tree Ω ι acts K) (a : acts d) :
    siaSum C (decision d child) d a =
      (∑ b, (C d).w b * siaSum C (child b) d a) + value C (child a) := by
  rw [siaSum_decision, dif_pos rfl]

/-- At a node carrying another point the functional is the `C`-average of the children's.
Source: none: infrastructure
Kind: L -/
theorem siaSum_decision_ne {d' d : ι} (h : d' ≠ d) (child : acts d' → Tree Ω ι acts K)
    (a : acts d) :
    siaSum C (decision d' child) d a = ∑ b, (C d').w b * siaSum C (child b) d a := by
  rw [siaSum_decision, dif_neg h, add_zero]

/-! ### The bridge to `forcedBelow` -/

/-- **The bridge**: `Φ_d(C, a) = ∑_{q : d_q = d} forcedBelow B (ofProc C B) q a`, the sum over
the fiber of the forced-below payoff masses (`= ∑_q R_q(C) G_q(C, a)` where `R_q ≠ 0`, by
`forcedBelow_eq_reach_mul_gNode`). The fiber membership is carried as a `dite` so that `a` can
be transported along `pt B q = d` without a subtype sum.
Source: [[decision-problems-v2]] §8 Theorem 1 (line 266); mandate representation decision 2
Kind: P (a structural induction through three `forcedBelow` node equations; regraded from L in
repair round 1, docstring aligned in round 2)
Fidelity: exact -/
theorem siaSum_eq_sum_fiber_forcedBelow [∀ d, DecidableEq (acts d)] (d : ι) :
    (B : Tree Ω ι acts K) → ∀ a : acts d, siaSum C B d a =
      ∑ q : B.DecNode, if h : pt B q = d then forcedBelow B (NodePolicy.ofProc C B) q (h ▸ a)
        else 0
  | leaf _ _, a => by
      simp only [siaSum_leaf]
      symm
      exact Finset.sum_eq_zero fun q _ => q.elim
  | chance _ β child, a => by
      rw [siaSum_chance, sum_decNode_chance]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [siaSum_eq_sum_fiber_forcedBelow d (child i) a, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [pt_chance]
      split_ifs with h
      · rw [forcedBelow_chance, NodePolicy.ofProc_restrictChance]
      · ring
  | decision d' child, a => by
      rw [siaSum_decision, sum_decNode_decision]
      rw [add_comm]
      congr 1
      · simp only [pt_decision_none]
        split_ifs with h
        · subst h
          rw [forcedBelow_decision_none, NodePolicy.ofProc_restrictDecision, valueNode_ofProc]
        · rfl
      · refine Finset.sum_congr rfl fun b _ => ?_
        rw [siaSum_eq_sum_fiber_forcedBelow d (child b) a, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        simp only [pt_decision_some]
        split_ifs with h
        · rw [forcedBelow_decision_some, NodePolicy.ofProc_restrictDecision, NodePolicy.ofProc_none]
        · ring

/-- **`∑_{q : d_q = d} R_q(C) = 𝔼_μ[#_d]`**: the SIA normaliser is the expected occurrence count.
Source: [[decision-problems-v2]] §8 (after Theorem 1: "Since `∑_{q : d_q = d} R_q = 𝔼_μ[#_d]`")
Kind: P
Fidelity: exact -/
theorem sum_reach_fiber_eq_expCount [∀ d, DecidableEq (acts d)] (B : Tree Ω ι acts K) (d : ι) :
    ∑ q ∈ fiber B d, reach C B q = expCount C B d := by
  unfold expCount
  simp only [reach_eq_mass_leavesBelow, leavesBelow, mass_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [count_eq_card_dNodesOn, dNodesOn_eq_filter_fiber, Finset.card_eq_sum_ones, Finset.sum_filter,
    Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs <;> simp

end sia

/-! ### The predicates -/

section predicates

variable [DecidableEq ι] (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- **Theorem 1's condition at `d`**: every action in the support of `C(d)` maximises
`Φ_d(C, ·) = ∑_{q : d_q = d} R_q(C) G_q(C, ·)` (`supp C(d) ⊆ argmax`, spelled out). Vacuous where
`Φ_d(C, ·)` is constant, in particular at `μ(occ(d)) = 0` (every `siaSum` is `0`: T7).
Source: [[decision-problems-v2]] §8 Theorem 1 (line 266)
Kind: D
Fidelity: exact (unnormalised; `Thm1At_iff_normalised` shows normalising by `𝔼[#_d] > 0`
changes nothing) -/
def Thm1At (d : ι) : Prop :=
  ∀ a, 0 < (C d).w a → ∀ b, siaSum C B d b ≤ siaSum C B d a

/-- **Theorem 1's condition** (CDT+SIA ratifiability) at every queried point.
Source: [[decision-problems-v2]] §8 Theorem 1 (line 266)
Kind: D
Fidelity: exact -/
def Thm1 : Prop := ∀ d ∈ queried B, Thm1At C B d

/-- **Definition 22 of record, at `d`, mixed form (A30)**: no point-deviation
`C[d ↦ m]`, `m ∈ Δ(A_d)`, improves `V_B`. Vacuous at `μ(occ(d)) = 0` (T7).
Source: [[decision-problems-v2]] §8 Definition 22 (line 279) as amended by
`cf-workflow/phase2-notes/final/v2-amendments.md` A30
Kind: D
Fidelity: exact (A30's text) -/
def CoherentAt (d : ι) : Prop :=
  ∀ m : FinDistr K (acts d), value (C.deviate d m) B ≤ value C B

/-- **Definition 22 of record (mixed)**: `B`-coherence at every queried point.
Source: [[decision-problems-v2]] §8 Definition 22 (line 279), A30
Kind: D
Fidelity: exact -/
def Coherent : Prop := ∀ d ∈ queried B, CoherentAt C B d

/-- **Definition 22 as v2 prints it, at `d` (pure deviations only)**: `V_B(C[d ↦ a]) ≤ V_B(C)`
for every `a ∈ A_d`. Strictly weaker than `CoherentAt` under self-succession (T3(a)).
Source: [[decision-problems-v2]] §8 Definition 22 (line 279)
Kind: D
Fidelity: exact (v2 as written; superseded by A30) -/
def CoherentPureAt [∀ d, DecidableEq (acts d)] (d : ι) : Prop :=
  ∀ a, value (C.deviatePure d a) B ≤ value C B

/-- **Definition 22 as v2 prints it** (pure deviations), at every queried point.
Source: [[decision-problems-v2]] §8 Definition 22 (line 279)
Kind: D
Fidelity: exact (v2 as written; superseded by A30) -/
def CoherentPure [∀ d, DecidableEq (acts d)] : Prop := ∀ d ∈ queried B, CoherentPureAt C B d

/-- **Optimality on `B`** (Definition 21): `V_B(C) ≥ V_B(C')` for every procedure `C'`.
Source: [[decision-problems-v2]] §6 Definition 21 (line 201)
Kind: D
Fidelity: exact (`= max` rendered as `≥` every competitor; existence of the max is T5) -/
def IsOptimal : Prop := ∀ C' : Proc ι acts K, value C' B ≤ value C B

/-- Mixed coherence implies pure coherence (`δ_a` is a mixed action).
Source: A30 ("Quantifying over pure `a` only is strictly weaker")
Kind: L -/
theorem CoherentAt.pure [∀ d, DecidableEq (acts d)] {d : ι} (h : CoherentAt C B d) :
    CoherentPureAt C B d := fun a => h (FinDistr.pure a)

/-- Mixed coherence implies pure coherence, at every queried point.
Source: A30
Kind: L -/
theorem Coherent.pure [∀ d, DecidableEq (acts d)] (h : Coherent C B) : CoherentPure C B :=
  fun d hd => CoherentAt.pure C B (h d hd)

/-- Optimality implies mixed coherence at every point (a point-deviation is a procedure).
Source: [[decision-problems-v2]] §8 Theorem 2 proof ("the global maximum survives every
point-deviation")
Kind: L -/
theorem IsOptimal.coherentAt (h : IsOptimal C B) (d : ι) : CoherentAt C B d :=
  fun m => h (C.deviate d m)

/-- Optimality implies mixed coherence.
Source: [[decision-problems-v2]] §8 Theorem 2 proof
Kind: L -/
theorem IsOptimal.coherent (h : IsOptimal C B) : Coherent C B :=
  fun d _ => IsOptimal.coherentAt C B h d

/-- Normalising Theorem 1's functional by a positive constant (v2's `𝔼[#_d]`) leaves the support
condition unchanged.
Source: [[decision-problems-v2]] §8 (after Theorem 1: the weights `R_q / 𝔼_μ[#_d]`)
Kind: L -/
theorem Thm1At_iff_normalised (d : ι) {N : K} (hN : 0 < N) :
    Thm1At C B d ↔ ∀ a, 0 < (C d).w a → ∀ b, siaSum C B d b / N ≤ siaSum C B d a / N := by
  unfold Thm1At
  constructor
  · intro h a ha b
    exact div_le_div_of_nonneg_right (h a ha b) hN.le
  · intro h a ha b
    exact (div_le_div_iff_of_pos_right hN).mp (h a ha b)

end predicates

end Cleanroom.Decision.DpLocalOpt

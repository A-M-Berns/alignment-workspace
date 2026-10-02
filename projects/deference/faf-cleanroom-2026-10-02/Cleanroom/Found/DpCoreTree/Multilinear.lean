import Cleanroom.Found.DpCoreTree.Seed

/-!
# Multilinearity of the value in the node-level distributions

T7(i)–(iii) of [[dp-core-tree-mandate]] (the interpolation half, T7(iv), is in `Seed.lean`).
With one distribution `p_q` per decision node (`NodePolicy`), the value `V_B(p)` is affine in
each `p_q` because every node lies on a path at most once:

* the **master identity** `valueNode_update_eq`: `V_B(p[q ↦ m]) = ∑_a m(a) · Φ_q(p, a) + Ψ_q(p)`,
  where `Φ_q(p, a) = forcedBelow B p q a` (the payoff mass below `q` forcing `a` at `q` only,
  `= R_q · G_q(a)`) and `Ψ_q(p)` is the payoff mass off `q`, neither depending on `p_q`;
* (i) `valueNode_affine`: `V_B(p) = ∑_a p_q(a) · V_B(p[q ↦ δ_a])`;
* (ii) `valueNode_update_sub`: `V_B(p[q ↦ p']) − V_B(p) = ∑_a (p'(a) − p_q(a)) · Φ_q(p, a)`,
  with `forcedBelow_update_self` and `reachNode_update_self` (`Φ_q`, `R_q` free of `p_q`);
* (iii) `leafLawNode_ofProc` / `valueNode_ofProc` / `reachNode_ofProc`: tying `p_q := C(d_q)`
  recovers `μ_{B,C}`, `V_B(C)`, `R_q(C)`.

The chain rule over the fiber of `d` (Theorem 1) is `dp-local-opt`'s.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Found.DpCoreTree

open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]

namespace Tree

/-! ### Equation lemmas -/

section eqns

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem leafLawNode_leaf (ω : Ω) (r : K) (p : NodePolicy (leaf ω r : Tree Ω ι acts K))
    (ℓ : (leaf ω r : Tree Ω ι acts K).Leaves) : leafLawNode (leaf ω r) p ℓ = 1 := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem leafLawNode_chance {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) (p : NodePolicy (chance n β child)) (i : Fin n)
    (ℓ : (child i).Leaves) :
    leafLawNode (chance n β child) p ⟨i, ℓ⟩ =
      β.w i * leafLawNode (child i) (p.restrictChance i) ℓ := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem leafLawNode_decision (d : ι) (child : acts d → Tree Ω ι acts K)
    (p : NodePolicy (decision d child)) (a : acts d) (ℓ : (child a).Leaves) :
    leafLawNode (decision d child) p ⟨a, ℓ⟩ =
      (p none).w a * leafLawNode (child a) (p.restrictDecision a) ℓ := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem reachNode_chance {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) (p : NodePolicy (chance n β child)) (i : Fin n)
    (q : (child i).DecNode) :
    reachNode (chance n β child) p ⟨i, q⟩ = β.w i * reachNode (child i) (p.restrictChance i) q :=
  rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem reachNode_decision_none (d : ι) (child : acts d → Tree Ω ι acts K)
    (p : NodePolicy (decision d child)) : reachNode (decision d child) p none = 1 := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem reachNode_decision_some (d : ι) (child : acts d → Tree Ω ι acts K)
    (p : NodePolicy (decision d child)) (a : acts d) (q : (child a).DecNode) :
    reachNode (decision d child) p (some ⟨a, q⟩) =
      (p none).w a * reachNode (child a) (p.restrictDecision a) q := rfl

/-- Plumbing. Source: none: infrastructure. Kind: L -/
theorem NodePolicy.ofProc_restrictChance (C : Proc ι acts K) {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) (i : Fin n) :
    (NodePolicy.ofProc C (chance n β child)).restrictChance i = NodePolicy.ofProc C (child i) :=
  rfl

/-- Plumbing. Source: none: infrastructure. Kind: L -/
theorem NodePolicy.ofProc_restrictDecision (C : Proc ι acts K) (d : ι)
    (child : acts d → Tree Ω ι acts K) (a : acts d) :
    (NodePolicy.ofProc C (decision d child)).restrictDecision a = NodePolicy.ofProc C (child a) :=
  rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem NodePolicy.ofProc_none (C : Proc ι acts K) (d : ι) (child : acts d → Tree Ω ι acts K) :
    NodePolicy.ofProc C (decision d child) none = C d := rfl

end eqns

/-! ### (iii) Tying the node-level policy to a procedure -/

section tying

variable (C : Proc ι acts K)

/-- Tying `p_q := C(d_q)` recovers the run law of Definition 6.
Source: [[decision-problems-v2]] §8 Theorem 1 proof ("Tying `p_q := C(d_q)`")
Kind: P -/
theorem leafLawNode_ofProc :
    (B : Tree Ω ι acts K) → ∀ ℓ, leafLawNode B (NodePolicy.ofProc C B) ℓ = leafLaw C B ℓ
  | leaf _ _, _ => rfl
  | chance _ β child, ⟨i, ℓ⟩ => by
      rw [leafLawNode_chance, leafLaw_chance, NodePolicy.ofProc_restrictChance,
        leafLawNode_ofProc (child i) ℓ]
  | decision d child, ⟨a, ℓ⟩ => by
      rw [leafLawNode_decision, leafLaw_decision, NodePolicy.ofProc_restrictDecision,
        NodePolicy.ofProc_none, leafLawNode_ofProc (child a) ℓ]

/-- Tying recovers `V_B(C)`.
Source: [[decision-problems-v2]] §8 Theorem 1 proof
Kind: L -/
theorem valueNode_ofProc (B : Tree Ω ι acts K) :
    valueNode B (NodePolicy.ofProc C B) = value C B :=
  Finset.sum_congr rfl fun ℓ _ => by rw [leafLawNode_ofProc]

/-- Tying recovers `R_q(C)`.
Source: [[decision-problems-v2]] §8 Theorem 1 proof
Kind: L -/
theorem reachNode_ofProc :
    (B : Tree Ω ι acts K) → ∀ q, reachNode B (NodePolicy.ofProc C B) q = reach C B q
  | leaf _ _, q => q.elim
  | chance _ β child, ⟨i, q⟩ => by
      rw [reachNode_chance, reach_chance, NodePolicy.ofProc_restrictChance,
        reachNode_ofProc (child i) q]
  | decision d child, none => rfl
  | decision d child, some ⟨a, q⟩ => by
      rw [reachNode_decision_some, reach_decision_some, NodePolicy.ofProc_restrictDecision,
        NodePolicy.ofProc_none, reachNode_ofProc (child a) q]

end tying

/-! ### Single-node updates and restriction -/

section update

variable {B : Tree Ω ι acts K}

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem NodePolicy.update_self (p : NodePolicy B) (q : B.DecNode)
    (m : FinDistr K (acts (pt B q))) : p.update q m q = m := by
  unfold NodePolicy.update; exact Function.update_self q m p

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem NodePolicy.update_of_ne (p : NodePolicy B) {q q' : B.DecNode} (h : q' ≠ q)
    (m : FinDistr K (acts (pt B q))) : p.update q m q' = p q' := by
  unfold NodePolicy.update; exact Function.update_of_ne h m p

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem NodePolicy.update_idem (p : NodePolicy B) (q : B.DecNode)
    (m m' : FinDistr K (acts (pt B q))) : (p.update q m).update q m' = p.update q m' := by
  unfold NodePolicy.update; simp

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem NodePolicy.update_eq_self (p : NodePolicy B) (q : B.DecNode) : p.update q (p q) = p := by
  unfold NodePolicy.update; simp

end update

section restrict

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem NodePolicy.update_restrictChance_same {n : ℕ} {β : FinDistr K (Fin n)}
    {child : Fin n → Tree Ω ι acts K} (p : NodePolicy (chance n β child)) (i : Fin n)
    (q : (child i).DecNode) (m : FinDistr K (acts (pt (child i) q))) :
    (p.update ⟨i, q⟩ m).restrictChance i = (p.restrictChance i).update q m := by
  funext q'
  simp only [NodePolicy.restrictChance, NodePolicy.update]
  by_cases h : q' = q
  · subst h; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne h, Function.update_of_ne]
    · rfl
    · intro heq; exact h (eq_of_heq (Sigma.mk.inj_iff.mp heq).2)

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem NodePolicy.update_restrictChance_ne {n : ℕ} {β : FinDistr K (Fin n)}
    {child : Fin n → Tree Ω ι acts K} (p : NodePolicy (chance n β child)) {i j : Fin n}
    (hij : j ≠ i) (q : (child i).DecNode) (m : FinDistr K (acts (pt (child i) q))) :
    (p.update ⟨i, q⟩ m).restrictChance j = p.restrictChance j := by
  funext q'
  simp only [NodePolicy.restrictChance, NodePolicy.update]
  rw [Function.update_of_ne]
  intro heq; exact hij (Sigma.mk.inj_iff.mp heq).1

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem NodePolicy.update_none_restrictDecision {d : ι} {child : acts d → Tree Ω ι acts K}
    (p : NodePolicy (decision d child)) (m : FinDistr K (acts d)) (a : acts d) :
    (p.update none m).restrictDecision a = p.restrictDecision a := by
  funext q'
  simp only [NodePolicy.restrictDecision, NodePolicy.update]
  rw [Function.update_of_ne]
  exact Option.some_ne_none _

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem NodePolicy.update_some_none {d : ι} {child : acts d → Tree Ω ι acts K}
    (p : NodePolicy (decision d child)) (a : acts d) (q : (child a).DecNode)
    (m : FinDistr K (acts (pt (child a) q))) :
    (p.update (some ⟨a, q⟩) m) none = p none := by
  simp only [NodePolicy.update]
  rw [Function.update_of_ne]
  exact (Option.some_ne_none _).symm

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem NodePolicy.update_some_restrictDecision_same {d : ι} {child : acts d → Tree Ω ι acts K}
    (p : NodePolicy (decision d child)) (a : acts d) (q : (child a).DecNode)
    (m : FinDistr K (acts (pt (child a) q))) :
    (p.update (some ⟨a, q⟩) m).restrictDecision a = (p.restrictDecision a).update q m := by
  funext q'
  simp only [NodePolicy.restrictDecision, NodePolicy.update]
  by_cases h : q' = q
  · subst h; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne h, Function.update_of_ne]
    · rfl
    · intro heq
      exact h (eq_of_heq (Sigma.mk.inj_iff.mp (Option.some_injective _ heq)).2)

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem NodePolicy.update_some_restrictDecision_ne {d : ι} {child : acts d → Tree Ω ι acts K}
    (p : NodePolicy (decision d child)) {a b : acts d} (hab : b ≠ a) (q : (child a).DecNode)
    (m : FinDistr K (acts (pt (child a) q))) :
    (p.update (some ⟨a, q⟩) m).restrictDecision b = p.restrictDecision b := by
  funext q'
  simp only [NodePolicy.restrictDecision, NodePolicy.update]
  rw [Function.update_of_ne]
  intro heq
  exact hab (Sigma.mk.inj_iff.mp (Option.some_injective _ heq)).1

end restrict

/-! ### The factorisation of the law at one node -/

section factor

/-- On a leaf below `q` taking edge `a`, the law under `p[q ↦ m]` is `m(a)` times the law under
`p[q ↦ δ_a]` (every node is on a path at most once).
Source: [[decision-problems-v2]] §8 Theorem 1 proof ("multilinear (each node occurs at most
once per path)")
Kind: P -/
theorem leafLawNode_update_of_edge :
    (B : Tree Ω ι acts K) → ∀ (p : NodePolicy B) (q : B.DecNode) (ℓ : B.Leaves)
      (m : FinDistr K (acts (pt B q))) (a : acts (pt B q)), edgeOf B q ℓ = some a →
      leafLawNode B (p.update q m) ℓ = m.w a * leafLawNode B (p.update q (FinDistr.pure a)) ℓ
  | leaf _ _, _, q, _, _, _, _ => q.elim
  | chance _ β child, p, ⟨i, q⟩, ⟨j, ℓ⟩, m, a, h => by
      by_cases hji : j = i
      · subst hji
        simp only [edgeOf_chance, dite_true] at h
        simp only [leafLawNode_chance, NodePolicy.update_restrictChance_same]
        rw [leafLawNode_update_of_edge (child j) _ q ℓ m a h, mul_left_comm]
        try rfl
      · simp [edgeOf_chance, hji] at h
  | decision d child, p, none, ⟨b, ℓ⟩, m, a, h => by
      simp only [edgeOf_decision_none] at h
      have hba : b = a := Option.some.inj h
      subst hba
      simp [NodePolicy.update_none_restrictDecision]
  | decision d child, p, some ⟨c, q⟩, ⟨b, ℓ⟩, m, a, h => by
      by_cases hbc : b = c
      · subst hbc
        simp only [edgeOf_decision_some, dite_true] at h
        simp only [leafLawNode_decision, NodePolicy.update_some_none,
          NodePolicy.update_some_restrictDecision_same]
        rw [leafLawNode_update_of_edge (child b) _ q ℓ m a h, mul_left_comm]
        try rfl
      · simp [edgeOf_decision_some, hbc] at h

/-- On a leaf not below `q`, updating `p` at `q` does not change the law.
Source: [[decision-problems-v2]] §8 Theorem 1 proof
Kind: L -/
theorem leafLawNode_update_of_not_edge :
    (B : Tree Ω ι acts K) → ∀ (p : NodePolicy B) (q : B.DecNode) (ℓ : B.Leaves)
      (m : FinDistr K (acts (pt B q))), edgeOf B q ℓ = none →
      leafLawNode B (p.update q m) ℓ = leafLawNode B p ℓ
  | leaf _ _, _, q, _, _, _ => q.elim
  | chance _ β child, p, ⟨i, q⟩, ⟨j, ℓ⟩, m, h => by
      by_cases hji : j = i
      · subst hji
        simp only [edgeOf_chance, dite_true] at h
        simp only [leafLawNode_chance, NodePolicy.update_restrictChance_same]
        rw [leafLawNode_update_of_not_edge (child j) _ q ℓ m h]
      · simp only [leafLawNode_chance, NodePolicy.update_restrictChance_ne p hji]
  | decision d child, p, none, ⟨b, ℓ⟩, m, h => by
      simp at h
  | decision d child, p, some ⟨c, q⟩, ⟨b, ℓ⟩, m, h => by
      by_cases hbc : b = c
      · subst hbc
        simp only [edgeOf_decision_some, dite_true] at h
        simp only [leafLawNode_decision, NodePolicy.update_some_none,
          NodePolicy.update_some_restrictDecision_same]
        rw [leafLawNode_update_of_not_edge (child b) _ q ℓ m h]
      · simp only [leafLawNode_decision, NodePolicy.update_some_none,
          NodePolicy.update_some_restrictDecision_ne p hbc]

/-- `R_q` does not depend on `p_q`.
Source: [[decision-problems-v2]] §8 Theorem 1 proof ("`R_q` free of `p_q`")
Kind: L -/
theorem reachNode_update_self :
    (B : Tree Ω ι acts K) → ∀ (p : NodePolicy B) (q : B.DecNode) (m : FinDistr K (acts (pt B q))),
      reachNode B (p.update q m) q = reachNode B p q
  | leaf _ _, _, q, _ => q.elim
  | chance _ β child, p, ⟨i, q⟩, m => by
      simp only [reachNode_chance, NodePolicy.update_restrictChance_same,
        reachNode_update_self (child i) _ q m]
  | decision d child, p, none, m => rfl
  | decision d child, p, some ⟨a, q⟩, m => by
      simp only [reachNode_decision_some, NodePolicy.update_some_none,
        NodePolicy.update_some_restrictDecision_same, reachNode_update_self (child a) _ q m]

/-- `Φ_q(p, a) = forcedBelow` does not depend on `p_q`.
Source: [[decision-problems-v2]] §8 Theorem 1 proof
Kind: L -/
theorem forcedBelow_update_self (B : Tree Ω ι acts K) (p : NodePolicy B) (q : B.DecNode)
    (m : FinDistr K (acts (pt B q))) (a : acts (pt B q)) :
    forcedBelow B (p.update q m) q a = forcedBelow B p q a := by
  unfold forcedBelow
  rw [NodePolicy.update_idem]

end factor

/-! ### The master identity and its two corollaries -/

section master

variable (B : Tree Ω ι acts K) (p : NodePolicy B) (q : B.DecNode)

/-- The payoff mass off `q` (leaves not below `q`).
Source: none: infrastructure
Kind: D -/
def offMass : K :=
  ∑ ℓ ∈ Finset.univ.filter (fun ℓ => ¬ (edgeOf B q ℓ).isSome), leafLawNode B p ℓ * payoff B ℓ

/-- **Master identity**: `V_B(p[q ↦ m]) = ∑_a m(a) · Φ_q(p, a) + Ψ_q(p)`, where `Φ_q(p, a) =
forcedBelow B p q a` and `Ψ_q(p) = offMass B p q`; neither depends on `p_q`.
Source: [[decision-problems-v2]] §8 Theorem 1 proof ("multilinear … with
`∂V/∂p_q(a) = R_q · G_q(a)` and `R_q` free of `p_q`")
Kind: P
Fidelity: exact -/
theorem valueNode_update_eq (m : FinDistr K (acts (pt B q))) :
    valueNode B (p.update q m) = (∑ a, m.w a * forcedBelow B p q a) + offMass B p q := by
  unfold valueNode offMass forcedBelow leavesBelow
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ℓ => (edgeOf B q ℓ).isSome)]
  congr 1
  · simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_exists] at hℓ
    obtain ⟨a₀, ha₀⟩ := hℓ
    rw [leafLawNode_update_of_edge B p q ℓ m a₀ ha₀]
    rw [Finset.sum_eq_single a₀]
    · rw [leafLawNode_update_of_edge B p q ℓ (FinDistr.pure a₀) a₀ ha₀]
      simp only [FinDistr.pure_w, if_true, one_mul]
      ring
    · intro b _ hb
      rw [leafLawNode_update_of_edge B p q ℓ (FinDistr.pure b) a₀ ha₀]
      simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ a₀) h
  · refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true,
      Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hℓ
    rw [leafLawNode_update_of_not_edge B p q ℓ m hℓ]

/-- **(i) Affinity in each node's distribution**: `V_B(p) = ∑_a p_q(a) · V_B(p[q ↦ δ_a])`.
Source: [[decision-problems-v2]] §8 Theorem 1 proof; mandate T7(i)
Kind: P
Fidelity: exact
Hyps: none -/
theorem valueNode_affine :
    valueNode B p = ∑ a, (p q).w a * valueNode B (p.update q (FinDistr.pure a)) := by
  have h1 := valueNode_update_eq B p q (p q)
  rw [NodePolicy.update_eq_self] at h1
  rw [h1]
  have h2 : ∀ a, valueNode B (p.update q (FinDistr.pure a)) =
      forcedBelow B p q a + offMass B p q := by
    intro a
    rw [valueNode_update_eq B p q (FinDistr.pure a)]
    congr 1
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [FinDistr.pure_w, hb]
    · intro h; exact absurd (Finset.mem_univ a) h
  simp only [h2, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, (p q).sum_one, one_mul]

/-- **(ii) The partial-derivative form**:
`V_B(p[q ↦ p']) − V_B(p) = ∑_a (p'(a) − p_q(a)) · Φ_q(p, a)`, where `Φ_q(p, a) = forcedBelow`
(`= R_q · G_q(a)`) does not depend on `p_q`.
Source: [[decision-problems-v2]] §8 Theorem 1 proof (`∂V/∂p_q(a) = R_q · G_q(a)`); mandate T7(ii)
Kind: P
Fidelity: exact (finite-difference form of the derivative; `Φ_q = R_q · G_q` by
`forcedBelow_eq_reach_mul_gNode` when `R_q ≠ 0`)
Hyps: none -/
theorem valueNode_update_sub (p' : FinDistr K (acts (pt B q))) :
    valueNode B (p.update q p') - valueNode B p =
      ∑ a, (p'.w a - (p q).w a) * forcedBelow B p q a := by
  have h1 := valueNode_update_eq B p q (p q)
  rw [NodePolicy.update_eq_self] at h1
  rw [valueNode_update_eq B p q p', h1]
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

/-- `Φ_q(p, a) = R_q(p) · G_q(p, a)` when `R_q(p) ≠ 0`.
Source: [[decision-problems-v2]] §8 (`∂V/∂p_q(a) = R_q · G_q(a)`)
Kind: L -/
theorem forcedBelow_eq_reach_mul_gNode (a : acts (pt B q)) (h : reachNode B p q ≠ 0) :
    forcedBelow B p q a = reachNode B p q * gNode B p q a := by
  unfold gNode
  rw [mul_div_cancel₀ _ h]

end master

/-! ### Tied form: affinity in `C(d)` at a single node is *not* affinity in `C(d)` -/

/-- Tying `p_q := C(d_q)` and deviating at one node: the tied value `V_B(C)` equals the
node-level value at `ofProc C`, so (i) reads `V_B(C) = ∑_a C(d_q)(a) · V_B((ofProc C)[q ↦ δ_a])`
— a single-instance forcing, not the all-instance deviation `C[d ↦ a]`.
Source: [[decision-problems-v2]] §8 ("the two intrinsic counterfactuals of Remark 3.11:
single-instance forcing here, all-instance deviation `C[d ↦ a]` below")
Kind: C -/
theorem value_eq_sum_forced (C : Proc ι acts K) (B : Tree Ω ι acts K) (q : B.DecNode) :
    value C B = ∑ a, (C (pt B q)).w a *
      valueNode B ((NodePolicy.ofProc C B).update q (FinDistr.pure a)) := by
  rw [← valueNode_ofProc, valueNode_affine B _ q]
  rfl

end Tree

end Cleanroom.Found.DpCoreTree

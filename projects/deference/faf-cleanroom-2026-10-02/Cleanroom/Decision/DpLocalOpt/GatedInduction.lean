import Cleanroom.Decision.DpLocalOpt.StrongFair
import Cleanroom.Decision.DpLocalOpt.Coherence

/-!
# `dp-local-opt`: on a strongly fair tree every strict local maximum is global (repair round 2)

Closes the open statement of repair round 1 (`stronglyFair_strictLocalMax_isOptimal`, stated
with `sorry` in `StrongFair.lean` until this round; dp-cf-2-026's extension question in its
strongly-fair form). The proof is the induction on the
gating order sketched in findings F10, organised so that no tree surgery is needed:

* **The gated shape at a point.** On a strongly fair tree all `d`-subtrees are labelled-isomorphic
  to one reference `decision d c₀`, so Theorem 1's functional factors,
  `Φ_d(C, a) = fiberMass_d(C) · V_{c₀ a}(C)` (`siaSum_eq_fiberMass_mul_of_iso`, structural
  recursion; `fiberMass_d(C) = ∑_{q : d_q = d} R_q(C) ≥ 0`), and with the per-point affinity of
  `V` on almost-fair trees (`value_deviate_eq_sum_of_count_le_one`, strong fairness gives
  `#_d ≤ 1`) this is `V(C[d ↦ m]) = offOcc_d(C) + fiberMass_d(C) · ∑_a m(a) V_{c₀ a}(C)`
  (`value_deviate_eq_gated`).
* **Induction on the set `S` of points allowed to move.** `key`: if `C` is a strict local maximum
  then `V(C') ≤ V(C)` for every `C'` agreeing with `C` off `S`. Choose an `S`-node `q₀` whose
  subtree is smallest (`Finset.exists_min_image` on `size`); its point `d` has no `S`-point
  strictly below any `d`-node (`exists_node_lt_of_mem_queried_child` + `LabIso`), so the
  reference values `V_{c₀ a}(C')` do not depend on `C'` (`value_congr_queried`). Strictness at
  `C` in the `d`-direction alone forces `∑_a m(a) V_{c₀ a}(C) ≤ ∑_a C(d)(a) V_{c₀ a}(C)` for every
  `m` (move along `(1 − t) C(d) + t m` with `t = min ε 1`), so resetting `C'(d)` to `C(d)` does not
  lower `V` (`fiberMass ≥ 0`), and the induction hypothesis on `S ∖ {d}` finishes.

No new hypothesis: `StronglyFair` and `IsStrictLocalMax` are the definitions of record
(`dp-fairness-reloc`, `StrongFair.lean`).
-/

namespace Cleanroom.Decision.DpLocalOpt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpFairnessReloc

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [DecidableEq ι] [∀ d, DecidableEq (acts d)]

/-! ### Nodes and queried points -/

section nodes

omit [∀ d, DecidableEq (acts d)] in
/-- A queried point is carried by some node.
Source: [[decision-problems-v2]] §3.1 Definition 5 ("queried if some node carries it")
Kind: L -/
theorem exists_decNode_of_mem_queried :
    (B : Tree Ω ι acts K) → ∀ d ∈ queried B, ∃ q : B.DecNode, pt B q = d
  | leaf _ _, d, hd => by simp at hd
  | chance _ β child, d, hd => by
      simp only [queried_chance, Finset.mem_biUnion, Finset.mem_univ, true_and] at hd
      obtain ⟨i, hi⟩ := hd
      obtain ⟨q, hq⟩ := exists_decNode_of_mem_queried (child i) d hi
      exact ⟨⟨i, q⟩, hq⟩
  | decision d' child, d, hd => by
      simp only [queried_decision, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ,
        true_and] at hd
      rcases hd with rfl | ⟨a, ha⟩
      · exact ⟨none, rfl⟩
      · obtain ⟨q, hq⟩ := exists_decNode_of_mem_queried (child a) d ha
        exact ⟨some ⟨a, q⟩, hq⟩

omit [∀ d, DecidableEq (acts d)] in
/-- The point of a node is queried.
Source: [[decision-problems-v2]] §3.1 Definition 5
Kind: L -/
theorem pt_mem_queried : (B : Tree Ω ι acts K) → ∀ q : B.DecNode, pt B q ∈ queried B
  | leaf _ _, q => q.elim
  | chance _ β child, ⟨i, q⟩ => by
      simp only [queried_chance, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨i, pt_mem_queried (child i) q⟩
  | decision d' child, none => mem_queried_decision d' child
  | decision d' child, some ⟨a, q⟩ => by
      simp only [queried_decision, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ,
        true_and]
      exact Or.inr ⟨a, pt_mem_queried (child a) q⟩

omit [∀ d, Fintype (acts d)] [DecidableEq ι] [∀ d, DecidableEq (acts d)] in
/-- The subtree at `q₀` is `decision d c₀` for some `c₀`, when `d_{q₀} = d` (the point as a
variable, for `subst`).
Source: none: infrastructure
Kind: L -/
theorem subtreeAt_eq_decision' (B : Tree Ω ι acts K) (q₀ : B.DecNode) (d : ι)
    (hq₀ : pt B q₀ = d) :
    ∃ c₀ : acts d → Tree Ω ι acts K, subtreeAt B q₀ = .decision d c₀ := by
  subst hq₀
  exact subtreeAt_eq_decision B q₀

omit [∀ d, DecidableEq (acts d)] in
/-- **A point queried strictly below `q₀` is carried by a node with a smaller subtree**: if
`subtreeAt B q₀ = decision d_{q₀} c₀` and `e ∈ queried (c₀ a)`, some node of `B` carries `e` and
has a subtree of size `< size (subtreeAt B q₀)`.
Source: none: infrastructure (the minimality step of F10's induction)
Kind: P -/
theorem exists_node_lt_of_mem_queried_child :
    (B : Tree Ω ι acts K) → ∀ (q₀ : B.DecNode) (c₀ : acts (pt B q₀) → Tree Ω ι acts K),
      subtreeAt B q₀ = .decision (pt B q₀) c₀ → ∀ (a : acts (pt B q₀)) (e : ι),
      e ∈ queried (c₀ a) →
      ∃ q : B.DecNode, pt B q = e ∧ size (subtreeAt B q) < size (subtreeAt B q₀)
  | leaf _ _, q₀, _, _, _, _, _ => q₀.elim
  | chance _ β child, ⟨i, q₀⟩, c₀, hc₀, a, e, he => by
      obtain ⟨q, hq, hlt⟩ := exists_node_lt_of_mem_queried_child (child i) q₀ c₀ hc₀ a e he
      exact ⟨⟨i, q⟩, hq, hlt⟩
  | decision d' child, none, c₀, hc₀, a, e, he => by
      change Tree.decision d' child = Tree.decision d' c₀ at hc₀
      simp only [Tree.decision.injEq, heq_eq_eq, true_and] at hc₀
      subst hc₀
      obtain ⟨q, hq⟩ := exists_decNode_of_mem_queried (child a) e he
      refine ⟨some ⟨a, q⟩, hq, ?_⟩
      change size (subtreeAt (child a) q) < size (Tree.decision d' child)
      exact (size_subtreeAt_le (child a) q).trans_lt (size_child_lt_decision d' child a)
  | decision d' child, some ⟨b, q₀⟩, c₀, hc₀, a, e, he => by
      obtain ⟨q, hq, hlt⟩ := exists_node_lt_of_mem_queried_child (child b) q₀ c₀ hc₀ a e he
      exact ⟨some ⟨b, q⟩, hq, hlt⟩

/-- `exists_node_lt_of_mem_queried_child` with the point as a variable.
Source: none: infrastructure
Kind: L -/
theorem exists_node_lt_of_mem_queried_child' (B : Tree Ω ι acts K) (q₀ : B.DecNode) (d : ι)
    (hq₀ : pt B q₀ = d) (c₀ : acts d → Tree Ω ι acts K) (hc₀ : subtreeAt B q₀ = .decision d c₀)
    (a : acts d) (e : ι) (he : e ∈ queried (c₀ a)) :
    ∃ q : B.DecNode, pt B q = e ∧ size (subtreeAt B q) < size (subtreeAt B q₀) := by
  subst hq₀
  exact exists_node_lt_of_mem_queried_child B q₀ c₀ hc₀ a e he

end nodes

/-! ### The fiber mass `∑_{q : d_q = d} R_q(C)` -/

section fiberMass

variable (C : Proc ι acts K)

/-- The reach mass of the `d`-nodes, `∑_{q : d_q = d} R_q(C)` (`= 𝔼_μ[#_d]`,
`sum_reach_fiber_eq_expCount`); the gate `G` of F10's gated shape.
Source: [[decision-problems-v2]] §8 (after Theorem 1: "`∑_{q : d_q = d} R_q = 𝔼_μ[#_d]`")
Kind: D -/
def fiberMass (B : Tree Ω ι acts K) (d : ι) : K := ∑ q ∈ fiber B d, reach C B q

omit [∀ d, DecidableEq (acts d)] in
/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem fiberMass_leaf (ω : Ω) (r : K) (d : ι) :
    fiberMass C (leaf ω r : Tree Ω ι acts K) d = 0 :=
  Finset.sum_eq_zero fun q _ => q.elim

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem fiberMass_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K)
    (d : ι) :
    fiberMass C (chance n β child) d = ∑ i, β.w i * fiberMass C (child i) d := by
  unfold fiberMass
  simp only [fiber, Finset.sum_filter]
  rw [sum_decNode_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [pt_chance, reach_chance]
  split_ifs <;> simp

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem fiberMass_decision (d' : ι) (child : acts d' → Tree Ω ι acts K) (d : ι) :
    fiberMass C (decision d' child) d =
      (if d' = d then 1 else 0) + ∑ b, (C d').w b * fiberMass C (child b) d := by
  unfold fiberMass
  simp only [fiber, Finset.sum_filter]
  rw [sum_decNode_decision]
  refine congrArg₂ (· + ·) rfl ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [pt_decision_some, reach_decision_some]
  split_ifs <;> simp

/-- `0 ≤ fiberMass`.
Source: none: infrastructure
Kind: L -/
theorem fiberMass_nonneg (B : Tree Ω ι acts K) (d : ι) : 0 ≤ fiberMass C B d :=
  Finset.sum_nonneg fun q _ => reach_nonneg C B q

end fiberMass

/-! ### The gated shape at a point whose subtrees are all isomorphic -/

section gated

variable (C : Proc ι acts K)

/-- **Theorem 1's functional factors through the fiber mass when every `d`-subtree is
labelled-isomorphic to `decision d c₀`**: `Φ_d(C, a) = fiberMass_d(C) · V_{c₀ a}(C)`. By structural
recursion: at a `d`-node the forced term `V_{child a}(C)` equals `V_{c₀ a}(C)` because the node's
subtree is isomorphic to the reference (`LabIso.contLaw_eq`); everywhere else the recursion of
`siaSum` and of `fiberMass` agree.
Source: findings F10 (the gated shape: "`f` affine, all `d`-subtrees isomorphic");
`v2-amendments.md` A34 (equivalent subtrees ⟹ equal continuation laws)
Kind: P
Fidelity: exact -/
theorem siaSum_eq_fiberMass_mul_of_iso (d : ι) (c₀ : acts d → Tree Ω ι acts K) :
    (B : Tree Ω ι acts K) →
      (∀ q : B.DecNode, pt B q = d → LabIso (subtreeAt B q) (.decision d c₀)) →
      ∀ a, siaSum C B d a = fiberMass C B d * value C (c₀ a)
  | leaf _ _, _, a => by simp [fiberMass_leaf]
  | chance _ β child, hT, a => by
      have ih : ∀ i, siaSum C (child i) d a = fiberMass C (child i) d * value C (c₀ a) :=
        fun i => siaSum_eq_fiberMass_mul_of_iso d c₀ (child i) (fun q hq => hT ⟨i, q⟩ hq) a
      rw [siaSum_chance, fiberMass_chance, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [ih i, mul_assoc]
  | decision d' child, hT, a => by
      have ih : ∀ b, siaSum C (child b) d a = fiberMass C (child b) d * value C (c₀ a) :=
        fun b => siaSum_eq_fiberMass_mul_of_iso d c₀ (child b) (fun q hq => hT (some ⟨b, q⟩) hq) a
      rw [siaSum_decision, fiberMass_decision, add_mul, Finset.sum_mul,
        add_comm ((if d' = d then (1 : K) else 0) * value C (c₀ a))]
      congr 1
      · exact Finset.sum_congr rfl fun b _ => by rw [ih b, mul_assoc]
      · by_cases hd : d' = d
        · subst hd
          rw [dif_pos rfl, if_pos rfl, one_mul]
          have hiso := hT none rfl
          rw [subtreeAt_decision_none] at hiso
          cases hiso with
          | decision _ _ _ hchild => exact value_eq_of_contLaw_eq C ((hchild a).contLaw_eq C)
        · rw [dif_neg hd, if_neg hd, zero_mul]

/-- **The gated shape of `V` at a point of a strongly fair tree**: with `q₀` a `d`-node whose
subtree is `decision d c₀`, for every procedure `C` and every mixed action `m`,
`V_B(C[d ↦ m]) = offOcc_d(C) + fiberMass_d(C) · ∑_a m(a) V_{c₀ a}(C)`. (Strong fairness makes
every `d`-subtree isomorphic to `decision d c₀` and gives `#_d ≤ 1`, so `V` is affine in `C(d)`.)
Source: findings F10 ("`V = H(rest) + G(rest) f(C(d))` with `G ≥ 0` the reach mass of the
`d`-nodes and `f` affine"); dp-cf-2-026 (extension flag)
Kind: P
Fidelity: exact
Hyps: (a) `StronglyFair B` (the definition of record) -/
theorem value_deviate_eq_gated {B : Tree Ω ι acts K} (hB : StronglyFair B) (q₀ : B.DecNode)
    (d : ι) (hq₀ : pt B q₀ = d) (c₀ : acts d → Tree Ω ι acts K)
    (hc₀ : subtreeAt B q₀ = .decision d c₀) (m : FinDistr K (acts d)) :
    value (C.deviate d m) B =
      offOcc C B d + fiberMass C B d * ∑ a, m.w a * value C (c₀ a) := by
  have hcount : ∀ ℓ, count d B ℓ ≤ 1 := fun ℓ => StronglyFair.almostFair B hB d ℓ
  have hT : ∀ q : B.DecNode, pt B q = d → LabIso (subtreeAt B q) (.decision d c₀) :=
    fun q hq => by
      rw [← hc₀]
      exact hB d q ((mem_fiber B d q).mpr hq) q₀ ((mem_fiber B d q₀).mpr hq₀)
  rw [value_deviate_eq_sum_of_count_le_one C d B hcount m]
  simp only [value_deviatePure_eq_siaSum_add_offOcc C d B hcount,
    siaSum_eq_fiberMass_mul_of_iso C d c₀ B hT]
  have h1 : ∑ a, m.w a * (fiberMass C B d * value C (c₀ a) + offOcc C B d) =
      fiberMass C B d * (∑ a, m.w a * value C (c₀ a)) + offOcc C B d := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, m.sum_one, one_mul,
      Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [h1, add_comm]

end gated

/-! ### The theorem -/

section main

/-- `|((1 − t) p + t q) − p| ≤ ε` for `p, q ∈ [0, 1]` and `0 ≤ t ≤ ε`.
Source: none: infrastructure
Kind: L -/
theorem abs_lerp_sub_le {p q t ε : K} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ht0 : 0 ≤ t) (htε : t ≤ ε) : |(1 - t) * p + t * q - p| ≤ ε := by
  rw [show (1 - t) * p + t * q - p = t * (q - p) by ring, abs_mul, abs_of_nonneg ht0]
  have hb : |q - p| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc t * |q - p| ≤ t * 1 := mul_le_mul_of_nonneg_left hb ht0
    _ ≤ ε := by linarith

omit [∀ d, DecidableEq (acts d)] in
/-- Deviating to one's own action is no deviation.
Source: none: infrastructure
Kind: L -/
theorem Proc.deviate_self (C : Proc ι acts K) (d : ι) : C.deviate d (C d) = C := by
  funext e
  by_cases he : e = d
  · subst he; simp
  · simp [Proc.deviate_ne C _ he]

/-- **On a strongly fair tree every strict local maximum of `V_B` is a global maximum** — the
strongly-fair form of dp-cf-2-026's extension question ("does a strongly fair tree's `V` have
strict non-global local maxima?"): no. Proof: induction on the set `S` of points allowed to move
(`Finset.strongInduction`), choosing at each step the `S`-node `q₀` with the smallest subtree, so
that no `S`-point lies strictly below a `d_{q₀}`-node; the gated shape `value_deviate_eq_gated`
then makes `V` affine in `C(d)` with a `C'`-independent slope, strictness at `C` in that one
direction (along `(1 − t) C(d) + t m`, `t = min ε 1`) makes `C(d)` the best mixed action, and the
induction hypothesis on `S ∖ {d}` finishes. Contrast: on the almost-fair class the statement is
false (`almostFair_strictLocalMax_not_isOptimal`).
Source: dp-cf-2-026 (extension flag); findings F10 (the informal induction, now formal);
`repair/dynamic.md` Open 8; audit r1 fidelity B1
Kind: P
Fidelity: exact
Hyps: (a) `StronglyFair B` (definition of record, `dp-fairness-reloc`); (a) `IsStrictLocalMax C B`
(this package's definition, inhabited: `stronglyFair_strictLocalMax_inhabited`) -/
theorem stronglyFair_strictLocalMax_isOptimal (B : Tree Ω ι acts K) (hB : StronglyFair B)
    (C : Proc ι acts K) (h : IsStrictLocalMax C B) : IsOptimal C B := by
  obtain ⟨ε, hε, hloc⟩ := h
  have key : ∀ S : Finset ι, ∀ C' : Proc ι acts K, (∀ e, e ∉ S → C' e = C e) →
      value C' B ≤ value C B := by
    intro S
    induction S using Finset.strongInduction with
    | H S ih =>
      intro C' hC'
      by_cases hN : (Finset.univ.filter fun q : B.DecNode => pt B q ∈ S).Nonempty
      · obtain ⟨q₀, hq₀mem, hq₀min⟩ := Finset.exists_min_image
          (Finset.univ.filter fun q : B.DecNode => pt B q ∈ S) (fun q => size (subtreeAt B q)) hN
        obtain ⟨d, hq₀⟩ : ∃ d, pt B q₀ = d := ⟨_, rfl⟩
        have hdS : d ∈ S := hq₀ ▸ (Finset.mem_filter.mp hq₀mem).2
        have hdQ : d ∈ queried B := hq₀ ▸ pt_mem_queried B q₀
        obtain ⟨c₀, hc₀⟩ := subtreeAt_eq_decision' B q₀ d hq₀
        -- the gated shape at `d`
        have shape := fun (C'' : Proc ι acts K) (m : FinDistr K (acts d)) =>
          value_deviate_eq_gated C'' hB q₀ d hq₀ c₀ hc₀ m
        -- no `S`-point below a `d`-node: the reference values do not depend on `C'`
        have hchild : ∀ a, value C' (c₀ a) = value C (c₀ a) := by
          intro a
          apply value_congr_queried
          intro e he
          by_contra hne
          have heS : e ∈ S := by
            by_contra h'
            exact hne (hC' e h')
          obtain ⟨q, hq, hlt⟩ := exists_node_lt_of_mem_queried_child' B q₀ d hq₀ c₀ hc₀ a e he
          have := hq₀min q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq ▸ heS⟩)
          omega
        -- strictness at `C` in the `d`-direction: `C(d)` is the best mixed action
        have hf : ∀ m : FinDistr K (acts d),
            ∑ a, m.w a * value C (c₀ a) ≤ ∑ a, (C d).w a * value C (c₀ a) := by
          intro m
          by_contra hgt
          push Not at hgt
          have hmne : m ≠ C d := fun hm => by rw [hm] at hgt; exact lt_irrefl _ hgt
          have ht0 : (0 : K) ≤ min ε 1 := le_min hε.le zero_le_one
          have ht1 : min ε 1 ≤ 1 := min_le_right _ _
          have htpos : (0 : K) < min ε 1 := lt_min hε one_pos
          have htε : min ε 1 ≤ ε := min_le_left _ _
          have hmt := shape C (FinDistr.lerp (min ε 1) ht0 ht1 (C d) m)
          have hCd := shape C (C d)
          rw [Proc.deviate_self] at hCd
          have hne : ∃ e ∈ queried B, (C.deviate d (FinDistr.lerp (min ε 1) ht0 ht1 (C d) m)) e ≠
              C e := by
            refine ⟨d, hdQ, fun heq => hmne ?_⟩
            rw [Proc.deviate_same] at heq
            apply FinDistr.ext'
            intro a
            have := congrArg (fun p : FinDistr K (acts d) => p.w a) heq
            simp only [FinDistr.lerp_w] at this
            have h2 : min ε 1 * (m.w a - (C d).w a) = 0 := by linarith
            rcases mul_eq_zero.mp h2 with h | h
            · exact absurd h htpos.ne'
            · linarith
          have hnear : ∀ e x,
              |((C.deviate d (FinDistr.lerp (min ε 1) ht0 ht1 (C d) m)) e).w x - (C e).w x| ≤ ε := by
            intro e x
            by_cases hed : e = d
            · subst hed
              simp only [Proc.deviate_same, FinDistr.lerp_w]
              exact abs_lerp_sub_le (FinDistr.nonneg _ _) (FinDistr.w_le_one _ _) (m.nonneg _)
                (m.w_le_one _) ht0 htε
            · rw [Proc.deviate_ne C _ hed]
              simp [hε.le]
          have hlt := hloc _ hne hnear
          rw [hmt, hCd] at hlt
          have hlerp : ∑ a, (FinDistr.lerp (min ε 1) ht0 ht1 (C d) m).w a * value C (c₀ a) =
              (1 - min ε 1) * ∑ a, (C d).w a * value C (c₀ a) +
                min ε 1 * ∑ a, m.w a * value C (c₀ a) := by
            simp only [FinDistr.lerp_w, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
          rw [hlerp] at hlt
          have hF := fiberMass_nonneg C B d
          nlinarith [mul_nonneg (mul_nonneg hF ht0) (sub_nonneg.mpr hgt.le)]
        -- resetting `C'(d)` to `C(d)` does not lower `V`; then the induction hypothesis
        have h1 : value C' B =
            offOcc C' B d + fiberMass C' B d * ∑ a, (C' d).w a * value C (c₀ a) := by
          have := shape C' (C' d)
          rw [Proc.deviate_self] at this
          simpa only [hchild] using this
        have h2 : value (C'.deviate d (C d)) B =
            offOcc C' B d + fiberMass C' B d * ∑ a, (C d).w a * value C (c₀ a) := by
          simpa only [hchild] using shape C' (C d)
        have h3 : value (C'.deviate d (C d)) B ≤ value C B := by
          refine ih (S.erase d) (Finset.erase_ssubset hdS) _ fun e he => ?_
          by_cases hed : e = d
          · subst hed; simp
          · rw [Proc.deviate_ne C' _ hed]
            exact hC' e fun heS => he (Finset.mem_erase.mpr ⟨hed, heS⟩)
        have hF := fiberMass_nonneg C' B d
        have := mul_le_mul_of_nonneg_left (hf (C' d)) hF
        linarith
      · -- no node carries a point of `S`: `C'` agrees with `C` on every queried point
        have hagree : ∀ e ∈ queried B, C' e = C e := by
          intro e he
          by_contra hne
          have heS : e ∈ S := by
            by_contra h'
            exact hne (hC' e h')
          obtain ⟨q, hq⟩ := exists_decNode_of_mem_queried B e he
          exact hN ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq ▸ heS⟩⟩
        exact (value_congr_queried B hagree).le
  intro C'
  have hagree : ∀ e ∈ queried B,
      C' e = (fun e => if e ∈ queried B then C' e else C e : Proc ι acts K) e :=
    fun e he => by simp [he]
  rw [value_congr_queried B hagree]
  exact key (queried B) _ fun e he => by simp [he]

end main

end Cleanroom.Decision.DpLocalOpt

import Cleanroom.Decision.DpTwoLesions.Laws

/-!
# T10 — Proposition D: ITT on the draw is forcing; ITT on occurrences is deviation

**General finite-tree theorems.** The IV note's Proposition D(1): at a point `d` that is
*draw-recorded* for `C` — every positive `O_d`-run meets `d` at most once (clause 1) and every
`d`-node met on a positive `O_d`-run is subtree-veridical (clause 2), both stated inline as
hypotheses, **no action-veridicality** — the mass of `X ∧ (drew a) ∧ O_d` relates to the
reach-weighted single-instance forcing of `X` at the active `d`-nodes:
`μ(X ∩ drew a ∩ O_d)·∑_{q active} R_q = (∑_{q active} forcedBelowEv q a X)·μ(drew a ∩ O_d)`.
It is `dp-smoking-lesion`'s Proposition 13 with the *draw event* in place of the *act event*,
which is what lets it hold on the overwrite tree. D(2) is `dp-core-tree`'s
`disposition_faithful` at the run level plus the payoff form and the argmax identity with
`dp-local-opt`'s Theorem 2 evaluator. The overwrite witness is in `PropDWitness.lean`.
Serves [[dp-two-lesions-mandate]] T10 (dp-core-094, 2-004, 084, 086).
-/

namespace Cleanroom.Decision.DpTwoLesions

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree

section general

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] {acts : ι → Type}
  [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
variable (obs : ι → Finset Ω) (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)

/-! ## The active fiber and the forced `X`-mass -/

/-- **The active fiber**: the `d`-nodes met on some positive `O_d`-run (the IV note's
`N_d^ver`, under draw-recording clause 2 every such node is subtree-veridical).
Source: [[iv-design-draw-as-instrument]] §4 Proposition D ("let `N_d^ver` be the `d`-nodes met
on `O_d`-runs")
Kind: D -/
noncomputable def activeFiber : Finset B.DecNode := by
  classical exact (fiber B d).filter fun q => ActiveNode obs C B d q

/-- Membership in the active fiber. Source: none: infrastructure. Kind: L -/
theorem mem_activeFiber (q : B.DecNode) :
    q ∈ activeFiber obs C B d ↔ pt B q = d ∧ ActiveNode obs C B d q := by
  unfold activeFiber fiber
  classical
  simp [Finset.mem_filter]

/-- **The forced `X`-mass below `q`**: `∑_{ℓ below q, λ(ℓ) ⊨ X} μ_{C[q ↦ a]}(ℓ)` — the mass of
`X` below the `a`-edge of `q` when `a` is forced at `q` only (the IV note's `R_q θ_{q,a}(X)`;
`forcedBelow` with the indicator of `X` in place of the payoff).
Source: [[iv-design-draw-as-instrument]] §4 Proposition D(1) ("`θ_{q,a}` is the law of the
continuation below the `a`-edge of `q`"); [[decision-problems-v2]] §8 (`G_q`)
Kind: D -/
def forcedBelowEv (q : B.DecNode) (a : acts (pt B q)) (X : Finset Ω) : K :=
  ∑ ℓ ∈ leavesBelow B q, if world B ℓ ∈ X then
    leafLawNode B ((NodePolicy.ofProc C B).update q (FinDistr.pure a)) ℓ else 0

/-- **Node edge identity, indicator form**: the `C`-mass of `X` through the `a`-edge of `q` is
`C(d_q)(a)` times the forced `X`-mass below `q`.
Source: [[iv-design-draw-as-instrument]] §4 Proposition D proof sketch ("Definition 6 factors
`μ(reach q, draw a at q, X) = R_q · C(d)(a) · θ_{q,a}(X)`"); `dp-smoking-lesion`'s
`edge_paySum_eq_mul_forcedBelow` with an indicator
Kind: L -/
theorem edge_ev_eq_mul_forcedBelowEv (q : B.DecNode) (a : acts (pt B q)) (X : Finset Ω) :
    (∑ ℓ, if edgeOf B q ℓ = some a ∧ world B ℓ ∈ X then leafLaw C B ℓ else 0) =
      (C (pt B q)).w a * forcedBelowEv C B q a X := by
  unfold forcedBelowEv leavesBelow
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  by_cases he : edgeOf B q ℓ = some a
  · have hs : (edgeOf B q ℓ).isSome := by rw [he]; rfl
    rw [if_pos hs]
    by_cases hx : world B ℓ ∈ X
    · rw [if_pos ⟨he, hx⟩, if_pos hx]
      have h1 := leafLawNode_update_of_edge B (NodePolicy.ofProc C B) q ℓ
        (NodePolicy.ofProc C B q) a he
      rw [NodePolicy.update_eq_self] at h1
      rw [← leafLawNode_ofProc C B ℓ, h1]
      simp only [NodePolicy.ofProc]
    · rw [if_neg (fun h => hx h.2), if_neg hx, mul_zero]
  · rw [if_neg (fun h => he h.1)]
    by_cases hs : (edgeOf B q ℓ).isSome
    · rw [if_pos hs]
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hs
      have hba : b ≠ a := fun h => he (by rw [hb, h])
      rw [leafLawNode_update_of_edge B (NodePolicy.ofProc C B) q ℓ (FinDistr.pure a) b hb]
      simp [FinDistr.pure_w, hba]
    · rw [if_neg hs, mul_zero]

/-! ## Grouping positive `O_d`-runs by their unique `d`-node -/

/-- **Grouping under draw-recording clause 1** (`#_d ≤ 1` on positive `O_d`-runs only): the mass
of a run event `P` contained in the `O_d`-runs is the sum over the `d`-nodes `q` of the
positive mass of the leaves through `q` satisfying `Q q`, when `P` agrees with `Q q₀` at the
unique `d`-node `q₀` of each positive `O_d`-path, fails on paths meeting no `d`-node, and `Q`
is also contained in the `O_d`-runs. (`dp-core-tree`'s `mass_eq_sum_fiber_of_count_le_one`
assumes `#_d ≤ 1` on all positive runs; this is the `O_d`-restricted copy.)
Source: none: infrastructure (the grouping step of Proposition D's proof)
Kind: L -/
theorem mass_eq_sum_fiber_of_count_le_one_obs
    (hcount : ∀ ℓ, 0 < leafLaw C B ℓ → world B ℓ ∈ obs d → count d B ℓ ≤ 1)
    (P : B.Leaves → Prop) [DecidablePred P] (Q : B.DecNode → B.Leaves → Prop)
    [∀ q, DecidablePred (Q q)]
    (hPO : ∀ ℓ, P ℓ → world B ℓ ∈ obs d) (hQO : ∀ q ℓ, Q q ℓ → world B ℓ ∈ obs d)
    (hQ : ∀ q ℓ, Q q ℓ → (edgeOf B q ℓ).isSome)
    (hPQ : ∀ ℓ q₀, dNodesOn B d ℓ = {q₀} → (P ℓ ↔ Q q₀ ℓ))
    (hP0 : ∀ ℓ, dNodesOn B d ℓ = ∅ → ¬ P ℓ) :
    mass C B (Finset.univ.filter P) =
      ∑ q ∈ fiber B d, ∑ ℓ, if 0 < leafLaw C B ℓ ∧ Q q ℓ then leafLaw C B ℓ else 0 := by
  rw [mass_filter, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hzero
  · by_cases hO : world B ℓ ∈ obs d
    · have hle := hcount ℓ hpos hO
      rw [count_eq_card_dNodesOn] at hle
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
      · rw [Finset.card_eq_zero] at h0
        rw [if_neg (hP0 ℓ h0)]
        symm
        apply Finset.sum_eq_zero
        intro q hq
        rw [if_neg]
        rintro ⟨-, hQq⟩
        have hmem : q ∈ dNodesOn B d ℓ := by
          rw [mem_dNodesOn]; exact ⟨(Finset.mem_filter.mp hq).2, hQ q ℓ hQq⟩
        rw [h0] at hmem
        exact Finset.notMem_empty q hmem
      · obtain ⟨q₀, hq₀⟩ := Finset.card_eq_one.mp h1
        rw [sum_fiber_eq_of_singleton hq₀ _ (fun q hq => by
          rw [if_neg]; rintro ⟨-, h⟩; exact hq (hQ q ℓ h))]
        by_cases hPl : P ℓ
        · have hQl : Q q₀ ℓ := (hPQ ℓ q₀ hq₀).mp hPl
          rw [if_pos hPl, if_pos ⟨hpos, hQl⟩]
        · have hQl : ¬ Q q₀ ℓ := fun h => hPl ((hPQ ℓ q₀ hq₀).mpr h)
          rw [if_neg hPl, if_neg (fun h => hQl h.2)]
    · rw [if_neg (fun h => hO (hPO ℓ h))]
      symm
      apply Finset.sum_eq_zero
      intro q _
      rw [if_neg]
      rintro ⟨-, hQq⟩
      exact hO (hQO q ℓ hQq)
  · rw [← hzero]; simp

/-- On a positive path whose `d`-nodes form the singleton `{q₀}`, membership in `drew d a` is
"the path took the `a`-edge at `q₀`".
Source: none: infrastructure (from `screening_draw`'s proof)
Kind: L -/
theorem mem_drew_iff_edgeS_of_singleton (a : acts d) (ℓ : B.Leaves) (q₀ : B.DecNode)
    (hq₀ : dNodesOn B d ℓ = {q₀}) :
    ℓ ∈ drew d a B ↔ edgeS B q₀ ℓ = some ⟨d, a⟩ := by
  simp only [drew, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [mem_draws_iff_exists_edgeS]
  constructor
  · rintro ⟨q, hq⟩
    have hmem : q ∈ dNodesOn B d ℓ := by
      rw [mem_dNodesOn]; exact ⟨pt_eq_of_edgeS B q ℓ hq, isSome_of_edgeS B q ℓ hq⟩
    rw [hq₀, Finset.mem_singleton] at hmem
    rw [← hmem]; exact hq
  · intro h; exact ⟨q₀, h⟩

/-- A path meeting no `d`-node is not in `drew d a`. Source: none: infrastructure. Kind: L -/
theorem not_mem_drew_of_dNodesOn_empty (a : acts d) (ℓ : B.Leaves) (h0 : dNodesOn B d ℓ = ∅) :
    ℓ ∉ drew d a B := by
  intro hmem
  simp only [drew, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  rw [mem_draws_iff_exists_edgeS] at hmem
  obtain ⟨q, hq⟩ := hmem
  have hm : q ∈ dNodesOn B d ℓ := by
    rw [mem_dNodesOn]; exact ⟨pt_eq_of_edgeS B q ℓ hq, isSome_of_edgeS B q ℓ hq⟩
  rw [h0] at hm
  exact Finset.notMem_empty q hm

open Classical in
/-- **The per-node sum under subtree-veridicality**: at a `d`-node that is subtree-veridical
whenever active, the positive-`O_d`-`X`-mass through the `a`-edge is the plain `X`-mass through
the `a`-edge if the node is active, and `0` otherwise.
Source: none: infrastructure (the node step of Proposition D's proof)
Kind: L -/
theorem node_sum_X_edge (q : B.DecNode) (hq : pt B q = d)
    (hsvq : ActiveNode obs C B d q → SubtreeVeridical obs B q) (a : acts d) (X : Finset Ω) :
    (∑ ℓ, if 0 < leafLaw C B ℓ ∧ (world B ℓ ∈ X ∧ edgeS B q ℓ = some ⟨d, a⟩ ∧
        world B ℓ ∈ obs d) then leafLaw C B ℓ else 0) =
      if ActiveNode obs C B d q then
        ∑ ℓ, if edgeOf B q ℓ = some (hq.symm ▸ a) ∧ world B ℓ ∈ X then leafLaw C B ℓ else 0
      else 0 := by
  subst hq
  by_cases hact : ActiveNode obs C B (pt B q) q
  · rw [if_pos hact]
    have hsv := hsvq hact
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp only [edgeS_eq_some_iff]
    by_cases he : edgeOf B q ℓ = some a
    · by_cases hx : world B ℓ ∈ X
      · rw [if_pos (show edgeOf B q ℓ = some a ∧ world B ℓ ∈ X from ⟨he, hx⟩)]
        have hbelow : ℓ ∈ leavesBelow B q := by rw [mem_leavesBelow, he]; rfl
        have hO := hsv ℓ hbelow
        rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hzero
        · rw [if_pos (show 0 < leafLaw C B ℓ ∧ world B ℓ ∈ X ∧ edgeOf B q ℓ = some a ∧
            world B ℓ ∈ obs (pt B q) from ⟨hpos, hx, he, hO⟩)]
        · rw [← hzero]; simp
      · rw [if_neg (show ¬ (edgeOf B q ℓ = some a ∧ world B ℓ ∈ X) from fun h => hx h.2),
          if_neg (show ¬ (0 < leafLaw C B ℓ ∧ world B ℓ ∈ X ∧ edgeOf B q ℓ = some a ∧
            world B ℓ ∈ obs (pt B q)) from fun h => hx h.2.1)]
    · rw [if_neg (show ¬ (edgeOf B q ℓ = some a ∧ world B ℓ ∈ X) from fun h => he h.1),
        if_neg (show ¬ (0 < leafLaw C B ℓ ∧ world B ℓ ∈ X ∧ edgeOf B q ℓ = some a ∧
          world B ℓ ∈ obs (pt B q)) from fun h => he h.2.2.1)]
  · rw [if_neg hact]
    apply Finset.sum_eq_zero
    intro ℓ _
    rw [if_neg]
    rintro ⟨hpos, -, he, hO⟩
    exact hact ⟨ℓ, hpos, hO, isSome_of_edgeS B q ℓ he⟩

/-! ## Proposition D(1) -/

/-- **Proposition D(1), the numerator**: under draw-recording (clauses 1–2 inline),
`μ(X ∩ drew a ∩ O_d) = C(d)(a) · ∑_{q active} forcedBelowEv q a X`.
Source: [[iv-design-draw-as-instrument]] §4 Proposition D(1)
Kind: P
Fidelity: exact
Hyps: none (the two clauses of draw-recording) -/
theorem propD1_num
    (hcount : ∀ ℓ, 0 < leafLaw C B ℓ → world B ℓ ∈ obs d → count d B ℓ ≤ 1)
    (hsv : ∀ ℓ, 0 < leafLaw C B ℓ → world B ℓ ∈ obs d → ∀ q, pt B q = d →
      (edgeOf B q ℓ).isSome → SubtreeVeridical obs B q)
    (a : acts d) (X : Finset Ω) :
    mass C B (worldEv B X ∩ drew d a B ∩ worldEv B (obs d)) =
      (C d).w a * ∑ q ∈ activeFiber obs C B d,
        if h : pt B q = d then forcedBelowEv C B q (h.symm ▸ a) X else 0 := by
  classical
  have hset : worldEv B X ∩ drew d a B ∩ worldEv B (obs d) =
      Finset.univ.filter fun ℓ => world B ℓ ∈ X ∧ ℓ ∈ drew d a B ∧ world B ℓ ∈ obs d := by
    ext ℓ; simp [worldEv, and_assoc]
  rw [hset, mass_eq_sum_fiber_of_count_le_one_obs obs C B d hcount _
    (fun q ℓ => world B ℓ ∈ X ∧ edgeS B q ℓ = some ⟨d, a⟩ ∧ world B ℓ ∈ obs d)
    (fun ℓ h => h.2.2) (fun q ℓ h => h.2.2) (fun q ℓ h => isSome_of_edgeS B q ℓ h.2.1)
    (fun ℓ q₀ hq₀ => by rw [mem_drew_iff_edgeS_of_singleton B d a ℓ q₀ hq₀])
    (fun ℓ h0 hP => not_mem_drew_of_dNodesOn_empty B d a ℓ h0 hP.2.1)]
  -- per node
  have hsvq : ∀ q, pt B q = d → ActiveNode obs C B d q → SubtreeVeridical obs B q := by
    rintro q hq ⟨ℓ, hpos, hO, he⟩
    exact hsv ℓ hpos hO q hq he
  unfold activeFiber
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hqd : pt B q = d := (Finset.mem_filter.mp hq).2
  rw [node_sum_X_edge obs C B d q hqd (hsvq q hqd) a X]
  by_cases hact : ActiveNode obs C B d q
  · rw [if_pos hact, if_pos hact, dif_pos hqd, edge_ev_eq_mul_forcedBelowEv]
    subst hqd; rfl
  · rw [if_neg hact, if_neg hact, mul_zero]

/-- **Proposition D(1), the normaliser**: under draw-recording,
`μ(drew a ∩ O_d) = C(d)(a) · ∑_{q active} R_q`.
Source: [[iv-design-draw-as-instrument]] §4 Proposition D(1) ("`∑_{q ∈ N_d^ver} R_q(C)`")
Kind: P
Fidelity: exact
Hyps: none -/
theorem propD1_den
    (hcount : ∀ ℓ, 0 < leafLaw C B ℓ → world B ℓ ∈ obs d → count d B ℓ ≤ 1)
    (hsv : ∀ ℓ, 0 < leafLaw C B ℓ → world B ℓ ∈ obs d → ∀ q, pt B q = d →
      (edgeOf B q ℓ).isSome → SubtreeVeridical obs B q)
    (a : acts d) :
    mass C B (drew d a B ∩ worldEv B (obs d)) =
      (C d).w a * ∑ q ∈ activeFiber obs C B d, reach C B q := by
  classical
  have hset : drew d a B ∩ worldEv B (obs d) =
      Finset.univ.filter fun ℓ => world B ℓ ∈ (Finset.univ : Finset Ω) ∧ ℓ ∈ drew d a B ∧
        world B ℓ ∈ obs d := by
    ext ℓ; simp [worldEv]
  rw [hset, mass_eq_sum_fiber_of_count_le_one_obs obs C B d hcount _
    (fun q ℓ => world B ℓ ∈ (Finset.univ : Finset Ω) ∧ edgeS B q ℓ = some ⟨d, a⟩ ∧
      world B ℓ ∈ obs d)
    (fun ℓ h => h.2.2) (fun q ℓ h => h.2.2) (fun q ℓ h => isSome_of_edgeS B q ℓ h.2.1)
    (fun ℓ q₀ hq₀ => by rw [mem_drew_iff_edgeS_of_singleton B d a ℓ q₀ hq₀])
    (fun ℓ h0 hP => not_mem_drew_of_dNodesOn_empty B d a ℓ h0 hP.2.1)]
  have hsvq : ∀ q, pt B q = d → ActiveNode obs C B d q → SubtreeVeridical obs B q := by
    rintro q hq ⟨ℓ, hpos, hO, he⟩
    exact hsv ℓ hpos hO q hq he
  unfold activeFiber
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hqd : pt B q = d := (Finset.mem_filter.mp hq).2
  rw [node_sum_X_edge obs C B d q hqd (hsvq q hqd) a Finset.univ]
  by_cases hact : ActiveNode obs C B d q
  · rw [if_pos hact, if_pos hact]
    simp only [Finset.mem_univ, and_true]
    rw [mass_edge, Cleanroom.Decision.DpSmokingLesion.sum_isSome_eq_reach]
    subst hqd; rfl
  · rw [if_neg hact, if_neg hact, mul_zero]

/-- **Proposition D(1)** (general finite tree, no action-veridicality): under draw-recording
at `d` for `C`,
`μ(X ∩ drew a ∩ O_d) · ∑_{q active} R_q = (∑_{q active} forcedBelowEv q a X) · μ(drew a ∩ O_d)`
— the draw-conditional law of `X` on `O_d` is the reach-weighted single-instance forcing of `X`
at the real `d`-nodes (R2-real, with the draw event in place of the act event).
Source: [[iv-design-draw-as-instrument]] §4 Proposition D(1) ("`μ(X | a_d = a, λ ⊨ O_d) =
Σ_{q ∈ N_d^ver} R_q(C) θ_{q,a}(X) / Σ_{q ∈ N_d^ver} R_q(C)`"); dp-core-094, 2-004
Kind: P
Fidelity: exact (cross-multiplied; the note's `C(d)(a) > 0`, `ν(O_d) > 0` not needed for the
identity); the averaging set is the active fiber, which draw-recording makes subtree-veridical
Hyps: none (the two draw-recording clauses, inline) -/
theorem propD1
    (hcount : ∀ ℓ, 0 < leafLaw C B ℓ → world B ℓ ∈ obs d → count d B ℓ ≤ 1)
    (hsv : ∀ ℓ, 0 < leafLaw C B ℓ → world B ℓ ∈ obs d → ∀ q, pt B q = d →
      (edgeOf B q ℓ).isSome → SubtreeVeridical obs B q)
    (a : acts d) (X : Finset Ω) :
    mass C B (worldEv B X ∩ drew d a B ∩ worldEv B (obs d)) *
        (∑ q ∈ activeFiber obs C B d, reach C B q) =
      (∑ q ∈ activeFiber obs C B d,
        if h : pt B q = d then forcedBelowEv C B q (h.symm ▸ a) X else 0) *
        mass C B (drew d a B ∩ worldEv B (obs d)) := by
  rw [propD1_num obs C B d hcount hsv a X, propD1_den obs C B d hcount hsv a]
  ring

/-! ## Proposition D(2): ITT on occurrences is Theorem 2's deviation -/

/-- **Proposition D(2), run level** — `dp-core-tree`'s `disposition_faithful` restated: when
`#_d ≤ 1` on every run, `μ_C(S ∩ drew a)·μ_{C[d↦a]}(occ) = μ_{C[d↦a]}(S ∩ occ)·μ_C(drew a)`.
Source: [[iv-design-draw-as-instrument]] §4 Proposition D(2) ("`μ(X | a_d = a) =
μ_{C[d↦a]}(X | occ(d))`"); `dp-core-tree` Faithful.lean (dp-cf-2-004)
Kind: L (a restatement; the content is `disposition_faithful`)
Fidelity: exact -/
theorem propD2_run (hfair : ∀ ℓ, count d B ℓ ≤ 1) (a : acts d) (S : Finset B.Leaves) :
    mass C B (S ∩ drew d a B) * mass (C.deviatePure d a) B (occ d B) =
      mass (C.deviatePure d a) B (S ∩ occ d B) * mass C B (drew d a B) :=
  disposition_faithful C B d a hfair S

/-- The payoff mass of a run event. Source: none: infrastructure. Kind: D -/
def paySumRun (S : Finset B.Leaves) : K := ∑ ℓ ∈ S, leafLaw C B ℓ * payoff B ℓ

/-- **Proposition D(2), payoff form**: when `#_d ≤ 1` on every run,
`∑_{ℓ ∈ drew a} μ_C(ℓ) r(ℓ) = C(d)(a) · ∑_{ℓ ∈ occ} μ_{C[d↦a]}(ℓ) r(ℓ)` — the on-occurrence
payoff mass of the deviation (`dp-local-opt`'s `ssaNum`).
Source: [[iv-design-draw-as-instrument]] §4 Proposition D(2) ("`E[r | a_d = a] =
E_{μ_{C[d↦a]}}[r | occ(d)]`, Theorem 2's evaluator")
Kind: P
Fidelity: exact
Hyps: none -/
theorem propD2_pay (hfair : ∀ ℓ, count d B ℓ ≤ 1) (a : acts d) :
    paySumRun C B (drew d a B) =
      (C d).w a * Cleanroom.Decision.DpLocalOpt.ssaNum C B d (FinDistr.pure a) := by
  unfold paySumRun Cleanroom.Decision.DpLocalOpt.ssaNum
  rw [Finset.mul_sum]
  symm
  rw [← Finset.sum_subset (drew_subset_occ d a B)]
  · refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    rw [mem_drew] at hℓ
    rw [leafLaw_eq_mul_deviatePure_of_drew C B d a ℓ hℓ (hfair ℓ)]
    simp only [Proc.deviatePure]; ring
  · intro ℓ hℓ hℓ'
    rw [mem_occ] at hℓ
    rw [mem_drew] at hℓ'
    obtain ⟨b, hba, hb⟩ := exists_other_draw_of_not_drew B d a ℓ hℓ hℓ'
    rw [show leafLaw (C.deviate d (FinDistr.pure a)) B ℓ = 0 from
      leafLaw_deviatePure_eq_zero_of_other C B d a b hba ℓ hb]
    ring

/-- `μ_C(drew a) = C(d)(a) · μ_C(occ)` when `#_d ≤ 1` on every run.
Source: none: infrastructure (from `mass_inter_drew`, `mass_deviatePure_inter_occ`,
`occurrence_constancy`)
Kind: L -/
theorem mass_drew_eq (hfair : ∀ ℓ, count d B ℓ ≤ 1) (a : acts d) :
    mass C B (drew d a B) = (C d).w a * mass C B (occ d B) := by
  have h1 := mass_inter_drew C B d a hfair Finset.univ
  have h2 := mass_deviatePure_inter_occ C B d a hfair Finset.univ
  simp only [Finset.univ_inter] at h1 h2
  rw [h1, ← h2]
  show (C d).w a * mass (C.deviate d (FinDistr.pure a)) B (occ d B) = _
  rw [occurrence_constancy]

/-- **Proposition D(2), the argmax identity**: when `#_d ≤ 1` on every run, `C(d)(a), C(d)(b) > 0`
and `μ(occ(d)) > 0`, `E[r | drew a] ≤ E[r | drew b] ↔ V_B(C[d↦a]) ≤ V_B(C[d↦b])` — the
draw-conditional ranking of actions is Theorem 2's (Definition 22's) deviation ranking.
Source: [[iv-design-draw-as-instrument]] §4 Proposition D(2) ("`argmax_a E[r | a_d = a] =
argmax_a V_B(C[d↦a])`")
Kind: C
Fidelity: exact (as an iff of the two orders on any two actions with positive label mass)
Hyps: none -/
theorem propD2_argmax (hfair : ∀ ℓ, count d B ℓ ≤ 1) (a b : acts d) (ha : 0 < (C d).w a)
    (hb : 0 < (C d).w b) (hocc : 0 < mass C B (occ d B)) :
    paySumRun C B (drew d a B) / mass C B (drew d a B) ≤
        paySumRun C B (drew d b B) / mass C B (drew d b B) ↔
      value (C.deviatePure d a) B ≤ value (C.deviatePure d b) B := by
  rw [propD2_pay C B d hfair a, propD2_pay C B d hfair b, mass_drew_eq C B d hfair a,
    mass_drew_eq C B d hfair b]
  rw [mul_div_mul_left _ _ ha.ne', mul_div_mul_left _ _ hb.ne']
  rw [div_le_div_iff_of_pos_right hocc]
  show _ ↔ value (C.deviate d (FinDistr.pure a)) B ≤ value (C.deviate d (FinDistr.pure b)) B
  rw [Cleanroom.Decision.DpLocalOpt.value_deviate_eq_ssaNum_add_offOcc,
    Cleanroom.Decision.DpLocalOpt.value_deviate_eq_ssaNum_add_offOcc]
  constructor <;> intro h <;> linarith

end general

end Cleanroom.Decision.DpTwoLesions

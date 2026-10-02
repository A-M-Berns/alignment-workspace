import Cleanroom.Decision.DpReferentsCdt.C2A

/-!
# Theorem C2-B′ at the label in play: Open 11 closed

**Open 11** (`repair/C1.md`; dp-sl-073; mandate T6) asked whether Theorem C2-B′ — `refR1State =
refR2Real` — holds under Definition 7 recording *for `C` and its point-deviations at `d`*
(`RecordsForDeviations`) rather than for every procedure (`RecordsForAll`). The first pass proved it
at every full-support label (`refR1State_eq_refR2Real_deviate_of_fullSupport`, `C2A.lean`) and left
the step `refR2Real (C[d↦unif]) = refR2Real C` open for a label `C(d)` with null acts.

This file proves that step (`refR2Real_eq_refR2Real_deviate_of_recordsFor`) and closes Open 11
(`c2B_of_recordsFor_uniform`, `c2B_of_recordsForDeviations`), with a hypothesis **weaker** than the
one asked for: F3′ structural (for its first clause: real-fiber nodes are subtree-veridical),
Definition 3's disjointness (used only by the full-support half), and Definition 7 recording for
**one** full-support deviation `C[d↦m']` (the uniform one suffices). No positivity is assumed: at a
null denominator both sides are Lean's junk `0`, and the guarded reading is the one with
`0 < ν_{C[d↦a]}(O_d)` (see the report).

**The argument.** Fix a real-fiber node `q` (node-action-veridical, hence subtree-veridical by
F3′(i): every leaf below `q` lies in `O_d`). For a leaf `ℓ` below `q`: if a second `d`-node lies on
`ℓ`'s path, then `ℓ` is `C[d↦m']`-null (Definition 7's exactly-one clause, since `ℓ ∈ O_d`), and a
`C[d↦m']`-null leaf is null under the forced law `p[q↦δ_a]` of *both* `C` and `C[d↦m']` (the only
weights that vanish under `C[d↦m']` are chance weights and non-`d` draws, which `C` shares —
`leafLawNode_eq_zero_mono`); if no second `d`-node lies on the path, the two forced laws agree
weight by weight (`leafLawNode_congr_path`). Summing over the leaves below `q` gives
`forcedBelow` and (via `reachNode_eq_sum_leavesBelow` and `reachNode_update_self`) `R_q`
identical under `C` and `C[d↦m']`; summing over the real fiber gives `refR2Real`.

Corollaries: label-freedom of `refR2Real` under `RecordsForDeviations` with no positivity
(`refR2Real_deviate_eq_refR1State_of_recordsForDeviations`), and the fixed-face / tie / pure-label
statements of `C2A.lean` restated under `RecordsForDeviations`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpReferentsCdt

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-! ## Node-policy plumbing -/

section plumbing

/-- The run law under a node policy depends on the policy only at the nodes on the leaf's path.
Source: none: infrastructure ([[decision-problems-v2]] §8: "each node occurs at most once per path")
Kind: L -/
theorem leafLawNode_congr_path :
    (B : Tree Ω ι acts K) → ∀ (p p' : NodePolicy B) (ℓ : B.Leaves),
      (∀ q, (edgeOf B q ℓ).isSome → p q = p' q) → leafLawNode B p ℓ = leafLawNode B p' ℓ
  | leaf _ _, _, _, _, _ => rfl
  | chance _ β child, p, p', ⟨i, ℓ⟩, h => by
      rw [leafLawNode_chance, leafLawNode_chance]
      congr 1
      exact leafLawNode_congr_path (child i) _ _ ℓ fun q hq => h ⟨i, q⟩ (by
        rw [edgeOf_chance_same]; exact hq)
  | decision d child, p, p', ⟨a, ℓ⟩, h => by
      rw [leafLawNode_decision, leafLawNode_decision]
      have h0 : p none = p' none := h none (by simp [edgeOf_decision_none])
      rw [h0]
      congr 1
      exact leafLawNode_congr_path (child a) _ _ ℓ fun q hq => h (some ⟨a, q⟩) (by
        rw [edgeOf_decision_some_same]; exact hq)

/-- If every draw weight that vanishes under `p'` on the leaf's path also vanishes under `p`, a
`p'`-null leaf is `p`-null (chance weights are shared).
Source: none: infrastructure
Kind: L -/
theorem leafLawNode_eq_zero_mono :
    (B : Tree Ω ι acts K) → ∀ (p p' : NodePolicy B) (ℓ : B.Leaves),
      (∀ q b, edgeOf B q ℓ = some b → (p' q).w b = 0 → (p q).w b = 0) →
      leafLawNode B p' ℓ = 0 → leafLawNode B p ℓ = 0
  | leaf _ _, _, _, _, _, h0 => by
      rw [leafLawNode_leaf] at h0; exact absurd h0 one_ne_zero
  | chance _ β child, p, p', ⟨i, ℓ⟩, h, h0 => by
      rw [leafLawNode_chance] at h0 ⊢
      rcases mul_eq_zero.mp h0 with hβ | hrest
      · rw [hβ, zero_mul]
      · rw [leafLawNode_eq_zero_mono (child i) (p.restrictChance i) (p'.restrictChance i) ℓ
          (fun q b hq => h ⟨i, q⟩ b (by rw [edgeOf_chance_same]; exact hq)) hrest, mul_zero]
  | decision d child, p, p', ⟨a, ℓ⟩, h, h0 => by
      rw [leafLawNode_decision] at h0 ⊢
      rcases mul_eq_zero.mp h0 with hw | hrest
      · rw [h none a (by simp [edgeOf_decision_none]) hw, zero_mul]
      · rw [leafLawNode_eq_zero_mono (child a) (p.restrictDecision a) (p'.restrictDecision a) ℓ
          (fun q b hq => h (some ⟨a, q⟩) b (by rw [edgeOf_decision_some_same]; exact hq)) hrest,
          mul_zero]

/-- The run law under a node policy has total mass one.
Source: none: infrastructure (the node-policy form of `sum_leafLaw`)
Kind: L -/
theorem sum_leafLawNode :
    (B : Tree Ω ι acts K) → ∀ (p : NodePolicy B), ∑ ℓ, leafLawNode B p ℓ = 1
  | leaf ω r, _ => by
      have hc : Fintype.card (leaf ω r : Tree Ω ι acts K).Leaves = 1 := rfl
      simp only [leafLawNode_leaf, Finset.sum_const, Finset.card_univ, hc, one_smul]
  | chance _ β child, p => by
      rw [sum_leaves_chance]
      simp only [leafLawNode_chance, ← Finset.mul_sum, sum_leafLawNode (child _) _, mul_one]
      exact β.sum_one
  | decision d child, p => by
      rw [sum_leaves_decision]
      simp only [leafLawNode_decision, ← Finset.mul_sum, sum_leafLawNode (child _) _, mul_one]
      exact (p none).sum_one

/-- `R_q` under a node policy is the sum of the leaf laws below `q` (the node-policy form of
`reach_eq_mass_leavesBelow`).
Source: [[decision-problems-v2]] §8 (`R_q := μ(reach q)`); none: infrastructure
Kind: L -/
theorem reachNode_eq_sum_leavesBelow :
    (B : Tree Ω ι acts K) → ∀ (p : NodePolicy B) (q : B.DecNode),
      reachNode B p q = ∑ ℓ ∈ leavesBelow B q, leafLawNode B p ℓ
  | leaf _ _, _, q => q.elim
  | chance _ β child, p, ⟨i, q⟩ => by
      rw [reachNode_chance, reachNode_eq_sum_leavesBelow (child i) _ q]
      unfold leavesBelow
      rw [Finset.sum_filter, Finset.sum_filter, sum_leaves_chance]
      rw [Finset.sum_eq_single i]
      · simp only [edgeOf_chance, dite_true, leafLawNode_chance, mul_ite, mul_zero, Finset.mul_sum]
        rfl
      · intro j _ hj
        simp [edgeOf_chance, hj]
      · intro h; exact absurd (Finset.mem_univ i) h
  | decision d child, p, none => by
      rw [reachNode_decision_none]
      unfold leavesBelow
      rw [Finset.sum_filter, sum_leaves_decision]
      have hinner : ∀ a, (∑ ℓ : (child a).Leaves,
          if (edgeOf (decision d child) none ⟨a, ℓ⟩).isSome then
            leafLawNode (decision d child) p ⟨a, ℓ⟩ else 0) = (p none).w a := by
        intro a
        have hcond : ∀ ℓ : (child a).Leaves,
            (edgeOf (decision d child) none ⟨a, ℓ⟩).isSome = true := fun _ => rfl
        rw [Finset.sum_congr rfl (fun ℓ _ => if_pos (hcond ℓ))]
        simp only [leafLawNode_decision]
        rw [← Finset.mul_sum, sum_leafLawNode (child a) _, mul_one]
      simp only [hinner]
      exact (p none).sum_one.symm
  | decision d child, p, some ⟨a, q⟩ => by
      rw [reachNode_decision_some, reachNode_eq_sum_leavesBelow (child a) _ q]
      unfold leavesBelow
      rw [Finset.sum_filter, Finset.sum_filter, sum_leaves_decision]
      rw [Finset.sum_eq_single a]
      · simp only [edgeOf_decision_some, dite_true, leafLawNode_decision, mul_ite, mul_zero,
          Finset.mul_sum]
        rfl
      · intro b _ hb
        simp [edgeOf_decision_some, hb]
      · intro h; exact absurd (Finset.mem_univ a) h

/-- Two distinct `d`-nodes on a leaf's path put `#_d(ℓ) ≥ 2`.
Source: none: infrastructure ([[decision-problems-v2]] Definition 7's "exactly one `d`-node")
Kind: L -/
theorem two_le_count_of_ne (B : Tree Ω ι acts K) {d : ι} {ℓ : B.Leaves} {q q' : B.DecNode}
    (hne : q ≠ q') (hq : q ∈ dNodesOn B d ℓ) (hq' : q' ∈ dNodesOn B d ℓ) : 2 ≤ count d B ℓ := by
  rw [count_eq_card_dNodesOn]
  have hsub : ({q, q'} : Finset B.DecNode) ⊆ dNodesOn B d ℓ := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hq
    · exact hq'
  calc 2 = ({q, q'} : Finset B.DecNode).card := (Finset.card_pair_eq_two_iff.mpr hne).symm
    _ ≤ _ := Finset.card_le_card hsub

end plumbing

/-! ## The per-leaf congruence and the aggregate identities -/

section c2b

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
  (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- **The per-leaf congruence behind Open 11.** At a subtree-veridical `d`-node `q`, for a leaf `ℓ`
below `q`, the forced law `p[q ↦ δ_a]` is the same under `C` and under `C' := C[d ↦ m']` (`m'`
full-support), provided `B` records at `d` for `C'`: a leaf whose path meets a second `d`-node is
`C'`-null by Definition 7's exactly-one clause (it lies in `O_d`), hence null under both forced laws
(the vanishing weights are chance weights or non-`d` draws, which `C` shares); a leaf whose path
meets no other `d`-node sees the same weights under both laws.
Source: `repair/C1.md` Open 11 (the route recorded in the first pass's `c2B_of_recordsForDeviations_open`);
`C2.md` line 56 ("the `O_d`-runs are unchanged except for the draw at the recorded node"); mandate T6
Kind: P
Fidelity: exact
Hyps: (a) `∀ b, 0 < m'(b)`, (a) `RecordsFor obs actEv (C[d↦m']) B d`, (a) `SubtreeVeridical obs B q` -/
theorem leafLawNode_forced_eq_of_recordsFor {d : ι} {m' : FinDistr K (acts d)}
    (hm' : ∀ b, 0 < m'.w b) (hrec : RecordsFor obs actEv (C.deviate d m') B d) {q : B.DecNode}
    (hq : pt B q = d) (hsv : SubtreeVeridical obs B q) (a : acts (pt B q)) {ℓ : B.Leaves}
    (hℓ : (edgeOf B q ℓ).isSome) :
    leafLawNode B ((NodePolicy.ofProc C B).update q (FinDistr.pure a)) ℓ =
      leafLawNode B ((NodePolicy.ofProc (C.deviate d m') B).update q (FinDistr.pure a)) ℓ := by
  subst hq
  set C' := C.deviate (pt B q) m' with hC'
  have hC'd : ∀ (e : ι) (b : acts e), e = pt B q → 0 < (C' e).w b := by
    rintro e b rfl
    rw [hC', Proc.deviate_same]; exact hm' b
  have hoff : ∀ e, e ≠ pt B q → C' e = C e := fun e he => by rw [hC', Proc.deviate_ne C m' he]
  have hbelow : ℓ ∈ leavesBelow B q := by
    unfold leavesBelow; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hℓ⟩
  by_cases hex : ∃ q', q' ≠ q ∧ pt B q' = pt B q ∧ (edgeOf B q' ℓ).isSome
  · obtain ⟨q', hne, hq', he'⟩ := hex
    have hnull : leafLaw C' B ℓ = 0 := by
      by_contra hne0
      have hpos : 0 < leafLaw C' B ℓ := lt_of_le_of_ne (leafLaw_nonneg C' B ℓ) (Ne.symm hne0)
      have hobs : world B ℓ ∈ obs (pt B q) := hsv ℓ hbelow
      have h1 := (hrec ℓ hpos hobs).1
      have h2 := two_le_count_of_ne B (Ne.symm hne) ((mem_dNodesOn B _ ℓ q).mpr ⟨rfl, hℓ⟩)
        ((mem_dNodesOn B _ ℓ q').mpr ⟨hq', he'⟩)
      omega
    have hnull' : leafLawNode B (NodePolicy.ofProc C' B) ℓ = 0 := by
      rw [leafLawNode_ofProc]; exact hnull
    have key : ∀ (D : Proc ι acts K), (∀ e, e ≠ pt B q → D e = C' e) →
        leafLawNode B ((NodePolicy.ofProc D B).update q (FinDistr.pure a)) ℓ = 0 := by
      intro D hD
      refine leafLawNode_eq_zero_mono B _ _ ℓ ?_ hnull'
      intro q'' b _ hz
      by_cases hqq : q'' = q
      · subst hqq
        exact absurd hz (hC'd _ b rfl).ne'
      · rw [NodePolicy.update_of_ne _ hqq]
        by_cases hd : pt B q'' = pt B q
        · exact absurd hz (hC'd _ b hd).ne'
        · show (D (pt B q'')).w b = 0
          rw [hD _ hd]; exact hz
    rw [key C (fun e he => (hoff e he).symm), key C' (fun _ _ => rfl)]
  · refine leafLawNode_congr_path B _ _ ℓ ?_
    intro q'' hq''
    by_cases hqq : q'' = q
    · subst hqq; simp only [NodePolicy.update_self]
    · rw [NodePolicy.update_of_ne _ hqq, NodePolicy.update_of_ne _ hqq]
      show C (pt B q'') = C' (pt B q'')
      have hd : pt B q'' ≠ pt B q := fun h => hex ⟨q'', hqq, h, hq''⟩
      exact (hoff _ hd).symm

/-- **`forcedBelow` at a subtree-veridical `d`-node is label-free** across a full-support deviation
for which `B` records: `G_q`'s numerator under `C` equals its numerator under `C[d↦m']`.
Source: `repair/C1.md` Open 11; mandate T6
Kind: P
Fidelity: exact
Hyps: (a) as `leafLawNode_forced_eq_of_recordsFor` -/
theorem forcedBelow_eq_deviate_of_recordsFor {d : ι} {m' : FinDistr K (acts d)}
    (hm' : ∀ b, 0 < m'.w b) (hrec : RecordsFor obs actEv (C.deviate d m') B d) {q : B.DecNode}
    (hq : pt B q = d) (hsv : SubtreeVeridical obs B q) (a : acts (pt B q)) :
    forcedBelow B (NodePolicy.ofProc C B) q a =
      forcedBelow B (NodePolicy.ofProc (C.deviate d m') B) q a := by
  unfold forcedBelow
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  rw [leafLawNode_forced_eq_of_recordsFor obs actEv C B hm' hrec hq hsv a
    (by unfold leavesBelow at hℓ; exact (Finset.mem_filter.mp hℓ).2)]

/-- **`R_q` at a subtree-veridical `d`-node is label-free** across a full-support deviation for
which `B` records (no `d`-node lies above `q` on a `C[d↦m']`-positive path).
Source: `repair/C1.md` Open 11; mandate T6
Kind: P
Fidelity: exact
Hyps: (a) as `leafLawNode_forced_eq_of_recordsFor` -/
theorem reach_eq_deviate_of_recordsFor {d : ι} {m' : FinDistr K (acts d)}
    (hm' : ∀ b, 0 < m'.w b) (hrec : RecordsFor obs actEv (C.deviate d m') B d) {q : B.DecNode}
    (hq : pt B q = d) (hsv : SubtreeVeridical obs B q) :
    reach C B q = reach (C.deviate d m') B q := by
  let a₀ : acts (pt B q) := Classical.arbitrary _
  rw [← reachNode_ofProc, ← reachNode_ofProc,
    ← reachNode_update_self B (NodePolicy.ofProc C B) q (FinDistr.pure a₀),
    ← reachNode_update_self B (NodePolicy.ofProc (C.deviate d m') B) q (FinDistr.pure a₀),
    reachNode_eq_sum_leavesBelow, reachNode_eq_sum_leavesBelow]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  exact leafLawNode_forced_eq_of_recordsFor obs actEv C B hm' hrec hq hsv a₀
    (by unfold leavesBelow at hℓ; exact (Finset.mem_filter.mp hℓ).2)

/-- **The real fiber's forced mass is label-free** under F3′ structural (its first clause: real-fiber
nodes are subtree-veridical) and recording for one full-support deviation.
Source: `repair/C1.md` Open 11; mandate T6
Kind: C -/
theorem realForced_eq_deviate_of_recordsFor {d : ι} (hS : ActRecordingStructural obs actEv B d)
    {m' : FinDistr K (acts d)} (hm' : ∀ b, 0 < m'.w b)
    (hrec : RecordsFor obs actEv (C.deviate d m') B d) (a : acts d) :
    realForced actEv C B d a = realForced actEv (C.deviate d m') B d a := by
  unfold realForced
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [mem_realFiber] at hq
  split_ifs with h
  · exact forcedBelow_eq_deviate_of_recordsFor obs actEv C B hm' hrec h
      ((hS.actRecording C).1 q h hq.2) _
  · rfl

/-- **The real fiber's reach is label-free** under the same hypotheses.
Source: `repair/C1.md` Open 11; mandate T6
Kind: C -/
theorem realReach_eq_deviate_of_recordsFor {d : ι} (hS : ActRecordingStructural obs actEv B d)
    {m' : FinDistr K (acts d)} (hm' : ∀ b, 0 < m'.w b)
    (hrec : RecordsFor obs actEv (C.deviate d m') B d) :
    realReach actEv C B d = realReach actEv (C.deviate d m') B d := by
  unfold realReach
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [mem_realFiber] at hq
  exact reach_eq_deviate_of_recordsFor obs actEv C B hm' hrec hq.1
    ((hS.actRecording C).1 q hq.1 hq.2)

/-- **The open step of Open 11**: `refR2Real` at the label in play equals `refR2Real` at any
full-support deviation `C[d↦m']` for which `B` records at `d` — with no positivity assumed (at a null
real-fiber reach both sides are the junk `0`; the guarded reading is `0 < realReach`).
Source: `repair/C1.md` Open 11 (the step named open in the first pass); mandate T6
Kind: P
Fidelity: exact
Hyps: (a) `ActRecordingStructural` (first clause only), (a) `∀ b, 0 < m'(b)`,
(a) `RecordsFor obs actEv (C[d↦m']) B d` -/
theorem refR2Real_eq_refR2Real_deviate_of_recordsFor {d : ι}
    (hS : ActRecordingStructural obs actEv B d) {m' : FinDistr K (acts d)} (hm' : ∀ b, 0 < m'.w b)
    (hrec : RecordsFor obs actEv (C.deviate d m') B d) (a : acts d) :
    refR2Real actEv C B d a = refR2Real actEv (C.deviate d m') B d a := by
  unfold refR2Real
  rw [realForced_eq_deviate_of_recordsFor obs actEv C B hS hm' hrec,
    realReach_eq_deviate_of_recordsFor obs actEv C B hS hm' hrec]

/-- C2-B′ at a full-support label under recording for *that* deviation only (the first pass's
`refR1State_eq_refR2Real_deviate_of_fullSupport` used `RecordsForDeviations` but only at `m`).
Source: `C2.md` line 54; `repair/C1.md` Open 11; mandate T6
Kind: C
Fidelity: exact for full-support labels
Hyps: (a) `ActRecordingStructural`, (a) disjointness, (a) `RecordsFor obs actEv (C[d↦m]) B d`,
(a) `∀ a, 0 < m(a)` -/
theorem refR1State_eq_refR2Real_deviate_of_recordsFor {d : ι}
    (hS : ActRecordingStructural obs actEv B d) (hdisj : ActEvDisjoint actEv d)
    {m : FinDistr K (acts d)} (hrec : RecordsFor obs actEv (C.deviate d m) B d)
    (hm : ∀ a, 0 < m.w a) (a : acts d) :
    refR1State obs C B d a = refR2Real actEv (C.deviate d m) B d a := by
  have hA : ActRecording obs actEv (C.deviate d m) B d := hS.actRecording _
  have hma : 0 < ((C.deviate d m) d).w a := by rw [Proc.deviate_same]; exact hm a
  have hν := nu_deviatePure_obs_mul obs actEv (C.deviate d m) B hrec hma
  have hp := paySum_deviatePure_obs_mul obs actEv (C.deviate d m) B hrec hma
  rw [nu_actEv_inter_obs_eq obs actEv _ B hA hdisj a] at hν
  rw [paySum_actEv_inter_obs_eq obs actEv _ B hA hdisj a] at hp
  unfold Proc.deviatePure at hν hp
  rw [deviate_deviate'] at hν hp
  have hν' : nu (C.deviate d (FinDistr.pure a)) B (obs d) = realReach actEv (C.deviate d m) B d :=
    mul_right_cancel₀ hma.ne' (by rw [hν]; ring)
  have hp' : paySum (C.deviate d (FinDistr.pure a)) B (obs d) =
      realForced actEv (C.deviate d m) B d a :=
    mul_right_cancel₀ hma.ne' (by rw [hp]; ring)
  unfold refR1State condExp refR2Real Proc.deviatePure
  rw [hν', hp']

/-- **Open 11, closed — Theorem C2-B′ at the label in play, under recording for the uniform
deviation alone**: at an F3′-structural point with Definition 3's disjointness, if `B` records at
`d` (Definition 7) for `C[d ↦ unif]`, then `refR1State a = refR2Real a` at `C` itself, for every
act `a` — with no positivity assumed (at a null denominator both sides are the junk `0`; the guarded
reading carries `0 < ν_{C[d↦a]}(O_d)`, under which `refR1State a` is the genuine `O_d`-conditioned
deviation value). The hypothesis is strictly weaker than the `RecordsForDeviations` the source asks
for (next theorem) and than the `RecordsForAll` of `refR1State_eq_refR2Real_of_recordsForAll`.
Source: `C2.md` line 54 (Theorem C2-B′, WOUNDED form); `repair/C1.md` Open 11; dp-sl-026; dp-sl-073;
mandate T6
Kind: C
Fidelity: stronger: recording for one full-support deviation in place of "for every `C[d↦m]`"
Hyps: (a) `ActRecordingStructural`, (a) disjointness, (a) `RecordsFor obs actEv (C[d↦unif]) B d` -/
theorem c2B_of_recordsFor_uniform {d : ι} (hS : ActRecordingStructural obs actEv B d)
    (hdisj : ActEvDisjoint actEv d)
    (hrec : RecordsFor obs actEv (C.deviate d FinDistr.uniform) B d) (a : acts d) :
    refR1State obs C B d a = refR2Real actEv C B d a := by
  rw [refR1State_eq_refR2Real_deviate_of_recordsFor obs actEv C B hS hdisj hrec
      (fun b => FinDistr.uniform_w_pos b) a,
    ← refR2Real_eq_refR2Real_deviate_of_recordsFor obs actEv C B hS
      (fun b => FinDistr.uniform_w_pos b) hrec a]

/-- **Theorem C2-B′ under `RecordsForDeviations` (Open 11 as asked)**: C2-A′'s structural
hypotheses and Definition 7 recording for `C` and every `C[d ↦ m]` give `refR1State a = refR2Real a`
at `C` itself.
Source: `C2.md` line 54 (Theorem C2-B′, WOUNDED form: "records at `d` in Definition 7's sense for
every `C[d ↦ m]`"); `repair/C1.md` Open 11; dp-sl-073; mandate T6
Kind: C
Fidelity: exact (the WOUNDED form's quantifier)
Hyps: (a) `ActRecordingStructural`, (a) disjointness, (a) `RecordsForDeviations` -/
theorem c2B_of_recordsForDeviations {d : ι} (hS : ActRecordingStructural obs actEv B d)
    (hdisj : ActEvDisjoint actEv d) (hdev : RecordsForDeviations obs actEv C B d) (a : acts d) :
    refR1State obs C B d a = refR2Real actEv C B d a :=
  c2B_of_recordsFor_uniform obs actEv C B hS hdisj (hdev _) a

/-- **Label-freedom under `RecordsForDeviations`**: `refR2Real` at every label `m` is the label-free
`refR1State` of `C` — no positivity needed (the `RecordsForAll` version
`refR2Real_deviate_eq_refR1State` carried two positivity guards).
Source: `C2.md` line 54 (Theorem C2-B′: "the common value `v_d(a)` does not depend on `C(d)`");
mandate T6
Kind: C
Fidelity: exact
Hyps: (a) `ActRecordingStructural`, (a) disjointness, (a) `RecordsForDeviations` -/
theorem refR2Real_deviate_eq_refR1State_of_recordsForDeviations {d : ι}
    (hS : ActRecordingStructural obs actEv B d) (hdisj : ActEvDisjoint actEv d)
    (hdev : RecordsForDeviations obs actEv C B d) (m : FinDistr K (acts d)) (a : acts d) :
    refR2Real actEv (C.deviate d m) B d a = refR1State obs C B d a := by
  have hdev' : RecordsForDeviations obs actEv (C.deviate d m) B d := by
    intro m'; rw [deviate_deviate']; exact hdev m'
  rw [← c2B_of_recordsForDeviations obs actEv (C.deviate d m) B hS hdisj hdev' a]
  unfold refR1State Proc.deviatePure
  rw [deviate_deviate']

variable (s : ι → State Ω K)

/-- **C2-B′, the fixed face, under `RecordsForDeviations`**: `T_EDT`(R3-extended) approves
`C[d ↦ m]` iff `supp m ⊆ argmax_a v_d(a)` with the label-free `v_d := refR1State obs C B d`.
Source: `C2.md` line 54 (Theorem C2-B′: "the calibrated-and-approved set is the fixed face"); mandate T6
Kind: C
Fidelity: exact
Hyps: (a) `ActRecordingStructural`, (a) disjointness, (a) `RecordsForDeviations`,
(a) `0 < ν_{C[d↦m]}(O_d)`, (a) `StrictOCAt` for `C[d↦m]` -/
theorem tEdtExtAt_deviate_iff_fixedFace_of_recordsForDeviations {d : ι}
    (hS : ActRecordingStructural obs actEv B d) (hdisj : ActEvDisjoint actEv d)
    (hdev : RecordsForDeviations obs actEv C B d) (m : FinDistr K (acts d))
    (hpm : 0 < nu (C.deviate d m) B (obs d)) (hs : StrictOCAt s obs (C.deviate d m) B d) :
    TEdtExtAt s obs actEv (C.deviate d m) B d ↔
      ∀ a, 0 < m.w a → ∀ b, refR1State obs C B d b ≤ refR1State obs C B d a := by
  unfold TEdtExtAt
  simp only [evExt_eq_refR2Real s obs actEv (C.deviate d m) B hS hdisj hpm hs,
    refR2Real_deviate_eq_refR1State_of_recordsForDeviations obs actEv C B hS hdisj hdev m,
    Proc.deviate_same]

/-- **No properly mixed label is forced, under `RecordsForDeviations`**: an approved label with
`a, b` in its support has `v_d(a) = v_d(b)`.
Source: `C2.md` line 54 (Theorem C2-B′: "no mixed label is forced"); mandate T6
Kind: C
Fidelity: exact
Hyps: (a) as `tEdtExtAt_deviate_iff_fixedFace_of_recordsForDeviations` -/
theorem tie_of_approved_mixed_of_recordsForDeviations {d : ι}
    (hS : ActRecordingStructural obs actEv B d) (hdisj : ActEvDisjoint actEv d)
    (hdev : RecordsForDeviations obs actEv C B d) (m : FinDistr K (acts d))
    (hpm : 0 < nu (C.deviate d m) B (obs d)) (hs : StrictOCAt s obs (C.deviate d m) B d)
    (happ : TEdtExtAt s obs actEv (C.deviate d m) B d) {a b : acts d} (ha : 0 < m.w a)
    (hb : 0 < m.w b) : refR1State obs C B d a = refR1State obs C B d b := by
  rw [tEdtExtAt_deviate_iff_fixedFace_of_recordsForDeviations obs actEv C B s hS hdisj hdev m hpm
    hs] at happ
  exact le_antisymm (happ b hb a) (happ a ha b)

end c2b

end Cleanroom.Decision.DpReferentsCdt

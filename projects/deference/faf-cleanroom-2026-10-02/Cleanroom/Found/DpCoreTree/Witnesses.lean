import Cleanroom.Found.DpCoreTree.Catalogue
import Cleanroom.Found.DpCoreTree.Seed
import Cleanroom.Found.DpCoreTree.Occurrence
import Mathlib.Tactic.Ring

/-!
# Witnesses on the catalogue trees

Non-vacuity witnesses (N+/N−) for T3, T4, T5 and T7 of [[dp-core-tree-mandate]], all computed
from `leafLaw` on the catalogue definitions (never taken as `def`s):

* **T3** — the mugging `B₁` is almost fair (so the two semantics agree on it for every
  procedure); the AMD and Remark 4.3's miniature are nested, with `V = (1−q)(3q+1)` vs
  `V' = 1−q` (gap `3q(1−q)`, `4/3` vs `2/3` at `q = 1/3`) and `V = 3q(1−q)` vs `V' = 0`
  respectively — the miniature at the leaf-law level (its laws differ; its values differ too
  unless `q ∈ {0,1}`).
* **T4** — the routing root: `ν(O)` is `C(d)`-dependent (`= q`) and `ν(a ∩ O) = ν(O)` at
  `q = ½`, the selection-bias witness; `𝔼[#_d] = 1 + C(d)(b)` on the AMD.
* **T5** — tree J is recorded for `δ_a` and not for `δ_b` (so recording for `C` does not give
  recording for its deviations); the gate tree is recorded for every deviation at `d` of a
  procedure playing `a` at the gate `e`, but not for every procedure; opaque Newcomb is
  `ActRecording` for every procedure and `RecordsFor` for none.
* **T7** — the multiplicity term on the AMD is `3q(1−q)`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Found.DpCoreTree

open Finset Catalogue Tree

/-! ### General helpers -/

/-- Some leaf has positive mass.
Source: none: infrastructure
Kind: L -/
theorem Tree.exists_leafLaw_pos {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] [∀ d, Fintype (acts d)]
    (C : Proc ι acts K) (B : Tree Ω ι acts K) : ∃ ℓ, 0 < leafLaw C B ℓ := by
  by_contra h
  have h' : ∀ ℓ, leafLaw C B ℓ ≤ 0 := fun ℓ => not_lt.mp fun hℓ => h ⟨ℓ, hℓ⟩
  have : ∑ ℓ, leafLaw C B ℓ = 0 :=
    Finset.sum_eq_zero fun ℓ _ => le_antisymm (h' ℓ) (leafLaw_nonneg C B ℓ)
  rw [sum_leafLaw] at this
  exact one_ne_zero this

/-- The expected occurrence count `𝔼_μ[#_d]`.
Source: [[decision-problems-v2]] §3.1 after Lemma 1 ("the per-occurrence normalizer
`𝔼_μ[#_d]`"); §8 (`∑_{q : d_q = d} R_q = 𝔼_μ[#_d]`)
Kind: D -/
def Tree.expCount {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [DecidableEq ι]
    (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) : K :=
  ∑ ℓ, leafLaw C B ℓ * (count d B ℓ : K)

/-! ### T3: the AMD, the miniature, the mugging -/

/-- `V_{AMD}(C) = (1 − q)(3q + 1)` under Definition 6, `q := C(d)(a)`.
Source: `seeds.md` SE-2 Corollary ("AMD: `V(q) = (1−q)(3q+1)`")
Kind: N+ -/
theorem amd_value (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (procQ q h0 h1) amd = (1 - q) * (3 * q + 1) := by
  unfold value amd
  rw [sum_leaves_decision, Act2.sum_univ]
  simp only [leafLaw_decision, payoff_decision]
  rw [Tree.sum_leaves_leaf, sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf,
    Tree.sum_leaves_leaf]
  simp only [leafLaw_decision, payoff_decision, leafLaw_leaf, payoff_leaf, procQ,
    FinDistr.act2_a, FinDistr.act2_b]
  ring

/-- `V'_{AMD}(C) = 1 − q` under Definition 6′.
Source: `seeds.md` SE-1(b) ("AMD: `V'(q) = 1−q`"), SE-2 Corollary
Kind: N+ -/
theorem amd_value' (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value' (procQ q h0 h1) amd = 1 - q := by
  unfold value' amd
  rw [sum_leaves_decision, Act2.sum_univ]
  rw [Tree.sum_leaves_leaf, sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf,
    Tree.sum_leaves_leaf]
  simp only [leafLaw'_eq, draws_decision, draws_leaf, chanceWeight_decision,
    chanceWeight_leaf, payoff_decision, payoff_leaf, seedFold, Function.update_self, procQ,
    FinDistr.act2_a, FinDistr.act2_b]
  simp

/-- **The AMD gap**: `V − V' = 3q(1 − q)`.
Source: `seeds.md` SE-2 Corollary ("gap `3q(1−q)`")
Kind: N+ -/
theorem amd_gap (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (procQ q h0 h1) amd - value' (procQ q h0 h1) amd = 3 * q * (1 - q) := by
  rw [amd_value, amd_value']; ring

/-- **The multiplicity term on the AMD is `3q(1 − q)`** (T7 witness).
Source: dp-cf-2-055 ("`= 3x(1−x)` on Prop 5(c)")
Kind: N+ -/
theorem amd_multiplicityTerm (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    multiplicityTerm (procQ q h0 h1) amd = 3 * q * (1 - q) := by
  rw [multiplicityTerm_eq_value_sub_value', amd_gap]

/-- At `q = 1/3`: `V = 4/3`, `V' = 2/3`.
Source: `seeds.md` SE-2 Corollary ("at `q = 1/3`: `4/3` vs `2/3`")
Kind: N+ -/
theorem amd_at_third :
    value (procQ (1/3) (by norm_num) (by norm_num)) amd = 4/3 ∧
      value' (procQ (1/3) (by norm_num) (by norm_num)) amd = 2/3 := by
  rw [amd_value, amd_value']; norm_num

/-- The AMD is nested at its point (the SE-2 (⇒) hypothesis is inhabited).
Source: `seeds.md` SE-2 ("nested rows: … AMD")
Kind: N+ -/
theorem amd_nested : Nested amd () := by
  refine ⟨by decide, ⟨.b, ⟨.a, ()⟩⟩, ?_, ?_⟩
  · unfold Positive amd; simp
  · unfold amd; simp

/-- `𝔼[#_d] = 1 + C(d)(b)` on the AMD: the per-occurrence normaliser moves under deviation.
Source: [[decision-problems-v2]] §3.1 after Lemma 1 ("`𝔼_μ[#_d] = 1 + C(d)(b)` in Proposition
5(c)'s miniature")
Kind: N+ -/
theorem amd_expCount (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    expCount (procQ q h0 h1) amd () = 1 + (1 - q) := by
  unfold expCount amd
  rw [sum_leaves_decision, Act2.sum_univ]
  rw [Tree.sum_leaves_leaf, sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf,
    Tree.sum_leaves_leaf]
  simp only [leafLaw_decision, leafLaw_leaf, count_decision, count_leaf, procQ,
    FinDistr.act2_a, FinDistr.act2_b]
  simp
  ring

/-- `V_{mini}(C) = 3q(1 − q)` under Definition 6.
Source: [[decision-problems-v2]] Remark 4.3 (`V_{s_d}(a) = 2(1−q)`, `V_{s_d}(b) = q`, so
`V = q·2(1−q) + (1−q)·q`); mandate T3 ("`V = 3q(1−q)`")
Kind: N+ -/
theorem miniature_value (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (procQ q h0 h1) miniature = 3 * q * (1 - q) := by
  unfold value miniature
  rw [sum_leaves_decision, Act2.sum_univ, sum_leaves_decision, Act2.sum_univ,
    sum_leaves_decision, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf]
  simp only [leafLaw_decision, leafLaw_leaf, payoff_decision, payoff_leaf,
    procQ, FinDistr.act2_a, FinDistr.act2_b, miniPay]
  ring

/-- `V'_{mini}(C) = 0` under Definition 6′ (the seed forces sample = live, which pays `0`).
Source: mandate T3 ("Remark 4.3 miniature: `V = 3q(1−q)` vs `V' ≡ 0`"); dp-sl-006
Kind: N+ -/
theorem miniature_value' (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value' (procQ q h0 h1) miniature = 0 := by
  unfold value' miniature
  rw [sum_leaves_decision, Act2.sum_univ, sum_leaves_decision, Act2.sum_univ,
    sum_leaves_decision, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf]
  simp only [leafLaw'_eq, draws_decision, draws_leaf,
    chanceWeight_decision, chanceWeight_leaf, payoff_decision, payoff_leaf, seedFold,
    Function.update_self, procQ, FinDistr.act2_a, FinDistr.act2_b, miniPay]
  simp

/-- The miniature is nested.
Source: `seeds.md` SE-2 ("Remark 4.3's miniature")
Kind: N+ -/
theorem miniature_nested : Nested miniature () := by
  refine ⟨by decide, ⟨.a, ⟨.b, ()⟩⟩, ?_, ?_⟩
  · unfold Positive miniature; simp
  · unfold miniature; simp

/-- **Leaf-law level separation on the miniature**: at `q = ½` the leaf (sample `a`, live `b`)
has Definition-6 mass `¼` and shared-seed mass `0`.
Source: mandate T3 (the nested N+ at the leaf-law level); §6 item 7
Kind: N+ -/
theorem miniature_leaf_separation :
    leafLaw (procQ (1/2) (by norm_num) (by norm_num)) miniature ⟨.a, ⟨.b, ()⟩⟩ = 1/4 ∧
      leafLaw' (procQ (1/2) (by norm_num) (by norm_num)) miniature ⟨.a, ⟨.b, ()⟩⟩ = 0 := by
  constructor
  · unfold miniature
    simp only [leafLaw_decision, leafLaw_leaf, procQ, FinDistr.act2_a, FinDistr.act2_b]
    norm_num
  · unfold miniature
    simp only [leafLaw'_eq, draws_decision, draws_leaf, chanceWeight_decision, chanceWeight_leaf,
      seedFold, Function.update_self, procQ, FinDistr.act2_a, FinDistr.act2_b]
    simp

/-- **`B₁` is almost fair**: every path meets `d` exactly once.
Source: `seeds.md` SE-2 Corollary; `faithful.md` FA-4 ("almost-fair single-point trees")
Kind: N+ -/
theorem mug1_almostFair (x y : ℚ) : AlmostFair (mug1 x y) := by
  rintro d ⟨i, ⟨a, ℓ⟩⟩
  unfold mug1
  simp

/-- Hence on `B₁` the two semantics agree for every procedure (the N+ for SE-2 (⇐) on a tree
with a chance node, a real and a hypothetical query).
Source: `seeds.md` SE-2 Corollary
Kind: N+ -/
theorem mug1_agreement (x y : ℚ) (C : Proc Unit (fun _ => Act2) ℚ) (ℓ : (mug1 x y).Leaves) :
    leafLaw C (mug1 x y) ℓ = leafLaw' C (mug1 x y) ℓ :=
  (mug1_almostFair x y).leafLaw_eq_leafLaw' C ℓ

/-! ### T4: the routing root -/

/-- On the routing root `ν(O) = C(d)(a)`: the observation event's mass **does** depend on `C(d)`.
Source: [[decision-problems-v2]] Lemma 1 ("although `ν_{B,C}(O_d)` in general does"), Remark 3.4
Kind: N+ -/
theorem routingRoot_nu_obs (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    nu (procQ q h0 h1) routingRoot (routeObs ()) = q := by
  unfold nu mass worldEv routingRoot routeObs
  rw [Finset.sum_filter, sum_leaves_decision, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf, leafLaw_decision, leafLaw_leaf, world_decision, world_leaf,
    procQ, FinDistr.act2_a, FinDistr.act2_b]
  simp

/-- **Selection bias at the routing root**: at `C(d) = (½, ½)`, `ν(a ∩ O) = ν(O)` (so
`ν(a ∣ O) = 1 ≠ ½ = C(d)(a)`).
Source: [[decision-problems-v2]] Remark 3.4 ("with `C(d) = (½, ½)` there, `ν(a ∣ O) = 1 ≠ ½`")
Kind: N+ -/
theorem routingRoot_selection_bias :
    nu (procQ (1/2) (by norm_num) (by norm_num)) routingRoot (routeActEv () .a ∩ routeObs ()) =
      nu (procQ (1/2) (by norm_num) (by norm_num)) routingRoot (routeObs ()) ∧
    nu (procQ (1/2) (by norm_num) (by norm_num)) routingRoot (routeObs ()) = 1/2 := by
  refine ⟨?_, routingRoot_nu_obs _ _ _⟩
  unfold nu mass worldEv routingRoot routeObs routeActEv
  rw [Finset.sum_filter, Finset.sum_filter, sum_leaves_decision, sum_leaves_decision,
    Act2.sum_univ, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf, leafLaw_decision, leafLaw_leaf, world_decision, world_leaf,
    procQ, FinDistr.act2_a, FinDistr.act2_b]
  simp

/-! ### T5: tree J, the gate tree, opaque Newcomb -/

/-- **Tree J is recorded at `d` for `δ_a`.**
Source: `sl-synthesis.md` line 121 ("tree J … is Def-7-recorded for `δ_a`")
Kind: N+ -/
theorem treeJ_recordsFor_a :
    RecordsFor jObs jActEv (procQ 1 (by norm_num) (by norm_num)) treeJ () := by
  unfold treeJ
  intro ℓ hpos hobs
  rcases ℓ with ⟨_ | _, ℓ⟩
  · refine ⟨rfl, ?_⟩
    rintro (_ | ⟨_ | _, q⟩) hq a ha
    · simp only [edgeOf_decision_none, Option.some.injEq] at ha
      subst ha
      refine ⟨?_, ?_, ?_⟩
      · intro ℓ' _; simp [jObs]
      · simp [jActEv]
      · intro a' ha'; cases a' <;> simp_all [jActEv]
    · exact q.elim
    · simp [edgeOf_decision_some] at ha
  · exfalso
    simp [procQ] at hpos

/-- **Tree J is not recorded at `d` for `δ_b`**: the run `b, b` (mass `1` under `δ_b`) meets
`d` twice.
Source: `sl-synthesis.md` line 121 ("… yet not for `δ_b`"; C2-B′)
Kind: N+ -/
theorem treeJ_not_recordsFor_b :
    ¬ RecordsFor jObs jActEv (procQ 0 (by norm_num) (by norm_num)) treeJ () := by
  intro h
  have := (h ⟨.b, ⟨.b, ()⟩⟩ (by unfold treeJ; simp [procQ]) (by simp [jObs])).1
  exact absurd this (by decide)

/-- **Recording for `C` does not give recording for every deviation of `C`** (tree J).
Source: `sl-synthesis.md` line 20 ("the three come apart: C2-B′"); mandate T5
Kind: N+ -/
theorem treeJ_recordsFor_not_recordsForDeviations :
    RecordsFor jObs jActEv (procQ 1 (by norm_num) (by norm_num)) treeJ () ∧
      ¬ RecordsForDeviations jObs jActEv (procQ 1 (by norm_num) (by norm_num)) treeJ () := by
  refine ⟨treeJ_recordsFor_a, fun h => treeJ_not_recordsFor_b ?_⟩
  have := h (FinDistr.act2 0 (by norm_num) (by norm_num))
  have heq : (procQ 1 (by norm_num) (by norm_num) : Proc Unit (fun _ => Act2) ℚ).deviate ()
      (FinDistr.act2 0 (by norm_num) (by norm_num)) = procQ 0 (by norm_num) (by norm_num) := by
    funext d; cases d; simp [Proc.deviate, procQ]
  rwa [heq] at this

/-- The gate procedure: `(qe, 1−qe)` at the gate `e`, `(qd, 1−qd)` at `d`.
Source: mandate T5
Kind: D -/
def gateProc (qe : ℚ) (e0 : 0 ≤ qe) (e1 : qe ≤ 1) (qd : ℚ) (d0 : 0 ≤ qd) (d1 : qd ≤ 1) :
    Proc GatePt (fun _ => Act2) ℚ
  | .e => FinDistr.act2 qe e0 e1
  | .d => FinDistr.act2 qd d0 d1

/-- **The gate tree is recorded at `d` for every deviation at `d`** of a procedure playing `a`
at the gate (the deviation keeps `e ↦ a`, so `d` is met exactly once on every positive run).
Source: mandate T5 ("a two-point tree where a point `e`'s answer decides whether `d` is met
twice (`C[d↦m]` keeps `e` fixed)")
Kind: N+ -/
theorem gate_recordsForDeviations (qd : ℚ) (d0 : 0 ≤ qd) (d1 : qd ≤ 1) :
    RecordsForDeviations gateObs gateActEv (gateProc 1 (by norm_num) (by norm_num) qd d0 d1)
      gate .d := by
  intro m
  unfold gate
  intro ℓ hpos hobs
  rcases ℓ with ⟨_ | _, ℓ⟩
  · rcases ℓ with ⟨x, ℓ⟩
    refine ⟨rfl, ?_⟩
    intro q hq a ha
    rcases q with _ | ⟨_ | _, _ | ⟨y, q⟩⟩
    · simp at hq
    · simp only [edgeOf_decision_some, dite_true, edgeOf_decision_none, Option.some.injEq] at ha
      subst ha
      refine ⟨?_, ?_, ?_⟩
      · intro ℓ' _; simp [gateObs]
      · simp [gateActEv]
      · intro a' ha'; cases a' <;> cases x <;> simp_all [gateActEv]
    · exact q.elim
    · simp [edgeOf_decision_some] at ha
    · simp [edgeOf_decision_some] at ha
  · exfalso
    simp [Proc.deviate, gateProc] at hpos

/-- **The gate tree is not recorded at `d` for every procedure**: a procedure playing `b` at the
gate meets `d` twice on a positive run.
Source: mandate T5
Kind: N+ -/
theorem gate_not_recordsForAll : ¬ RecordsForAll gateObs gateActEv gate .d := by
  intro h
  have := (h (gateProc 0 (by norm_num) (by norm_num) 1 (by norm_num) (by norm_num))
    ⟨.b, ⟨.a, ⟨.a, ()⟩⟩⟩ (by unfold gate; simp [gateProc]) (by simp [gateObs])).1
  exact absurd this (by decide)

/-- **Recording for every deviation does not give recording for every procedure** (gate tree).
Source: `sl-synthesis.md` line 20; mandate T5
Kind: N+ -/
theorem gate_recordsForDeviations_not_recordsForAll :
    RecordsForDeviations gateObs gateActEv
      (gateProc 1 (by norm_num) (by norm_num) (1/2) (by norm_num) (by norm_num)) gate .d ∧
      ¬ RecordsForAll gateObs gateActEv gate .d :=
  ⟨gate_recordsForDeviations _ _ _, gate_not_recordsForAll⟩

/-- Every path of opaque Newcomb meets `d` exactly twice.
Source: dp-sl-2-041 ("every `O_d`-run passes two `d`-nodes")
Kind: L -/
theorem opaqueNewcomb_count (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ)
    (ℓ : (opaqueNewcomb p h0 h1 L S).Leaves) : count () (opaqueNewcomb p h0 h1 L S) ℓ = 2 := by
  unfold opaqueNewcomb at ℓ ⊢
  rcases ℓ with ⟨s, i, l, _⟩
  rfl

/-- **Opaque Newcomb is `RecordsFor` for no procedure** (Definition 7's exactly-one clause
fails on every positive run).
Source: dp-sl-2-041 ("fails Definition 7's exactly-one clause")
Kind: N+ -/
theorem opaqueNewcomb_not_recordsFor (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ)
    (C : Proc Unit (fun _ => Act2) ℚ) :
    ¬ RecordsFor opaqueObs opaqueActEv C (opaqueNewcomb p h0 h1 L S) () := by
  intro h
  obtain ⟨ℓ, hℓ⟩ := Tree.exists_leafLaw_pos C (opaqueNewcomb p h0 h1 L S)
  have := (h ℓ hℓ (by simp [opaqueObs])).1
  rw [opaqueNewcomb_count] at this
  exact absurd this (by norm_num)

/-- **Opaque Newcomb is `ActRecording` for every procedure**: the live node is the unique
node-action-veridical `d`-node on every run (the predictor node is not: its `s`-edge leads to
worlds with either act). With `O_d = ⊤` every node is subtree-veridical, so F3′'s clause (i)
is not exercised here; the separation from Definition 7 is clause (ii) against "exactly one
`d`-node" (`opaqueNewcomb_count`).
Source: dp-sl-2-041 ("satisfies P12's own criterion for deterministic `C`"); `faithful.md` F3′
("opaque Newcomb real node — F3′ not Def 7")
Kind: N+ -/
theorem opaqueNewcomb_actRecording (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ)
    (C : Proc Unit (fun _ => Act2) ℚ) :
    ActRecording opaqueObs opaqueActEv C (opaqueNewcomb p h0 h1 L S) () := by
  refine ⟨fun q _ _ ℓ _ => by simp [opaqueObs], ?_⟩
  unfold opaqueNewcomb
  intro ℓ _ _
  rcases ℓ with ⟨s, i, l, _⟩
  -- the live node below the chance edge `i`
  refine ⟨some ⟨s, ⟨i, none⟩⟩, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, ?_⟩
      simp [edgeOf_decision_some, edgeOf_chance, edgeOf_decision_none]
    · intro ℓ' a ha
      rcases ℓ' with ⟨s', i', l', _⟩
      by_cases hs : s' = s
      · subst hs
        by_cases hi : i' = i
        · subst hi
          simp only [edgeOf_decision_some, dite_true, edgeOf_chance, edgeOf_decision_none,
            Option.some.injEq] at ha
          subst ha
          simp [opaqueActEv]
        · simp [edgeOf_decision_some, edgeOf_chance, hi] at ha
      · simp [edgeOf_decision_some, hs] at ha
  · rintro (_ | ⟨s', i', (_ | ⟨l', q⟩)⟩) ⟨hmem, hnav⟩
    · -- the predictor node is not node-action-veridical
      exfalso
      obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card (by decide : 1 < Fintype.card Act2) s
      have := hnav ⟨s, ⟨i, ⟨b, ()⟩⟩⟩ s (by simp [edgeOf_decision_none])
      simp [opaqueActEv] at this
      exact hb this
    · have hmem' := (Finset.mem_filter.mp hmem).2.2
      clear hmem hnav
      by_cases hs : s = s'
      · subst hs
        by_cases hi : i = i'
        · subst hi; rfl
        · simp [edgeOf_decision_some, edgeOf_chance, hi] at hmem'
      · simp [edgeOf_decision_some, hs] at hmem'
    · exact q.elim

end Cleanroom.Found.DpCoreTree

import Cleanroom.Decision.DpEdtUdtFair.DfTheorem
import Cleanroom.Decision.DpEdtUdtFair.Assignment

/-!
# CA-3′ on strongly fair trees, and the existence of DF self-models (CA-2′(i))

* **CA-3′ (the size argument).** On a strongly fair tree, `e` strictly below `d` forces every
  `e`-node's subtree to be strictly smaller than every `d`-node's
  (`stronglyFair_size_lt_of_strictlyBelow`: some `e`-node sits under some `d`-node, and `LabIso`
  preserves `size` across each fiber). Hence `StrictlyBelow` is irreflexive
  (`stronglyFair_not_strictlyBelow_self`) and **no ancestor point of a `d`-node is strictly
  below `d`** (`stronglyFair_not_strictlyBelow_of_mem_ancestorPts`) — the fact CA-2′(i) needs.
* **Reach positivity** (`reach_pos_of_pruned`): on a pruned tree a node is reached with positive
  probability by any procedure that is full-support at the node's ancestor points.
* **DF self-models exist at every point of `𝔉`** (`FairClass.exists_dfMasked`, CA-2′(i) "no point
  of `𝔉` is DF-free"): for any `C`, the self-model "`C` strictly below `d`, uniform elsewhere"
  realizes `O_d` (its ancestors are not strictly below `d`, so the realized `O_d`-run's `d`-node
  is reached) and the calibrated state satisfies the strict clauses.
* Corollaries: a **DF-`T_EDT`-consistent deterministic procedure exists on every `B ∈ 𝔉`**
  (`FairClass.exists_dfMasked_tEdt_ofFun`, the leaves-up argmax of `Q`), and **D2 implies
  DF-EDT-consistency as a statement about procedures** (`FairClass.dfMasked_tEdt_of_eventTremble`,
  CA-4′'s first inclusion `{D2} ⊆ {DF-EDT}`).
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

/-! ### CA-3′: the size argument -/

section ca3

omit [Fintype Ω] [DecidableEq Ω] [∀ d, DecidableEq (acts d)] [DecidableEq ι] in
/-- An ancestor point of `q` is carried by a node with a strictly larger subtree.
Source: none: infrastructure (CA-3′'s size argument)
Kind: L -/
theorem exists_node_gt_of_mem_ancestorPts :
    (B : Tree Ω ι acts K) → ∀ (q : B.DecNode) (e : ι), e ∈ ancestorPts B q →
      ∃ q' : B.DecNode, pt B q' = e ∧ size (subtreeAt B q) < size (subtreeAt B q')
  | leaf _ _, q, _, _ => q.elim
  | chance _ β child, ⟨i, q⟩, e, he => by
      obtain ⟨q', hq', hlt⟩ := exists_node_gt_of_mem_ancestorPts (child i) q e he
      exact ⟨⟨i, q'⟩, hq', hlt⟩
  | decision d' child, none, e, he => absurd he (List.not_mem_nil)
  | decision d' child, some ⟨a, q⟩, e, he => by
      rcases List.mem_cons.mp he with rfl | he'
      · refine ⟨none, rfl, ?_⟩
        change size (subtreeAt (child a) q) < size (Tree.decision e child)
        exact (size_subtreeAt_le (child a) q).trans_lt (size_child_lt_decision e child a)
      · obtain ⟨q', hq', hlt⟩ := exists_node_gt_of_mem_ancestorPts (child a) q e he'
        exact ⟨some ⟨a, q'⟩, hq', hlt⟩

omit [Fintype Ω] [DecidableEq Ω] in
/-- **CA-3′, the size inequality**: on a strongly fair tree, if `e` is strictly below `d` then
every `e`-node's subtree is strictly smaller than every `d`-node's (`LabIso` preserves `size`
across each fiber).
Source: `calibration.md` CA-3′ ("by fiber isomorphism, every `d`-node has an `e`-node below it";
the well-foundedness it needs); `fair-repair.md` FR-1(i) (the size argument)
Kind: P
Fidelity: exact
Hyps: (a) `StronglyFair B` -/
theorem stronglyFair_size_lt_of_strictlyBelow {B : Tree Ω ι acts K} (hB : StronglyFair B)
    {e d : ι} (h : StrictlyBelow B e d) (qe qd : B.DecNode) (he : pt B qe = e)
    (hd : pt B qd = d) : size (subtreeAt B qe) < size (subtreeAt B qd) := by
  obtain ⟨q, hq, hanc⟩ := h
  obtain ⟨q', hq', hlt⟩ := exists_node_gt_of_mem_ancestorPts B q d hanc
  have h1 := (hB e qe ((mem_fiber B e qe).mpr he) q ((mem_fiber B e q).mpr hq)).size_eq
  have h2 := (hB d qd ((mem_fiber B d qd).mpr hd) q' ((mem_fiber B d q').mpr hq')).size_eq
  omega

omit [Fintype Ω] [DecidableEq Ω] in
/-- **CA-3′, irreflexivity**: no point is strictly below itself on a strongly fair tree.
Source: `calibration.md` CA-3′
Kind: C
Hyps: (a) `StronglyFair B` -/
theorem stronglyFair_not_strictlyBelow_self {B : Tree Ω ι acts K} (hB : StronglyFair B) (d : ι) :
    ¬ StrictlyBelow B d d := by
  intro h
  obtain ⟨q, hq, -⟩ := id h
  exact lt_irrefl _ (stronglyFair_size_lt_of_strictlyBelow hB h q q hq hq)

omit [Fintype Ω] [DecidableEq Ω] in
/-- **CA-3′, the locality needed for DF self-models**: on a strongly fair tree an ancestor point
of a `d`-node is never strictly below `d`.
Source: `calibration.md` CA-3′ ("points strictly below `d` are never on a path to a `d`-node")
Kind: C
Hyps: (a) `StronglyFair B` -/
theorem stronglyFair_not_strictlyBelow_of_mem_ancestorPts {B : Tree Ω ι acts K}
    (hB : StronglyFair B) (q : B.DecNode) {e : ι} (he : e ∈ ancestorPts B q) :
    ¬ StrictlyBelow B e (pt B q) := by
  intro h
  obtain ⟨q', hq', hlt⟩ := exists_node_gt_of_mem_ancestorPts B q e he
  have := stronglyFair_size_lt_of_strictlyBelow hB h q' q hq' rfl
  omega

end ca3

/-! ### Reach positivity -/

section reach

omit [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] in
/-- On a pruned tree, a node is reached with positive probability by every procedure that is
full-support at the node's ancestor points.
Source: none: infrastructure
Kind: L -/
theorem reach_pos_of_pruned [∀ d, Nonempty (acts d)] (C : Proc ι acts K) :
    (B : Tree Ω ι acts K) → (∀ ℓ, 0 < chanceWeight B ℓ) → ∀ q : B.DecNode,
      (∀ e ∈ ancestorPts B q, ∀ a, 0 < (C e).w a) → 0 < reach C B q
  | leaf _ _, _, q, _ => q.elim
  | chance _ β child, hp, ⟨i, q⟩, hC => by
      rw [reach_chance]
      obtain ⟨ℓ₀⟩ := leaves_nonempty (child i)
      have hβ : 0 < β.w i := by
        have := hp ⟨i, ℓ₀⟩
        rw [chanceWeight_chance] at this
        rcases (β.nonneg i).lt_or_eq with h | h
        · exact h
        · rw [← h, zero_mul] at this; exact absurd this (lt_irrefl 0)
      have hp' : ∀ ℓ, 0 < chanceWeight (child i) ℓ := fun ℓ => by
        have := hp ⟨i, ℓ⟩
        rw [chanceWeight_chance] at this
        exact pos_of_mul_pos_right this hβ.le
      exact mul_pos hβ (reach_pos_of_pruned C (child i) hp' q hC)
  | decision d' child, _, none, _ => by rw [reach_decision_none]; exact one_pos
  | decision d' child, hp, some ⟨a, q⟩, hC => by
      rw [reach_decision_some]
      have hp' : ∀ ℓ, 0 < chanceWeight (child a) ℓ := fun ℓ => by
        have := hp ⟨a, ℓ⟩
        rwa [chanceWeight_decision] at this
      exact mul_pos (hC d' List.mem_cons_self a)
        (reach_pos_of_pruned C (child a) hp' q fun e he => hC e (List.mem_cons_of_mem d' he))

end reach

/-! ### DF self-models exist on `𝔉` -/

section existence

variable {obs : ι → Finset Ω} {actEv : (d : ι) → acts d → Finset Ω}

/-- The DF self-model of `C` at `d`: `C` at the points strictly below `d`, uniform elsewhere.
Source: `calibration.md` Definition C2 (the self-model's shape); CA-2′(i)
Kind: D -/
noncomputable def dfSelfModel [∀ d, Nonempty (acts d)] (B : Tree Ω ι acts K)
    (C : Proc ι acts K) (d : ι) : Proc ι acts K := fun e =>
  haveI := Classical.propDecidable
  if StrictlyBelow B e d then C e else FinDistr.uniform

/-- The DF self-model is full-support off the points strictly below `d` and equals `C` on them.
Source: none: infrastructure
Kind: L -/
theorem dfSelfModel_spec [∀ d, Nonempty (acts d)] (B : Tree Ω ι acts K) (C : Proc ι acts K)
    (d : ι) :
    (∀ e, ¬ StrictlyBelow B e d → ∀ a, 0 < (dfSelfModel B C d e).w a) ∧
    (∀ e, StrictlyBelow B e d → dfSelfModel B C d e = C e) := by
  classical
  constructor
  · intro e he a
    unfold dfSelfModel
    rw [if_neg he]
    exact FinDistr.uniform_w_pos a
  · intro e he
    unfold dfSelfModel
    rw [if_pos he]

/-- **The DF self-model realizes `O_d` on `𝔉`** (the positivity CA-2′(i) needs): the realized
`O_d`-run's `d`-node is reached under `dfSelfModel`, because its ancestor points are not strictly
below `d` (CA-3′) and so carry the uniform mixed action.
Source: `calibration.md` CA-2′(i) ("on `𝔉` no point is DF-free"); CA-3′
Kind: P
Fidelity: exact
Hyps: (a) `FairClass` -/
theorem FairClass.nu_dfSelfModel_obs_pos [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) (C : Proc ι acts K) {d : ι} (hd : d ∈ queried B) :
    0 < nu (dfSelfModel B C d) B (obs d) := by
  rw [h.nu_obs_eq_fiberMass' _ hd]
  obtain ⟨ℓ₀, hpos, hobs⟩ := h.realized d hd
  have hlaw : 0 < leafLaw (Proc.uniform : Proc ι acts K) B ℓ₀ :=
    pruned_leafLaw_pos h.pruned Proc.uniform_fullSupport ℓ₀
  obtain ⟨hcount, -⟩ := h.frec d hd Proc.uniform ℓ₀ hlaw hobs
  obtain ⟨q₀, hq₀, -⟩ := exists_dNode_of_count_pos d B ℓ₀ (by omega)
  have hreach : 0 < reach (dfSelfModel B C d) B q₀ := by
    refine reach_pos_of_pruned _ B h.pruned q₀ fun e he a => ?_
    refine (dfSelfModel_spec B C d).1 e ?_ a
    rw [← hq₀]
    exact stronglyFair_not_strictlyBelow_of_mem_ancestorPts h.stronglyFair q₀ he
  unfold fiberMass
  exact lt_of_lt_of_le hreach (Finset.single_le_sum (fun q _ => reach_nonneg _ B q)
    ((mem_fiber B d q₀).mpr hq₀))

/-- **CA-2′(i): DF self-models exist at every queried point of `𝔉`, for every procedure** — with
the calibrated states of the self-models `dfSelfModel`.
Source: `calibration.md` CA-2′(i) ("on `𝔉` no point is DF-free"); A52
Kind: P
Fidelity: exact
Hyps: (a) `FairClass` -/
theorem FairClass.exists_dfMasked [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) (C : Proc ι acts K) : ∃ s, DFMasked s obs C B := by
  classical
  obtain ⟨ℓ₀⟩ := leaves_nonempty B
  refine ⟨fun d => if hd : d ∈ queried B then
      calibratedState (dfSelfModel B C d) B (obs d) (h.nu_dfSelfModel_obs_pos C hd)
    else State.dirac (world B ℓ₀) 0, fun d hd => ?_⟩
  obtain ⟨hfull, hbelow⟩ := dfSelfModel_spec B C d
  refine ⟨dfSelfModel B C d, hfull d (stronglyFair_not_strictlyBelow_self h.stronglyFair d), hfull, hbelow,
    h.nu_dfSelfModel_obs_pos C hd, ?_⟩
  exact strictClausesAt_calibratedState obs (dfSelfModel B C d) B _ d
    (h.nu_dfSelfModel_obs_pos C hd) (by rw [dif_pos hd])

/-- **A DF-`T_EDT`-consistent deterministic procedure exists on every `B ∈ 𝔉`** (the leaves-up
argmax of `Q`, `exists_pointwise_best`, with the DF self-models of `FairClass.exists_dfMasked`):
the untrembled analogue of FR-13 whose trembled form (`fairClass_eventTremble_exists_open`)
remains open.
Source: `calibration.md` CA-2′(i); mandate T12(b) ("Existence of DF-consistent deterministic
procedures: leaves-up argmax of `Q`")
Kind: C
Fidelity: exact
Hyps: (a) `FairClass` -/
theorem FairClass.exists_dfMasked_tEdt_ofFun [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) :
    ∃ (σ : (d : ι) → acts d) (s : ι → State Ω K),
      DFMasked s obs (Proc.ofFun σ) B ∧ TEdt s actEv (Proc.ofFun σ) B := by
  obtain ⟨σ, hσ⟩ := exists_pointwise_best h.stronglyFair
  obtain ⟨s, hs⟩ := h.exists_dfMasked (Proc.ofFun σ)
  refine ⟨σ, s, hs, (h.dfMasked_tEdt_iff s hs).mpr fun d hd a ha b => ?_⟩
  have : a = σ d := by
    by_contra hne
    simp [Proc.ofFun_w, hne] at ha
  subst this
  exact hσ d hd b

/-- **CA-4′'s first inclusion as a statement about procedures**: on `𝔉`, every event-tremble-EDT-
consistent procedure is DF-masked-EDT-consistent (some DF state assignment approves it).
Source: `calibration.md` CA-4′ (`{D2} ⊆ {DF-EDT}`); A52
Kind: C
Fidelity: exact
Hyps: (a) `FairClass`, (a) D2 -/
theorem FairClass.dfMasked_tEdt_of_eventTremble [∀ d, Nonempty (acts d)]
    {B : Tree Ω ι acts K} (h : FairClass obs actEv B) {C : Proc ι acts K}
    (hD2 : EventTrembleEdtConsistent obs actEv C B) :
    ∃ s, DFMasked s obs C B ∧ TEdt s actEv C B := by
  obtain ⟨s, hs⟩ := h.exists_dfMasked C
  exact ⟨s, hs, h.tEdt_of_eventTremble_of_dfMasked hD2 s hs⟩

end existence

/-! ### CA-4′'s second strictness on `fr12` -/

section chain

open Cleanroom.Found.DpCoreTree.Catalogue

/-- **`{DF-EDT} ⊊ {opt}` on `fr12`** (CA-4′'s second strictness): `(out, y)` is optimal and
DF-`T_EDT`-rejected under every DF state assignment — at `p2`, `Q(x) = 0 > −1 = Q(y)` and `y` is
played — while some deterministic procedure is DF-`T_EDT`-consistent on `fr12`
(`FairClass.exists_dfMasked_tEdt_ofFun`). With `{D2} ⊆ {DF-EDT}` (`dfMasked_tEdt_of_eventTremble`)
this places DF-EDT strictly inside optimality; the first strictness `{D2} ⊊ {DF-EDT}` (the
mandate's `t3` instance) is not shipped.
Source: `calibration.md` CA-4′ (`{D2} ⊊ {DF-EDT} ⊊ {opt}`); `fair-repair.md` FR-12; mandate T12(c)
Kind: N+
Fidelity: weaker: the second strictness only
Hyps: (a) all -/
theorem fr12_outY_isOptimal_not_dfMasked_tEdt :
    IsOptimal outY fr12 ∧
    (∀ s, DFMasked s twoObs outY fr12 → ¬ TEdt s twoActEv outY fr12) ∧
    ∃ (σ : Pt2 → Act2) (s : Pt2 → State TwoW ℚ),
      DFMasked s twoObs (Proc.ofFun σ) fr12 ∧ TEdt s twoActEv (Proc.ofFun σ) fr12 := by
  obtain ⟨hF, hopt, -, -, -, -, -⟩ := fr12_outY_isOptimal_not_eventTremble
  refine ⟨hopt, fun s hDF hT => ?_, hF.exists_dfMasked_tEdt_ofFun⟩
  have := (hF.dfMasked_tEdt_iff s hDF).mp hT .p2 (twoPoint_queried 0 0 (-1)).2 .b
    (by simp [outY, proc2, FinDistr.act2]) .a
  unfold fr12 at this
  rw [twoPoint_Q_p2_a, twoPoint_Q_p2_b] at this
  norm_num at this

end chain

end Cleanroom.Decision.DpEdtUdtFair

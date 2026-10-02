import Cleanroom.Decision.DpCartesianFrames.Witnesses
import Cleanroom.Decision.DpCartesianFrames.OneRound

/-!
# Tree `M`: the N+ witness of headline 3 and of CF-12; the β-pair is N− for both

Package `dp-cartesian-frames`, file 12 (repair round 1, audit B1 of both lenses). Lazy seeding.

* **CFF-13's tree `M`** (`treeM`): a *recorded* root coin; tails → an unrecorded coin over two
  copies of the `d`-node (`d = true`, worlds `true`); heads → the `e`-node (`e = false`, worlds
  `false`). It is strongly fair with a **two-node fiber** (`treeM_stronglyFair`), the coin
  partition `mS` is column-determined (`treeM_columnDetermined`) with **both cells realized**
  (`treeM_in`, `treeM_out`), no point straddles it (`treeM_not_straddles`), and the conclusion of
  `observable2_fr_of_stronglyFair` holds on it (`treeM_observable2_lazy`) for a non-trivial
  reason: the row realizing "`a` on `S`, `b` off `S`" is forced to be the genuinely conditional
  policy `π true = a, π false = b` (`treeM_conditional_forced`). This is the witness the
  mandate's §7 bar asks for ("a fiber with two nodes in one cell and a column-determined
  non-trivial `S`").
* **The same tree inhabits CF-12's full hypothesis package** (one-round, every node
  subtree-veridical under `mObs`, disjoint observations) with an observation system that takes
  two values on the image (`treeM_obsSystem_observable`, `treeM_obsSystem_two_values`), and so
  instantiates T4(b)'s `&`-decomposition (`treeM_fr_biextEquiv_sumI_assume`).
* **The β-pair is N− for the forward direction** (the audits' finding, proved): on
  `Fr (pairTree β)` for *every* inner weight `β`, every column-determined partition is trivial on
  the image (`pairTree_columnDetermined_trivial`, `pairTree_no_nontrivial_columnDetermined`),
  so observability holds there for the trivial reason (`pairTree_observable2_trivially`); and
  "no point straddles" already forces the same triviality (`pairTree_not_straddles_trivial`).
  Consequence for the sources: CFF-13's second "non-vacuous instance" (the β-pair's `P′`) is
  vacuous — findings F15.
* **T5(b) (⟸)**: dp-core-063's backward reading, "every column-determined partition observable
  ⟹ strongly fair", is refuted **non-degenerately by tree `Mₓ`** (`treeMx`, repair round 2):
  tree `M` with the two `d`-copies given *unequal* payoffs (`mNodeDj`). It is not strongly fair
  (`treeMx_not_stronglyFair`), yet every column-determined partition of its lazy frame is
  observable (`treeMx_observable2_of_columnDetermined`, through the no-straddle theorem — both
  points are consulted on one side of the root coin), and its coin partition `mS` is
  column-determined with both cells realized (`treeMx_backward_refutation`), the realizing row
  again forced conditional (`treeMx_conditional_forced`). `pairTree coinThird` also refutes the
  sentence (`pairTree_third_observable_not_stronglyFair`, CF-14(b)'s own witness), but only
  **N−**: on the β-pair the antecedent holds because no column-determined partition is
  non-trivial on the image — the same degeneracy that makes it N− for the forward direction.
* **T3's third branch**: observability at `Loc d` while coverage fails. The N+ witness is
  **`uncov3`** (repair round 3, audit r3 adversarial B1): CF-10 line 47's own shape — a root
  coin; tails → a second coin → [the `d`-node with both leaves in `O_d`, an unconsulted
  `O_d`-leaf]; heads → a leaf *outside* `O_d`. Its single `d`-node is subtree-veridical
  (`uncov3_veridical`), so `S_{O_d}` is observable at `Loc d` by the Local Theorem
  (`uncov3_observable2_loc`); **both cells are realized** (`uncov3_both_cells`: tails columns
  land in `S_{O_d}`, heads columns outside — `uncov3_loc_mem_iff`); the `d`-node is consulted
  with distinct outcomes inside the `S`-cell (`uncov3_d_consulted`); and the tails-heads leaf,
  of mass `¼` and world in `O_d`, passes no `d`-node, so coverage fails for every procedure
  (`uncov3_not_covers`) — packaged as `uncov3_observable2_loc_not_covers`. Coverage appears in
  no hypothesis of the Local Theorem, and this is the instance showing it is not implied
  either. The earlier two-branch tree `uncovTree` (repair round 1) is kept and regraded
  **N−**: every one of its worlds is `true ∈ O_d`, so `S_{O_d}` contains the whole image of
  `Loc () uncovTree` and its observability holds for the trivial reason (one cell); only its
  coverage-fails conjunct has content.
-/

namespace Cleanroom.Decision.DpCartesianFrames

open CartesianFrames
open scoped CartesianFrames.Frame
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpFairnessReloc

/-! ### Tree `M` -/

/-- The `d`-node of tree `M` (point `true`): every leaf records world `true`; payoff `1` after
`a`, `0` after `b`.
Source: cf-frontier CFF-13 (line 82: "two isomorphic `d`-nodes")
Kind: D -/
def mNodeD : Tree Bool Bool (fun _ => Act2) ℚ :=
  .decision true fun act => .leaf true (if act = .a then 1 else 0)

/-- The `e`-node of tree `M` (point `false`): every leaf records world `false`.
Source: cf-frontier CFF-13 (line 82: "`H → e`")
Kind: D -/
def mNodeE : Tree Bool Bool (fun _ => Act2) ℚ :=
  .decision false fun act => .leaf false (if act = .a then 1 else 0)

/-- The tails branch of tree `M`: an unrecorded fair coin over two copies of the `d`-node.
Source: cf-frontier CFF-13 (line 82: "`T →` unrecorded `c₂ →` two isomorphic `d`-nodes")
Kind: D -/
def mTails : Tree Bool Bool (fun _ => Act2) ℚ := .chance 2 FinDistr.fair fun _ => mNodeD

/-- **CFF-13's tree `M`**: a recorded fair root coin; index `0` (tails) → `mTails`, index `1`
(heads) → the `e`-node.
Source: cf-frontier CFF-13 (line 82: "Non-vacuous instances: tree `M` (recorded `c₁`;
`H → e`; `T →` unrecorded `c₂ →` two isomorphic `d`-nodes …)")
Kind: D
Fidelity: exact -/
def treeM : Tree Bool Bool (fun _ => Act2) ℚ := .chance 2 FinDistr.fair ![mTails, mNodeE]

/-- The coin partition of tree `M`: the worlds recording tails (`true`).
Source: cf-frontier CFF-13 (line 82: "coin partition")
Kind: D -/
def mS : Set (Bool × ℚ) := {w | w.1 = true}

/-- Observation labels of tree `M`: `O_d = {true}`, `O_e = {false}` — disjoint.
Source: cf-correspondence CF-12 (line 47: "pairwise disjoint" observations); none otherwise
Kind: D -/
def mObs : Bool → Finset Bool := fun p => {p}

/-- The world of every run of tree `M` is its root coin.
Source: none: infrastructure
Kind: L -/
theorem treeM_outcome_fst (π : Bool → Act2) :
    ∀ ε : ChanceProfile treeM, ((Fr treeM).outcome π ε).1 = decide (ε.1 = 0)
  | (i, _) => by fin_cases i <;> rfl

/-- **The coin partition of tree `M` is column-determined** in the lazy frame.
Source: cf-frontier CFF-13 (line 82)
Kind: N+
Fidelity: exact -/
theorem treeM_columnDetermined : ColumnDetermined (Fr treeM) mS := by
  intro ε π π'
  show (((Fr treeM).outcome π ε).1 = true) ↔ (((Fr treeM).outcome π' ε).1 = true)
  rw [treeM_outcome_fst, treeM_outcome_fst]

/-- A tails column of tree `M` (the inner coin and the unqueried coordinates arbitrary).
Source: none: infrastructure
Kind: D -/
noncomputable def mεT : ChanceProfile treeM := (0, fun _ => Classical.arbitrary _)

/-- A heads column of tree `M`.
Source: none: infrastructure
Kind: D -/
noncomputable def mεH : ChanceProfile treeM := (1, fun _ => Classical.arbitrary _)

/-- Every row lies in `mS` at the tails column: the `S`-cell is realized.
Source: cf-frontier CFF-13 (line 82)
Kind: N+
Fidelity: exact -/
theorem treeM_in (π : Bool → Act2) : (Fr treeM).outcome π mεT ∈ mS := by
  show ((Fr treeM).outcome π mεT).1 = true
  rw [treeM_outcome_fst]; rfl

/-- Every row lies off `mS` at the heads column: the `Sᶜ`-cell is realized.
Source: cf-frontier CFF-13 (line 82)
Kind: N+
Fidelity: exact -/
theorem treeM_out (π : Bool → Act2) : (Fr treeM).outcome π mεH ∉ mS := by
  show ¬ (((Fr treeM).outcome π mεH).1 = true)
  rw [treeM_outcome_fst]; decide

/-- **Tree `M` is strongly fair with a two-node fiber**: the two `d`-nodes carry the same
subtree (`LabIso.refl`), the `e`-fiber is a singleton. This is not the singleton-fiber reason
the mandate's §7 vacuity trap names.
Source: cf-frontier CFF-13 (line 82: "two isomorphic `d`-nodes")
Kind: N+
Fidelity: exact -/
theorem treeM_stronglyFair : StronglyFair treeM := by
  intro d q hq q' hq'
  rw [mem_fiber] at hq hq'
  obtain ⟨i, q⟩ := q
  obtain ⟨i', q'⟩ := q'
  fin_cases i <;> fin_cases i'
  · obtain ⟨j, q⟩ := q
    obtain ⟨j', q'⟩ := q'
    rcases q with _ | ⟨_, e⟩ <;> rcases q' with _ | ⟨_, e'⟩
    · exact LabIso.refl _
    · exact e'.elim
    · exact e.elim
    · exact e.elim
  · obtain ⟨j, q⟩ := q
    rcases q with _ | ⟨_, e⟩ <;> rcases q' with _ | ⟨_, e'⟩
    · exact absurd (a := (true = false)) (hq.trans hq'.symm) (by decide)
    · exact e'.elim
    · exact e.elim
    · exact e.elim
  · obtain ⟨j', q'⟩ := q'
    rcases q with _ | ⟨_, e⟩ <;> rcases q' with _ | ⟨_, e'⟩
    · exact absurd (a := (false = true)) (hq.trans hq'.symm) (by decide)
    · exact e'.elim
    · exact e.elim
    · exact e.elim
  · rcases q with _ | ⟨_, e⟩ <;> rcases q' with _ | ⟨_, e'⟩
    · exact LabIso.refl _
    · exact e'.elim
    · exact e.elim
    · exact e.elim

/-- No point with two actions straddles `mS` (from strong fairness, through
`not_straddles_of_stronglyFair`): the hypothesis of the no-straddle theorem on tree `M`.
Source: cf-frontier CFF-13 (line 82)
Kind: N+
Fidelity: exact -/
theorem treeM_not_straddles (d : Bool) (h2 : 2 ≤ Fintype.card ((fun _ : Bool => Act2) d)) :
    ¬ Straddles treeM mS d :=
  not_straddles_of_stronglyFair treeM_stronglyFair treeM_columnDetermined d h2

/-- **Headline 3 instantiated on tree `M`** (lazy): the coin partition is observable in
`Fr treeM`, by `observable2_fr_of_stronglyFair` on its full hypothesis package — with both cells
realized (`treeM_in`, `treeM_out`), so the partition is not trivial on the image.
Source: cf-frontier CFF-13(a) (line 82); mandate §7 ("T6's N+ witness needs a fiber with two
nodes in one cell and a column-determined non-trivial `S`: tree `M` of CFF-13")
Kind: N+
Fidelity: exact -/
theorem treeM_observable2_lazy : Observable2 (Fr treeM) mS :=
  observable2_fr_of_stronglyFair treeM_stronglyFair treeM_columnDetermined

/-- **The instance exercises the content**: any row realizing the conditional policy "`a` on
`mS`, `b` off `mS`" answers `a` at `d` and `b` at `e` — it is genuinely conditional, so
observability on tree `M` is not for the "every row constant" or "one cell realized" reasons.
Source: cf-frontier CFF-13 (line 82: "coin partition observable via `π_f(e) = f(S_H)(e)`,
`π_f(d) = f(S_T)(d)`")
Kind: N+
Fidelity: exact -/
theorem treeM_conditional_forced (π : Bool → Act2)
    (h : ∀ e, ((Fr treeM).outcome π e ∈ mS →
        (Fr treeM).outcome π e = (Fr treeM).outcome (fun _ => Act2.a) e) ∧
      ((Fr treeM).outcome π e ∉ mS →
        (Fr treeM).outcome π e = (Fr treeM).outcome (fun _ => Act2.b) e)) :
    π true = Act2.a ∧ π false = Act2.b := by
  constructor
  · have hp := congrArg Prod.snd ((h mεT).1 (treeM_in π))
    change (if π true = Act2.a then (1 : ℚ) else 0) =
      (if Act2.a = Act2.a then (1 : ℚ) else 0) at hp
    rw [if_pos rfl] at hp
    by_contra hne
    rw [if_neg hne] at hp
    norm_num at hp
  · have hp := congrArg Prod.snd ((h mεH).2 (treeM_out π))
    change (if π false = Act2.a then (1 : ℚ) else 0) =
      (if Act2.b = Act2.a then (1 : ℚ) else 0) at hp
    rw [if_neg (show ¬ (Act2.b = Act2.a) by decide)] at hp
    by_contra hne
    have ha : π false = Act2.a := by
      cases hπ : π false
      · rfl
      · exact absurd hπ hne
    rw [if_pos ha] at hp
    norm_num at hp

/-! ### Tree `M` inhabits CF-12's hypothesis package -/

/-- Tree `M` is one-round: no decision node lies strictly below another.
Source: cf-correspondence CF-12 (line 47)
Kind: N+
Fidelity: exact -/
theorem treeM_oneRound : OneRound treeM := by
  intro i
  fin_cases i
  · intro j act; trivial
  · intro act; trivial

/-- Every node of tree `M` is subtree-veridical under `mObs`.
Source: cf-correspondence CF-12 (line 47)
Kind: N+
Fidelity: exact -/
theorem treeM_veridical : ∀ d, ∀ q ∈ fiber treeM d, SubtreeVeridical mObs treeM q := by
  show ∀ d, ∀ q ∈ fiber treeM d, ∀ ℓ ∈ leavesBelow treeM q,
    world treeM ℓ ∈ mObs (pt treeM q)
  decide

/-- The realized observation events of tree `M` are pairwise disjoint.
Source: cf-correspondence CF-12 (line 47)
Kind: N+
Fidelity: exact -/
theorem treeM_disjoint :
    ∀ d d', d ≠ d' → ∀ ℓ : treeM.Leaves, ¬ (world treeM ℓ ∈ mObs d ∧ world treeM ℓ ∈ mObs d') := by
  decide

/-- **CF-12 instantiated on tree `M`**: the observation system is observable in `Fr treeM`, by
`observable_fr_obsSystem_of_oneRound` on its full hypothesis package.
Source: cf-correspondence CF-12 (line 47); mandate T4(a)
Kind: N+
Fidelity: exact -/
theorem treeM_obsSystem_observable : Observable (Fr treeM) (obsSystem mObs) :=
  observable_fr_obsSystem_of_oneRound mObs treeM treeM_oneRound treeM_veridical treeM_disjoint

/-- **The observation system takes two values on the image**: `some true` on a tails column,
`some false` on a heads column — so the conditional policy `π_f(d) := f(some d)(d)` of CF-12
is load-bearing on tree `M`.
Source: cf-correspondence CF-12 (line 47)
Kind: N+
Fidelity: exact -/
theorem treeM_obsSystem_two_values (π : Bool → Act2) :
    obsSystem mObs ((Fr treeM).outcome π mεT) = some true ∧
    obsSystem mObs ((Fr treeM).outcome π mεH) = some false := by
  constructor
  · refine obsSystem_readout_eq_some mObs treeM treeM_disjoint _ true ?_
    exact Finset.mem_singleton.mpr (treeM_in π)
  · refine obsSystem_readout_eq_some mObs treeM treeM_disjoint _ false ?_
    refine Finset.mem_singleton.mpr ?_
    have h := treeM_outcome_fst π mεH
    exact h.trans rfl

/-- **T4(b) instantiated on tree `M`**: `Fr treeM ≃ᵇ &_c Assume_{E_c}(Fr treeM)` over
`Option Bool`, with two cells realized.
Source: cf-correspondence CF-12 (line 47); mandate T4(b)
Kind: N+
Fidelity: exact -/
theorem treeM_fr_biextEquiv_sumI_assume :
    Fr treeM ≃ᵇ sumI fun c => (Fr treeM).assume (colCell (Fr treeM) (obsSystem mObs) c) :=
  fr_biextEquiv_sumI_assume_obsSystem mObs treeM treeM_oneRound treeM_veridical treeM_disjoint

/-! ### The β-pair is N− for the forward direction -/

/-- The outcome of `Fr (pairTree β)` reads the inner coin below the chosen action and the
action's payoff; the root branch is invisible in the outcome (CF-14(a): the upstream coin is
unrecorded).
Source: cf-correspondence CF-14(a) (line 65: "leaf labels equal (upstream coin unrecorded in
worlds)")
Kind: L -/
theorem pairTree_outcome (β : FinDistr ℚ (Fin 2)) (π : Unit → Act2) (i : Fin 2)
    (εs : (j : Fin 2) → ChanceProfile (pairSub (![FinDistr.fair, β] j))) :
    (Fr (pairTree β)).outcome π (i, εs) =
      (coinOf ((εs i : Act2 → Fin 2 × (Fin 2 → Unit)) (π ())).1,
        if π () = Act2.a then (1 : ℚ) else 0) := rfl

/-- **Every column-determined partition of `Fr (pairTree β)` is trivial on the image**, for
every inner weight `β`: any two outcomes lie on the same side (move `π`'s sub-profile into the
other root branch, then Lemma A, since the root coin is unrecorded).
Source: audit r1 (both lenses), probes `PairTreeVacuity.lean`/`PairTreeTrivial.lean`;
cf-correspondence CF-14(a) (line 65)
Kind: P
Fidelity: exact
Hyps: none -/
theorem pairTree_columnDetermined_trivial (β : FinDistr ℚ (Fin 2)) (S : Set (Bool × ℚ))
    (hcd : ColumnDetermined (Fr (pairTree β)) S) (π π' : Unit → Act2)
    (ε ε' : ChanceProfile (pairTree β)) :
    ((Fr (pairTree β)).outcome π ε ∈ S ↔ (Fr (pairTree β)).outcome π' ε' ∈ S) := by
  obtain ⟨i, εs⟩ := ε
  obtain ⟨i', εs'⟩ := ε'
  let εt : ChanceProfile (pairTree β) := (i', fun _ => εs i)
  have h1 : (Fr (pairTree β)).outcome π (i, εs) = (Fr (pairTree β)).outcome π εt := rfl
  have hsr : SameRoute (pairTree β) εt (i', εs') := And.intro rfl (Or.inl (by decide))
  rw [h1]
  exact cell_eq_of_sameRoute S (pairTree β) hcd εt (i', εs') hsr π π'

/-- **No column-determined partition of `Fr (pairTree β)` has both cells realized** — so the
β-pair cannot inhabit headline 3's hypothesis package non-degenerately (N−), and CFF-13's
"non-vacuous instance" `P′` is vacuous (findings F15).
Source: audit r1; cf-frontier CFF-13 (line 82: "the β-pair's `P′` (realizable-outcome-fair, not
strongly fair)")
Kind: P
Fidelity: exact
Hyps: none -/
theorem pairTree_no_nontrivial_columnDetermined (β : FinDistr ℚ (Fin 2)) :
    ¬ ∃ S : Set (Bool × ℚ), ColumnDetermined (Fr (pairTree β)) S ∧
      (∃ π ε, (Fr (pairTree β)).outcome π ε ∈ S) ∧
      (∃ π ε, (Fr (pairTree β)).outcome π ε ∉ S) := by
  rintro ⟨S, hcd, ⟨π, ε, hin⟩, ⟨π', ε', hout⟩⟩
  exact hout ((pairTree_columnDetermined_trivial β S hcd π π' ε ε').mp hin)

/-- On the β-pair the conclusion of `observable2_fr_of_stronglyFair` holds for a trivial reason
— no fairness, no straddle argument: pick the row by looking at one column.
Source: audit r1
Kind: P
Fidelity: exact
Hyps: none -/
theorem pairTree_observable2_trivially (β : FinDistr ℚ (Fin 2)) (S : Set (Bool × ℚ))
    (hcd : ColumnDetermined (Fr (pairTree β)) S) : Observable2 (Fr (pairTree β)) S := by
  intro a₀ a₁
  let ε₀ : ChanceProfile (pairTree β) := Classical.arbitrary _
  by_cases h : (Fr (pairTree β)).outcome a₀ ε₀ ∈ S
  · refine ⟨a₀, fun e => ⟨fun _ => rfl, fun hn => absurd ?_ hn⟩⟩
    exact (pairTree_columnDetermined_trivial β S hcd a₀ a₀ ε₀ e).mp h
  · refine ⟨a₁, fun e => ⟨fun hs => absurd ?_ h, fun _ => rfl⟩⟩
    exact (pairTree_columnDetermined_trivial β S hcd a₁ a₀ e ε₀).mp hs

/-- The single point of `pairTree β` is consulted on every run.
Source: none: infrastructure
Kind: L -/
theorem pairTree_count_pos (β : FinDistr ℚ (Fin 2)) (π : Unit → Act2)
    (ε : ChanceProfile (pairTree β)) :
    0 < count () (pairTree β) (runLeaf π (pairTree β) ε) := by
  obtain ⟨i, εs⟩ := ε
  show 0 < (if () = () then 1 else 0) + 0
  simp

/-- "No point straddles `S`" on `pairTree β` already forces every outcome to one side: the
hypothesis of `observable2_fr_of_not_straddles` admits no partition with both cells realized
on the β-pair either.
Source: audit r1
Kind: P
Fidelity: exact
Hyps: none -/
theorem pairTree_not_straddles_trivial (β : FinDistr ℚ (Fin 2)) (S : Set (Bool × ℚ))
    (hns : ∀ d, 2 ≤ Fintype.card ((fun _ : Unit => Act2) d) → ¬ Straddles (pairTree β) S d)
    (π π' : Unit → Act2) (ε ε' : ChanceProfile (pairTree β)) :
    ((Fr (pairTree β)).outcome π ε ∈ S ↔ (Fr (pairTree β)).outcome π' ε' ∈ S) := by
  have h := hns () (by decide)
  unfold Straddles at h
  constructor
  · intro hs; by_contra hn
    exact h ⟨⟨π, ε, pairTree_count_pos β π ε, hs⟩, ⟨π', ε', pairTree_count_pos β π' ε', hn⟩⟩
  · intro hs; by_contra hn
    exact h ⟨⟨π', ε', pairTree_count_pos β π' ε', hs⟩, ⟨π, ε, pairTree_count_pos β π ε, hn⟩⟩

/-! ### T5(b) (⟸): the backward reading of dp-core-063 -/

/-- **dp-core-063's backward direction refuted on the β-pair** (T5(b) ⟸, CF-14(b)'s own
witness; **N−**): `pairTree coinThird` has every column-determined two-cell partition observable
in its lazy frame, yet it is not strongly fair (its fiber members are not labelled-isomorphic).
Degenerate: the antecedent holds only because every column-determined partition of
`Fr (pairTree β)` is trivial on the image (`pairTree_columnDetermined_trivial`,
`pairTree_no_nontrivial_columnDetermined`) — the mandate's "trivial partition observable" — so
nothing of "observable" is exercised. The non-degenerate refutation is `treeMx_backward_refutation`
(audit r2, both lenses).
Source: fable-slop-notes Claim 2.2 (line 47, "[guess]"), the (⟸) direction; cf-correspondence
CF-14(b) (line 67: "the (S3) Smoking-Lesion tree … has its (trivial) claimed partition
observable while the fiber's subtrees are non-isomorphic"); mandate T5(b) ("(⟸) the S3-shaped
one-point tree with `O_d = ⊤` queried on two branches with different lower weights — trivial
partition observable, fiber not `≅`")
Kind: N−
Fidelity: exact (the mandate's S3-shaped tree *is* `pairTree coinThird`: one point, `O_d = ⊤`,
two branches with different lower weights; the mandate prescribed this degenerate shape —
STANDARDS §3 wins, findings F19) -/
theorem pairTree_third_observable_not_stronglyFair :
    (∀ S : Set (Bool × ℚ), ColumnDetermined (Fr (pairTree coinThird)) S →
      Observable2 (Fr (pairTree coinThird)) S) ∧
    ¬ StronglyFair (pairTree coinThird) :=
  ⟨fun S hcd => pairTree_observable2_trivially coinThird S hcd, pairTree_third_not_stronglyFair⟩

/-! ### T5(b) (⟸), non-degenerate: tree `Mₓ` — tree `M` with unequal `d`-copies -/

/-- The `j`-th `d`-copy of tree `Mₓ` (point `true`): every leaf records world `true`; payoff
after `a` is `1` in copy `0` and `2` in copy `1`, `0` after `b`. The copies are *not*
labelled-isomorphic.
Source: audit r2 (adversarial B2: "tree `M` with unequal payoffs in the two `d`-copies");
cf-frontier CFF-13 (line 82: tree `M`), one payoff changed
Kind: D -/
def mNodeDj (j : Fin 2) : Tree Bool Bool (fun _ => Act2) ℚ :=
  .decision true fun act => .leaf true (if act = .a then (if j = 0 then 1 else 2) else 0)

/-- The tails branch of tree `Mₓ`: an unrecorded fair coin over the two unequal `d`-copies.
Source: audit r2 (adversarial B2)
Kind: D -/
def mxTails : Tree Bool Bool (fun _ => Act2) ℚ := .chance 2 FinDistr.fair fun j => mNodeDj j

/-- **Tree `Mₓ`**: tree `M` with unequal `d`-copies — a recorded fair root coin; index `0`
(tails) → `mxTails`; index `1` (heads) → the `e`-node.
Source: audit r2 (both lenses, B2); cf-frontier CFF-13 (line 82: tree `M`)
Kind: D -/
def treeMx : Tree Bool Bool (fun _ => Act2) ℚ := .chance 2 FinDistr.fair ![mxTails, mNodeE]

/-- The world of every run of tree `Mₓ` is its root coin.
Source: none: infrastructure
Kind: L -/
theorem treeMx_outcome_fst (π : Bool → Act2) :
    ∀ ε : ChanceProfile treeMx, ((Fr treeMx).outcome π ε).1 = decide (ε.1 = 0)
  | (i, _) => by fin_cases i <;> rfl

/-- The coin partition of tree `Mₓ` is column-determined in the lazy frame.
Source: audit r2 (B2)
Kind: N+
Fidelity: exact -/
theorem treeMx_columnDetermined : ColumnDetermined (Fr treeMx) mS := by
  intro ε π π'
  show (((Fr treeMx).outcome π ε).1 = true) ↔ (((Fr treeMx).outcome π' ε).1 = true)
  rw [treeMx_outcome_fst, treeMx_outcome_fst]

/-- Every row lies in `mS` at every tails column of tree `Mₓ`.
Source: audit r2 (B2)
Kind: N+
Fidelity: exact -/
theorem treeMx_in (π : Bool → Act2) (εs : (i : Fin 2) → ChanceProfile (![mxTails, mNodeE] i)) :
    (Fr treeMx).outcome π (0, εs) ∈ mS := by
  show ((Fr treeMx).outcome π (0, εs)).1 = true
  rw [treeMx_outcome_fst]; rfl

/-- Every row lies off `mS` at every heads column of tree `Mₓ`.
Source: audit r2 (B2)
Kind: N+
Fidelity: exact -/
theorem treeMx_out (π : Bool → Act2) (εs : (i : Fin 2) → ChanceProfile (![mxTails, mNodeE] i)) :
    (Fr treeMx).outcome π (1, εs) ∉ mS := by
  show ¬ (((Fr treeMx).outcome π (1, εs)).1 = true)
  rw [treeMx_outcome_fst]
  show ¬ (decide ((1 : Fin 2) = 0) = true)
  decide

/-- The constant-`b` row lands on `(coin, 0)` at every column of tree `Mₓ`.
Source: none: infrastructure
Kind: L -/
theorem treeMx_outcome_b : ∀ ε : ChanceProfile treeMx,
    (Fr treeMx).outcome (fun _ => Act2.b) ε = (decide (ε.1 = 0), 0)
  | (i, _) => by fin_cases i <;> rfl

/-- For column-determined `S`, membership on tree `Mₓ` depends only on the root coin (bridge
through the constant-`b` row).
Source: none: infrastructure
Kind: L -/
theorem treeMx_mem_iff (S : Set (Bool × ℚ)) (hcd : ColumnDetermined (Fr treeMx) S)
    (π : Bool → Act2) (ε : ChanceProfile treeMx) :
    (Fr treeMx).outcome π ε ∈ S ↔ ((decide (ε.1 = 0) : Bool), (0 : ℚ)) ∈ S := by
  rw [hcd ε π (fun _ => Act2.b), treeMx_outcome_b]

/-- The `d`-point of tree `Mₓ` is consulted only on tails columns.
Source: none: infrastructure
Kind: L -/
theorem treeMx_count_true (ℓ : treeMx.Leaves) :
    count true treeMx ℓ = if ℓ.1 = 0 then 1 else 0 := by
  revert ℓ; decide

/-- The `e`-point of tree `Mₓ` is consulted only on heads columns.
Source: none: infrastructure
Kind: L -/
theorem treeMx_count_false (ℓ : treeMx.Leaves) :
    count false treeMx ℓ = if ℓ.1 = 0 then 0 else 1 := by
  revert ℓ; decide

/-- A run consulting the `d`-point of tree `Mₓ` is a tails run.
Source: none: infrastructure
Kind: L -/
theorem treeMx_coin_of_count_true (π : Bool → Act2) (ε : ChanceProfile treeMx)
    (h : 0 < count true treeMx (runLeaf π treeMx ε)) : ε.1 = 0 := by
  have h1 : (runLeaf π treeMx ε).1 = ε.1 := rfl
  rw [treeMx_count_true, h1] at h
  by_contra hne
  rw [if_neg hne] at h
  exact lt_irrefl _ h

/-- A run consulting the `e`-point of tree `Mₓ` is a heads run.
Source: none: infrastructure
Kind: L -/
theorem treeMx_coin_of_count_false (π : Bool → Act2) (ε : ChanceProfile treeMx)
    (h : 0 < count false treeMx (runLeaf π treeMx ε)) : ε.1 ≠ 0 := by
  have h1 : (runLeaf π treeMx ε).1 = ε.1 := rfl
  rw [treeMx_count_false, h1] at h
  intro h0
  rw [if_pos h0] at h
  exact lt_irrefl _ h

/-- **No point of tree `Mₓ` straddles any column-determined partition**: each point is consulted
on one side of the root coin only, and a column-determined cell is a function of the coin.
Source: audit r2 (B2); zoo ZO-12 (line 108: the no-straddle hypothesis)
Kind: P
Fidelity: exact
Hyps: none -/
theorem treeMx_not_straddles_of_columnDetermined (S : Set (Bool × ℚ))
    (hcd : ColumnDetermined (Fr treeMx) S) (d : Bool)
    (_ : 2 ≤ Fintype.card ((fun _ : Bool => Act2) d)) : ¬ Straddles treeMx S d := by
  rintro ⟨⟨π, ε, hc, hS⟩, ⟨π', ε', hc', hS'⟩⟩
  change (Fr treeMx).outcome π ε ∈ S at hS
  change (Fr treeMx).outcome π' ε' ∉ S at hS'
  rw [treeMx_mem_iff S hcd] at hS hS'
  cases d
  · rw [decide_eq_false (treeMx_coin_of_count_false π ε hc)] at hS
    rw [decide_eq_false (treeMx_coin_of_count_false π' ε' hc')] at hS'
    exact hS' hS
  · rw [decide_eq_true (treeMx_coin_of_count_true π ε hc)] at hS
    rw [decide_eq_true (treeMx_coin_of_count_true π' ε' hc')] at hS'
    exact hS' hS

/-- **Every column-determined partition of `Fr Mₓ` is observable** (the no-straddle theorem).
Source: audit r2 (B2); zoo ZO-12 (line 108)
Kind: C
Fidelity: exact
Hyps: none -/
theorem treeMx_observable2_of_columnDetermined (S : Set (Bool × ℚ))
    (hcd : ColumnDetermined (Fr treeMx) S) : Observable2 (Fr treeMx) S :=
  observable2_fr_of_not_straddles treeMx S (treeMx_not_straddles_of_columnDetermined S hcd)

/-- Labelled-isomorphic leaves carry equal payoffs (`LabIso.leaf` is the only constructor that
applies).
Source: `dp-fairness-reloc` `LabIso` (definition of record); none otherwise
Kind: L -/
theorem labIso_leaf_payoff {ω ω' : Bool} {r r' : ℚ}
    (h : LabIso (Tree.leaf ω r : Tree Bool Bool (fun _ => Act2) ℚ) (.leaf ω' r')) : r = r' := by
  cases h; rfl

/-- **Tree `Mₓ` is not strongly fair**: its two `d`-copies carry different payoffs after `a`,
so they are not labelled-isomorphic.
Source: audit r2 (B2)
Kind: N+
Fidelity: exact -/
theorem treeMx_not_stronglyFair : ¬ StronglyFair treeMx := by
  intro h
  have hiso := h true ⟨0, ⟨0, none⟩⟩ ((mem_fiber _ _ _).mpr rfl)
    ⟨0, ⟨1, none⟩⟩ ((mem_fiber _ _ _).mpr rfl)
  change LabIso (mNodeDj 0) (mNodeDj 1) at hiso
  unfold mNodeDj at hiso
  cases hiso with
  | decision _ _ _ hchild =>
    have h2 := labIso_leaf_payoff (hchild .a)
    simp at h2

/-- **The instance exercises the content**: on tree `Mₓ` any row realizing the conditional policy
"`a` on `mS`, `b` off `mS`" answers `a` at `d` and `b` at `e` — observability of the coin
partition is not for the "every row constant" or "one cell realized" reasons.
Source: audit r2 (B2); cf-frontier CFF-13 (line 82: "`π_f(e) = f(S_H)(e)`, `π_f(d) = f(S_T)(d)`")
Kind: N+
Fidelity: exact -/
theorem treeMx_conditional_forced (π : Bool → Act2)
    (h : ∀ e, ((Fr treeMx).outcome π e ∈ mS →
        (Fr treeMx).outcome π e = (Fr treeMx).outcome (fun _ => Act2.a) e) ∧
      ((Fr treeMx).outcome π e ∉ mS →
        (Fr treeMx).outcome π e = (Fr treeMx).outcome (fun _ => Act2.b) e)) :
    π true = Act2.a ∧ π false = Act2.b := by
  let εs : (i : Fin 2) → ChanceProfile (![mxTails, mNodeE] i) := fun _ => Classical.arbitrary _
  constructor
  · have hp := congrArg Prod.snd ((h (0, εs)).1 (treeMx_in π εs))
    change (if π true = Act2.a then (if (εs 0).1 = 0 then (1 : ℚ) else 2) else 0) =
      (if Act2.a = Act2.a then (if (εs 0).1 = 0 then (1 : ℚ) else 2) else 0) at hp
    rw [if_pos rfl] at hp
    by_contra hne
    rw [if_neg hne] at hp
    split_ifs at hp <;> norm_num at hp
  · have hp := congrArg Prod.snd ((h (1, εs)).2 (treeMx_out π εs))
    change (if π false = Act2.a then (1 : ℚ) else 0) =
      (if Act2.b = Act2.a then (1 : ℚ) else 0) at hp
    rw [if_neg (show ¬ (Act2.b = Act2.a) by decide)] at hp
    by_contra hne
    have ha : π false = Act2.a := by
      cases hπ : π false
      · rfl
      · exact absurd hπ hne
    rw [if_pos ha] at hp
    norm_num at hp

/-- **dp-core-063's backward direction refuted non-degenerately** (T5(b) ⟸): on tree `Mₓ` every
column-determined partition of the lazy frame is observable, the tree is not strongly fair, and
the coin partition `mS` is column-determined with **both cells realized** — a tree with a
non-trivial observable column-determined partition and unequal fiber members. So "every
chance-determined partition observable ⟹ strongly fair" fails where "observable" has content
(contrast the β-pair, `pairTree_third_observable_not_stronglyFair`, N−).
Source: fable-slop-notes Claim 2.2 (line 47, "[guess]"), the (⟸) direction; dp-core-063;
mandate T5(b) ⟸; audit r2 (both lenses, B2; fidelity probe `BackwardNondegenerate`)
Kind: N+
Fidelity: stronger: the mandate's prescribed witness is the degenerate S3-shape; this one
realizes both cells of a column-determined partition -/
theorem treeMx_backward_refutation :
    (∀ S : Set (Bool × ℚ), ColumnDetermined (Fr treeMx) S → Observable2 (Fr treeMx) S) ∧
    ¬ StronglyFair treeMx ∧
    ColumnDetermined (Fr treeMx) mS ∧
    (∃ π ε, (Fr treeMx).outcome π ε ∈ mS) ∧ (∃ π ε, (Fr treeMx).outcome π ε ∉ mS) :=
  ⟨treeMx_observable2_of_columnDetermined, treeMx_not_stronglyFair, treeMx_columnDetermined,
    ⟨fun _ => Act2.b, (0, fun _ => Classical.arbitrary _), treeMx_in _ _⟩,
    ⟨fun _ => Act2.b, (1, fun _ => Classical.arbitrary _), treeMx_out _ _⟩⟩

/-- **Tree `Mₓ` satisfies dp-core-063's "veridical labelling" premise**: every node is
subtree-veridical under `mObs` (the `d`-copies lie under tails, world `true`; the `e`-node
under heads, world `false`), so the ⟸-refutation `treeMx_backward_refutation` does not escape
the quoted claim through its premise (audit r3 fidelity 2, probe `TreeMxVeridical`).
Source: fable-slop-notes Claim 2.2 (line 47: "For trees with veridical labelling"); audit r3
(fidelity, non-blocking 2)
Kind: N+
Fidelity: exact -/
theorem treeMx_veridical : ∀ d, ∀ q ∈ fiber treeMx d, SubtreeVeridical mObs treeMx q := by
  show ∀ d, ∀ q ∈ fiber treeMx d, ∀ ℓ ∈ leavesBelow treeMx q,
    world treeMx ℓ ∈ mObs (pt treeMx q)
  decide

/-- … and under the trivial label `obs _ = univ` (the reading the β-pair row uses).
Source: fable-slop-notes Claim 2.2 (line 47); audit r3 (fidelity, non-blocking 2)
Kind: L -/
theorem treeMx_veridical_trivial :
    ∀ d, ∀ q ∈ fiber treeMx d, SubtreeVeridical (fun _ => Finset.univ) treeMx q := by
  show ∀ d, ∀ q ∈ fiber treeMx d, ∀ ℓ ∈ leavesBelow treeMx q,
    world treeMx ℓ ∈ (Finset.univ : Finset Bool)
  decide

/-! ### T3's third branch: observable at `Loc d` while coverage fails -/

/-- A tree whose single `d`-node is subtree-veridical while an `O_d`-leaf lies outside every
`d`-node: a fair coin; tails → the `d`-node with both leaves in `O_d = {true}`; heads → a leaf
with world `true` and no decision node. **Degenerate for observability** (audit r3 adversarial
B1): every world of this tree is `true ∈ O_d`, so `S_{O_d}` contains the whole image of
`Loc () uncovTree` and only one cell is realized. The N+ witness of T3's third branch is
`uncov3` below; this tree is kept for its coverage-fails conjunct only.
Source: cf-correspondence CF-10 (line 47: coverage is not needed for observability);
mandate T3 ("the third-branch coverage-fails variant")
Kind: D -/
def uncovTree : Tree Bool Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair
    ![.decision () fun act => .leaf true (if act = .a then 1 else 0), .leaf true 0]

/-- Every `d`-node of `uncovTree` is subtree-veridical under `trueObs`.
Source: mandate T3
Kind: L -/
theorem uncovTree_veridical : ∀ q ∈ fiber uncovTree (), SubtreeVeridical trueObs uncovTree q := by
  show ∀ q ∈ fiber uncovTree (), ∀ ℓ ∈ leavesBelow uncovTree q,
    world uncovTree ℓ ∈ trueObs (pt uncovTree q)
  decide

/-- Every leaf of `uncovTree` records the world `true`: the reason its observability conjunct
is degenerate (audit r3 adversarial probe `UncovTrivial`).
Source: audit r3 (adversarial B1)
Kind: L -/
theorem uncovTree_world (ℓ : uncovTree.Leaves) : world uncovTree ℓ = true := by
  revert ℓ; decide

/-- Observable at `Loc d` while coverage fails — **N−** (regraded in repair round 3): `S_{O_d}`
is observable at `Loc () uncovTree`, but for the trivial reason (`uncovTree_world`: every
outcome lies in `S_{O_d}`, one cell), not through the Local Theorem's content; the second
conjunct is real — for *every* procedure `C` the tree does not cover `d`, since the heads
leaf has world in `O_d`, positive mass `½`, and passes no `d`-node. The N+ statement is
`uncov3_observable2_loc_not_covers`.
Source: cf-correspondence CF-10 (lines 43–47); mandate T3; audit r3 (adversarial B1)
Kind: N-
Fidelity: weaker: the observability conjunct is trivially true on this tree (whole image in
`S`); CF-10 line 47's witness is the three-branch mugging variant `uncov3` -/
theorem uncovTree_observable2_loc_not_covers :
    Observable2 (Loc () uncovTree) (SO trueObs ()) ∧
    ∀ C : Proc Unit (fun _ => Act2) ℚ, ¬ Covers trueObs C uncovTree () := by
  refine ⟨observable2_loc_of_subtreeVeridical trueObs uncovTree () uncovTree_veridical, ?_⟩
  intro C hcov
  have h := hcov ⟨1, ()⟩ (by
      show 0 < FinDistr.fair.w 1 * 1
      norm_num [FinDistr.fair, FinDistr.coin])
    (by show (true : Bool) ∈ trueObs (); decide)
  exact absurd h (by decide)

/-- The tails subtree of `uncov3`: a fair coin; index `0` → the `d`-node with both leaves in
`O_d = {true}` (payoff `1` after `a`, `0` after `b`); index `1` → an unconsulted leaf in `O_d`
with payoff `0` (CF-10 line 47's "`(T, ⊥, 0)`").
Source: cf-correspondence CF-10 (line 47: "a third root-chance branch to an unconsulted
`(T,⊥,0)`-leaf"); audit r3 (adversarial B1, probe `UncovThreeBranch`)
Kind: D -/
def uncovTails : Tree Bool Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair
    ![.decision () fun act => .leaf true (if act = .a then 1 else 0), .leaf true 0]

/-- **The mugging variant with an unconsulted `O_d`-leaf** (CF-10 line 47's witness shape):
a fair root coin; index `0` (tails) → `uncovTails`; index `1` (heads) → a leaf *outside*
`O_d` (world `false`, no decision node). The heads branch is what keeps the `Sᶜ`-cell
realized; the third branch (inside `uncovTails`) is what breaks coverage.
Source: cf-correspondence CF-10 (line 47); mandate T3 ("the third-branch mugging variant");
audit r3 (adversarial B1)
Kind: D -/
def uncov3 : Tree Bool Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair ![uncovTails, .leaf false 0]

/-- The world of a leaf of `uncov3` is its root coin (`true` on tails, `false` on heads).
Source: none: infrastructure
Kind: L -/
theorem uncov3_world (ℓ : uncov3.Leaves) : world uncov3 ℓ = decide (ℓ.1 = 0) := by
  revert ℓ; decide

/-- Every `d`-node of `uncov3` is subtree-veridical under `trueObs` (the Local Theorem's full
hypothesis package).
Source: mandate T3; cf-correspondence CF-10 (line 47)
Kind: N+
Fidelity: exact -/
theorem uncov3_veridical : ∀ q ∈ fiber uncov3 (), SubtreeVeridical trueObs uncov3 q := by
  show ∀ q ∈ fiber uncov3 (), ∀ ℓ ∈ leavesBelow uncov3 q, world uncov3 ℓ ∈ trueObs (pt uncov3 q)
  decide

/-- `S_{O_d}` is observable at `Loc () uncov3`, by the Local Theorem.
Source: cf-correspondence CF-10 (line 47); mandate T3
Kind: C
Fidelity: exact -/
theorem uncov3_observable2_loc : Observable2 (Loc () uncov3) (SO trueObs ()) :=
  observable2_loc_of_subtreeVeridical trueObs uncov3 () uncov3_veridical

/-- The cell of an outcome of `Loc () uncov3` is its root coin: tails columns land in
`S_{O_d}`, heads columns outside it (for every row and every other-point answer).
Source: cf-correspondence CF-10 (line 47)
Kind: L -/
theorem uncov3_loc_mem_iff (x : Act2) (q : (e : {e : Unit // e ≠ ()}) → Act2) :
    ∀ ε : ChanceProfile uncov3, (Loc () uncov3).outcome x (q, ε) ∈ SO trueObs () ↔ ε.1 = 0
  | (i, f) => by
    rw [mem_SO]
    show world uncov3 (runLeaf (extend () x q) uncov3 (i, f)) ∈ trueObs () ↔ i = 0
    rw [uncov3_world]
    show decide (i = 0) ∈ trueObs () ↔ i = 0
    revert i; decide

/-- **Both cells of `S_{O_d}` are realized at `Loc () uncov3`**: a tails column lies in the
`S`-cell, a heads column in the `Sᶜ`-cell.
Source: cf-correspondence CF-10 (line 47); audit r3 (adversarial B1)
Kind: N+
Fidelity: exact -/
theorem uncov3_both_cells :
    (∃ x p, (Loc () uncov3).outcome x p ∈ SO trueObs ()) ∧
    (∃ x p, (Loc () uncov3).outcome x p ∉ SO trueObs ()) :=
  ⟨⟨.a, (noOther, (0, fun _ => Classical.arbitrary _)), (uncov3_loc_mem_iff _ _ _).2 rfl⟩,
    ⟨.a, (noOther, (1, fun _ => Classical.arbitrary _)),
      fun h => absurd ((uncov3_loc_mem_iff _ _ _).1 h) (by decide)⟩⟩

/-- The payoff of a run of `uncovTails` that takes its tails edge is `1` after `a` and `0`
after `b`: the `d`-node is consulted.
Source: none: infrastructure
Kind: L -/
theorem uncovTails_payoff_tails (π : Unit → Act2) :
    ∀ ε : ChanceProfile uncovTails, ε.1 = 0 →
      payoff uncovTails (runLeaf π uncovTails ε) = if π () = .a then 1 else 0
  | (j, g), hj => by
    have hj' : j = 0 := hj
    subst hj'
    rfl

/-- **The `d`-node of `uncov3` is consulted inside the `S`-cell**: on a tails-tails column the
rows `a` and `b` have different outcomes (payoff `1` vs `0`), so the agent of `Loc () uncov3`
is not inert and the observability of `S_{O_d}` is not that of a trivial frame.
Source: audit r3 (adversarial B1: "exercises the content"); [[STANDARDS]] §3 (N+)
Kind: N+
Fidelity: exact -/
theorem uncov3_d_consulted (q : (e : {e : Unit // e ≠ ()}) → Act2) :
    ∀ ε : ChanceProfile uncov3, ε.1 = 0 → (ε.2 0).1 = 0 →
      (Loc () uncov3).outcome .a (q, ε) ≠ (Loc () uncov3).outcome .b (q, ε)
  | (i, f), hi, h0 => by
    have hi' : i = 0 := hi
    subst hi'
    intro h
    have ha := congrArg Prod.snd h
    change payoff uncovTails (runLeaf (extend () Act2.a q) uncovTails (f 0)) =
      payoff uncovTails (runLeaf (extend () Act2.b q) uncovTails (f 0)) at ha
    rw [uncovTails_payoff_tails _ _ h0, uncovTails_payoff_tails _ _ h0, extend_self,
      extend_self] at ha
    norm_num at ha
    exact absurd ha (by decide)

/-- A tails-tails column of `uncov3`: root coin `0`, inner coin `0` (the run reaches the
`d`-node); the unconsulted coordinates arbitrary.
Source: none: infrastructure
Kind: D -/
noncomputable def uncovεTT : ChanceProfile uncov3 :=
  (0, Fin.cons (α := fun i : Fin 2 =>
      ChanceProfile (![uncovTails, (Tree.leaf false 0 : Tree Bool Unit (fun _ => Act2) ℚ)] i))
    ((0, fun _ => Classical.arbitrary _) : ChanceProfile uncovTails)
    (fun _ => Classical.arbitrary _))

/-- The tails-tails column has root coin `0` and inner coin `0`.
Source: none: infrastructure
Kind: L -/
theorem uncovεTT_spec : uncovεTT.1 = 0 ∧ (uncovεTT.2 0).1 = 0 := ⟨rfl, rfl⟩

/-- **Coverage fails for every procedure**: the tails-heads leaf has mass `¼`, world
`true ∈ O_d`, and passes no `d`-node.
Source: cf-correspondence CF-10 (line 47: "despite coverage failing"); mandate T3
Kind: N+
Fidelity: exact -/
theorem uncov3_not_covers : ∀ C : Proc Unit (fun _ => Act2) ℚ, ¬ Covers trueObs C uncov3 () := by
  intro C hcov
  have h := hcov ⟨0, ⟨1, ()⟩⟩ (by
      show 0 < FinDistr.fair.w 0 * (FinDistr.fair.w 1 * 1)
      norm_num [FinDistr.fair, FinDistr.coin])
    (by show (true : Bool) ∈ trueObs (); decide)
  exact absurd h (by decide)

/-- **Observable at `Loc d` while coverage fails** (T3's third branch, N+): on CF-10 line 47's
mugging variant `uncov3`, `S_{O_d}` is observable at `Loc () uncov3` by the Local Theorem,
**both cells are realized**, the `d`-node is consulted with distinct outcomes inside the
`S`-cell, and for *every* procedure `C` the tree does not cover `d`. Coverage is neither a
hypothesis nor a consequence of the Local Theorem.
Source: cf-correspondence CF-10 (lines 43–47); mandate T3; audit r3 (adversarial B1)
Kind: N+
Fidelity: exact -/
theorem uncov3_observable2_loc_not_covers :
    Observable2 (Loc () uncov3) (SO trueObs ()) ∧
    (∃ x p, (Loc () uncov3).outcome x p ∈ SO trueObs ()) ∧
    (∃ x p, (Loc () uncov3).outcome x p ∉ SO trueObs ()) ∧
    (∃ p, (Loc () uncov3).outcome .a p ≠ (Loc () uncov3).outcome .b p) ∧
    ∀ C : Proc Unit (fun _ => Act2) ℚ, ¬ Covers trueObs C uncov3 () :=
  ⟨uncov3_observable2_loc, uncov3_both_cells.1, uncov3_both_cells.2,
    ⟨(noOther, uncovεTT), uncov3_d_consulted noOther uncovεTT uncovεTT_spec.1 uncovεTT_spec.2⟩,
    uncov3_not_covers⟩

end Cleanroom.Decision.DpCartesianFrames

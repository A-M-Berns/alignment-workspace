import Cleanroom.Found.DpCoreTree.NodeSums
import Cleanroom.Found.DpCoreTree.Witnesses

/-!
# "Recording = F3′ + exactly one" — refuted as stated, repaired

T5 stretch of [[dp-core-tree-mandate]]: dp-cf-2-001 asserts, without proof, that for
full-support `C`, Definition 7 recording equals F3′ act-recording plus "no other `d`-node on an
`O_d`-run".

* **Refuted as stated** (`twoBranch_recordsFor_not_actRecording`): F3′'s clause (i) ("every
  node-action-veridical `d`-node is subtree-veridical") quantifies over *all* `d`-nodes,
  including simulation nodes off the `O_d`-runs, about which Definition 7 says nothing. The
  two-branch tree — a fair coin, then a `d`-node in each branch whose leaves record the act,
  with `O_d` true in one branch only — is recorded at `d` for every procedure (so for every
  full-support one) and meets `d` once on every run, yet the off-`O_d` node is
  node-action-veridical and not subtree-veridical. The identity fails in the direction
  "recording ⟹ F3′".
* **Repaired** (`recordsFor_iff_actRecordingOn`): with clause (i) restricted to the `d`-nodes
  met on positive `O_d`-runs (`ActRecordingOn`), and under Definition 3's disjointness of the
  action events, recording is equivalent to `ActRecordingOn` plus exactly one `d`-node on every
  positive `O_d`-run — for **every** procedure, full support not needed, provided the
  node-action-veridicality clause is read a.s. (`NodeActionVeridicalAS`, on positive leaves);
  with all chance edges positive and `C` of full support the a.s. reading is the plain one.
  (Clause (i) keeps Definition 7's plain subtree-veridicality, as the definition of record does.)
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Found.DpCoreTree

open Finset Catalogue Tree

/-! ### The refutation -/

/-- Two-branch worlds `(o, act)`: whether the observation holds, and the recorded act.
Source: mandate T5 (stretch); dp-cf-2-001 (the claim refuted)
Kind: D -/
abbrev TwoBranchW : Type := Bool × Act2

/-- **The two-branch tree**: a fair coin (index `0` = `o = 1`), then a `d`-node in each branch
whose leaves record the act; `O_d = {o = 1}`.
Source: mandate T5 (stretch): a counterexample to dp-cf-2-001's identity
Kind: D -/
def twoBranch : Tree TwoBranchW Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i => .decision () fun act => .leaf (decide (i = 0), act) 0

/-- `O_d = {o = 1}`. Source: mandate T5. Kind: D -/
def tbObs : Unit → Finset TwoBranchW := fun _ => Finset.univ.filter fun w => w.1 = true

/-- Action events `{act = ·}`. Source: mandate T5. Kind: D -/
def tbActEv (_ : Unit) (act : Act2) : Finset TwoBranchW := Finset.univ.filter fun w => w.2 = act

/-- The two-branch tree is recorded at `d` for every procedure.
Source: mandate T5 (stretch)
Kind: N+ -/
theorem twoBranch_recordsFor (C : Proc Unit (fun _ => Act2) ℚ) :
    RecordsFor tbObs tbActEv C twoBranch () := by
  intro ℓ _ hobs
  unfold twoBranch at ℓ hobs ⊢
  rcases ℓ with ⟨i, act, _⟩
  refine ⟨rfl, ?_⟩
  rintro ⟨i', (_ | ⟨b, q⟩)⟩ hq a ha
  · by_cases hi : i = i'
    · subst hi
      simp only [edgeOf_chance, dite_true, edgeOf_decision_none, Option.some.injEq] at ha
      subst ha
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨j, b, _⟩ hj
        rw [mem_leavesBelow] at hj
        by_cases hji : j = i
        · subst hji
          simp only [tbObs, Finset.mem_filter, Finset.mem_univ, true_and] at hobs ⊢
          simpa using hobs
        · simp [edgeOf_chance, hji] at hj
      · simp [tbActEv]
      · intro a' ha'
        simp [tbActEv] at ha'
        first | exact ha'.symm | exact ha'
    · simp [edgeOf_chance, hi] at ha
  · exact q.elim

/-- Every run of the two-branch tree meets `d` exactly once.
Source: mandate T5 (stretch)
Kind: L -/
theorem twoBranch_count (ℓ : twoBranch.Leaves) : count () twoBranch ℓ = 1 := by
  unfold twoBranch at ℓ ⊢
  rcases ℓ with ⟨i, act, _⟩
  rfl

/-- The off-`O_d` node of the two-branch tree is node-action-veridical.
Source: mandate T5 (stretch)
Kind: L -/
theorem twoBranch_offNode_nav :
    NodeActionVeridical tbActEv twoBranch ⟨1, none⟩ := by
  intro ℓ a ha
  unfold twoBranch at ℓ ha ⊢
  rcases ℓ with ⟨i, act, _⟩
  by_cases hi : i = 1
  · subst hi
    simp only [edgeOf_chance, dite_true, edgeOf_decision_none, Option.some.injEq] at ha
    subst ha
    simp [tbActEv]
  · simp [edgeOf_chance, hi] at ha

/-- …but not subtree-veridical.
Source: mandate T5 (stretch)
Kind: L -/
theorem twoBranch_offNode_not_sv :
    ¬ SubtreeVeridical tbObs twoBranch ⟨1, none⟩ := by
  intro h
  have := h ⟨1, .a, ()⟩ (by
    unfold twoBranch
    rw [mem_leavesBelow, edgeOf_chance, dif_pos rfl]
    rfl)
  unfold twoBranch at this
  simp [tbObs] at this

/-- **dp-cf-2-001's identity is false as stated**: the two-branch tree is recorded at `d` for
every procedure (in particular for every full-support one) and meets `d` exactly once on every
run, yet it is not F3′ act-recording, because a node-action-veridical simulation node off the
`O_d`-runs is not subtree-veridical.
Source: `cf-workflow/phase2-notes/repair/faithful.md` line 40 ("for full-support `C`, Def 7
recording `=` F3′ `+` 'no other `d`-node on an `O_d`-run'"), restated in dp-cf-2-001 ("Lemma
(stated) …", flagged there as "asserted … without a written proof")
Kind: N−
Fidelity: exact (the refuted reading is the literal wording: F3′'s clause (i), "every
node-action-veridical `d`-node is subtree-veridical", quantifies over all `d`-nodes, simulation
nodes off the `O_d`-runs included; the reading with clause (i) restricted to active nodes is
the repaired identity `recordsFor_iff_actRecordingOn`, which holds) -/
theorem twoBranch_recordsFor_not_actRecording (C : Proc Unit (fun _ => Act2) ℚ) :
    RecordsFor tbObs tbActEv C twoBranch () ∧
    (∀ ℓ, count () twoBranch ℓ = 1) ∧
    ¬ ActRecording tbObs tbActEv C twoBranch () := by
  refine ⟨twoBranch_recordsFor C, twoBranch_count, fun h => ?_⟩
  exact twoBranch_offNode_not_sv (h.1 ⟨1, none⟩ rfl twoBranch_offNode_nav)

/-! ### The repair -/

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] [DecidableEq ι]

namespace Tree

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)

/-- Node-action-veridicality a.s.: every positive-mass leaf below `q` taking edge `a` has its
world in the action event `a`.
Source: `faithful.md` F3′, read "`μ_{B,C}`-a.s." like Definition 7
Kind: D -/
def NodeActionVeridicalAS (C : Proc ι acts K) (B : Tree Ω ι acts K) (q : B.DecNode) : Prop :=
  ∀ ℓ a, 0 < leafLaw C B ℓ → edgeOf B q ℓ = some a → world B ℓ ∈ actEv (pt B q) a

/-- **F3′ restricted to the `d`-nodes met on positive `O_d`-runs** (the repair of dp-cf-2-001):
every such node that is a.s. node-action-veridical is a.s. subtree-veridical, and every
positive `O_d`-run passes exactly one a.s. node-action-veridical `d`-node.
Source: `faithful.md` F3′ with clause (i) restricted to active nodes; mandate T5 (stretch)
Kind: D -/
def ActRecordingOn (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) : Prop :=
  (∀ q, pt B q = d → (∃ ℓ, 0 < leafLaw C B ℓ ∧ world B ℓ ∈ obs d ∧ (edgeOf B q ℓ).isSome) →
    NodeActionVeridicalAS actEv C B q → SubtreeVeridical obs B q) ∧
  ∀ ℓ, 0 < leafLaw C B ℓ → world B ℓ ∈ obs d →
    ∃! q, q ∈ dNodesOn B d ℓ ∧ NodeActionVeridicalAS actEv C B q

/-- **The repaired identity**: under pairwise-disjoint action events (Definition 3), recording
at `d` for `C` is equivalent to `ActRecordingOn` together with exactly one `d`-node on every
positive `O_d`-run — for every procedure. The content is the (⇐) direction (disjointness turns
clause 3 into clause 4; subtree-veridicality of the active node makes every positive leaf below
it count); in (⇒) clause (i)'s antecedent is inert and the uniqueness is redundant under
`#_d = 1`.
Source: `cf-workflow/phase2-notes/repair/faithful.md` line 40 (the identity as stated, via
dp-cf-2-001), repaired; [[decision-problems-v2]] Definition 3 ("pairwise disjoint as events"),
Definition 7
Kind: C
Fidelity: variant: F3′'s clause (i) restricted to nodes on positive `O_d`-runs and
node-action-veridicality read a.s.; the plain reading is the special case of full-support `C`
on a tree with all chance edges positive
Hyps: none (disjointness is Definition 3's constraint on action events, carried as a hypothesis) -/
theorem recordsFor_iff_actRecordingOn (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)
    (hdisj : ∀ a a' : acts d, a ≠ a' → Disjoint (actEv d a) (actEv d a')) :
    RecordsFor obs actEv C B d ↔
      ActRecordingOn obs actEv C B d ∧
        ∀ ℓ, 0 < leafLaw C B ℓ → world B ℓ ∈ obs d → count d B ℓ = 1 := by
  constructor
  · intro hrec
    refine ⟨⟨?_, ?_⟩, fun ℓ hpos hobs => (hrec ℓ hpos hobs).1⟩
    · -- an active node is subtree-veridical (Definition 7, clause 2, at any leaf reaching it)
      rintro q hq ⟨ℓ₀, hpos₀, hobs₀, he₀⟩ _
      obtain ⟨a₀, ha₀⟩ := Option.isSome_iff_exists.mp he₀
      exact ((hrec ℓ₀ hpos₀ hobs₀).2 q hq a₀ ha₀).1
    · intro ℓ hpos hobs
      obtain ⟨q₀, hq₀⟩ := by
        have h := (hrec ℓ hpos hobs).1
        rw [count_eq_card_dNodesOn] at h
        exact Finset.card_eq_one.mp h
      have hmem : q₀ ∈ dNodesOn B d ℓ := by rw [hq₀]; exact Finset.mem_singleton_self _
      refine ⟨q₀, ⟨hmem, ?_⟩, fun q ⟨hq, _⟩ => by rw [hq₀] at hq; exact Finset.mem_singleton.mp hq⟩
      -- the unique node is a.s. node-action-veridical: every positive leaf below it is on an
      -- `O_d`-run (clause 2) whose instance is action-veridical (clause 3)
      intro ℓ' a hpos' ha
      rw [mem_dNodesOn] at hmem
      obtain ⟨hpt, he⟩ := hmem
      obtain ⟨a₀, ha₀⟩ := Option.isSome_iff_exists.mp he
      have hsv := ((hrec ℓ hpos hobs).2 q₀ hpt a₀ ha₀).1
      have hobs' : world B ℓ' ∈ obs d := by
        have := hsv ℓ' ((mem_leavesBelow B q₀ ℓ').mpr (by rw [ha]; rfl))
        rwa [hpt] at this
      exact ((hrec ℓ' hpos' hobs').2 q₀ hpt a ha).2.1
  · rintro ⟨⟨hsv, huniq⟩, hone⟩ ℓ hpos hobs
    refine ⟨hone ℓ hpos hobs, fun q hq a ha => ?_⟩
    subst hq
    -- `q` is the unique `d`-node on the path, hence the a.s.-node-action-veridical one
    obtain ⟨q₁, ⟨hq₁, hnav₁⟩, hu⟩ := huniq ℓ hpos hobs
    have hq_mem : q ∈ dNodesOn B (pt B q) ℓ := by
      rw [mem_dNodesOn]; exact ⟨rfl, by rw [ha]; rfl⟩
    have hqq₁ : q = q₁ := by
      have h1 := hone ℓ hpos hobs
      rw [count_eq_card_dNodesOn] at h1
      obtain ⟨q₂, hq₂⟩ := Finset.card_eq_one.mp h1
      rw [hq₂, Finset.mem_singleton] at hq_mem hq₁
      rw [hq_mem, hq₁]
    subst hqq₁
    have hact : world B ℓ ∈ actEv (pt B q) a := hnav₁ ℓ a hpos ha
    refine ⟨hsv q rfl ⟨ℓ, hpos, hobs, by rw [ha]; rfl⟩ hnav₁, hact, fun a' ha' => ?_⟩
    by_contra hne
    have hd := hdisj a' a hne
    exact Finset.disjoint_left.mp hd ha' hact

end Tree

end Cleanroom.Found.DpCoreTree

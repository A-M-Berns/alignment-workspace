import Cleanroom.Decision.DpFairnessReloc.Output
import Cleanroom.Decision.DpFairnessReloc.Witnesses

/-!
# Further witnesses (repair round 1)

Package `dp-fairness-reloc`, file 12. Constructions adopted from the round-1 audit probes
(`run/wp/dp-fairness-reloc/audit-r1-probes/Vacuity.lean`, adversarial lens), re-documented:

* **Chance-free trees** satisfy `EventedChance` and `Pruned` for free (`NoChance.eventedChance`,
  `NoChance.pruned`); the Claim B witness `twoSeq` is chance-free (`twoSeq_noChance`), which
  regrades `twoSeq_claimB` to N− for those two hypotheses.
* **`coinSeq`** — Claim B's hypotheses jointly on a tree *with* chance (a fair coin; heads: a
  `d`-node whose leaves record the coin and the act; tails: a plain leaf), EC and Pruned
  exercised. The N+ the `singleton_fibers` row needs (`coinSeq_claimB`).
* **`dd`** — realized observations are load-bearing in Claim B: an `e`-node over two equal
  `d`-nodes with `obs ≡ ∅` satisfies the other four hypotheses and has a two-member fiber
  (`hreal_load_bearing`).
* **`gr3W`** — GR-9's repaired example (3) with `Bool` worlds recording the `1`-vs-`3` outcome:
  law-fair, not strongly fair, two-member fiber, and `ν_{T_q}({true}) = 1/3` under `a`, so the
  fork-closure instance `gr3W_fork_true` at `X = {true}` is a genuine statistic (the N+ the
  fork-closure row needs; on the `Unit`-world `gr3` every `X` is trivial).
* **`cb`** — adversary-repair Claim B's tree (fair coin; T: a `d`-node with an `e`-node below
  each answer; H: a hypothetical `d`-node over plain leaves): not strongly fair, `{d}` closed for
  it, so `Closed.stronglyFair_output` applies between the trivial ends (`cb_output_stronglyFair`,
  N+) with a two-member `inl e`-fiber in the output; and with the `pol` stamps kept the output is
  **not** strongly fair (`cb_reloc_not_stronglyFair`) — FR-4 as stated refuted on the source's
  own tree (the N− row findings F1 recorded as pending).
-/

namespace Cleanroom.Decision.DpFairnessReloc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

/-! ### Chance-free trees: EC and Pruned are vacuous -/

/-- A tree with no chance node.
Source: none: audit r1 (adversarial) probe A
Kind: D -/
def NoChance : Tree Ω ι acts K → Prop
  | .leaf _ _ => True
  | .chance _ _ _ => False
  | .decision _ child => ∀ x, NoChance (child x)

/-- Without chance nodes `EventedChance` holds for free.
Source: none: audit r1 (adversarial) probe A
Kind: L -/
theorem NoChance.eventedChance : (T : Tree Ω ι acts K) → NoChance T → EventedChance T
  | .leaf _ _, _ => trivial
  | .chance _ _ _, h => h.elim
  | .decision _ child, h => fun x => NoChance.eventedChance (child x) (h x)

/-- Without chance nodes `Pruned` holds for free (every chance weight is `1`).
Source: none: audit r1 (adversarial) probe A
Kind: L -/
theorem NoChance.pruned : (T : Tree Ω ι acts K) → NoChance T → Pruned T
  | .leaf _ _, _ => fun _ => by unfold Positive; simp
  | .chance _ _ _, h => h.elim
  | .decision _ child, h => fun ⟨x, ℓ⟩ => by
      have := NoChance.pruned (child x) (h x) ℓ
      unfold Positive at this ⊢
      simpa using this

/-- The Claim B witness `twoSeq` has no chance node: on it EC and Pruned are the free instances
above and every fiber is a singleton outright, so `twoSeq_claimB` exercises recording only (N−
for EC, Pruned and strong fairness).
Source: none: audit r1 (adversarial) probe A
Kind: N− -/
theorem twoSeq_noChance : NoChance twoSeq := fun x => by
  cases x
  · exact fun _ => trivial
  · exact trivial

/-! ### `coinSeq`: Claim B's hypotheses on a tree with chance -/

/-- Heads: a `d`-node whose leaves record `(heads, act_d)`.
Source: none: audit r1 (adversarial) probe B
Kind: D -/
def coinT : Tree SeqW GatePt (fun _ => Act2) ℚ := .decision .d fun x => .leaf (.a, x) 0

/-- Tails: a plain leaf recording `(tails, a)`.
Source: none: audit r1 (adversarial) probe B
Kind: D -/
def coinH : Tree SeqW GatePt (fun _ => Act2) ℚ := .leaf (.b, .a) 0

/-- **`coinSeq`**: a fair coin over `coinT` / `coinH`; `O_d = {coin = heads}`, act events on the
second coordinate (the catalogue's `seqObs`, `seqActEv`, reading the coin as `act_e`).
Source: none: audit r1 (adversarial) probe B
Kind: D -/
def coinSeq : Tree SeqW GatePt (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i => Fin.cases coinT (fun _ => coinH) i

theorem coinSeq_fibers_singleton :
    ∀ d, ∀ q ∈ fiber coinSeq d, ∀ q' ∈ fiber coinSeq d, q = q' := by
  decide

theorem coinSeq_stronglyFair : StronglyFair coinSeq := by
  intro d q hq q' hq'
  rw [coinSeq_fibers_singleton d q hq q' hq']
  exact LabIso.refl _

/-- EC is a real constraint on `coinSeq`: two positive edges with disjoint world sets
(`coin = heads` vs `coin = tails`).
Source: none: audit r1 (adversarial) probe B
Kind: N+ -/
theorem coinSeq_eventedChance : EventedChance coinSeq := by
  refine ⟨fun i j hij ℓ ℓ' => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · change coinT.Leaves at ℓ; change coinH.Leaves at ℓ'
      obtain ⟨x, _⟩ := ℓ
      show (Act2.a, x) ≠ (Act2.b, Act2.a)
      simp
    · change coinH.Leaves at ℓ; change coinT.Leaves at ℓ'
      obtain ⟨x, _⟩ := ℓ'
      show (Act2.b, Act2.a) ≠ (Act2.a, x)
      simp
    · exact absurd rfl hij
  · fin_cases i
    · exact fun _ => trivial
    · exact trivial

/-- Pruned is a real constraint on `coinSeq` (a fair coin, both edges `1/2 > 0`).
Source: none: audit r1 (adversarial) probe B
Kind: N+ -/
theorem coinSeq_pruned : Pruned coinSeq := by
  intro ℓ
  obtain ⟨i, ℓ⟩ := ℓ
  fin_cases i
  · change coinT.Leaves at ℓ
    obtain ⟨x, _⟩ := ℓ
    show (0 : ℚ) < FinDistr.fair.w 0 * 1
    rw [show FinDistr.fair.w 0 = 1/2 from rfl]
    norm_num
  · change coinH.Leaves at ℓ
    show (0 : ℚ) < FinDistr.fair.w 1 * 1
    rw [show FinDistr.fair.w 1 = 1 - 1/2 from rfl]
    norm_num

theorem coinSeq_records_d : RecordsForAll seqObs seqActEv coinSeq .d := by
  intro C ℓ _ hobs
  have key : ∀ ℓ : coinSeq.Leaves, world coinSeq ℓ ∈ seqObs .d →
      count .d coinSeq ℓ = 1 ∧
      ∀ q : coinSeq.DecNode, pt coinSeq q = .d → ∀ a, edgeOf coinSeq q ℓ = some a →
        (∀ ℓ' ∈ leavesBelow coinSeq q, world coinSeq ℓ' ∈ seqObs (pt coinSeq q)) ∧
        world coinSeq ℓ ∈ seqActEv (pt coinSeq q) a ∧
        ∀ a', world coinSeq ℓ ∈ seqActEv (pt coinSeq q) a' → a' = a := by decide
  exact key ℓ hobs

theorem coinSeq_queried : queried coinSeq = {.d} := by decide

/-- **Claim B's hypotheses are jointly satisfiable on a tree with chance (N+)**: every hypothesis
of `singleton_fibers` holds on `coinSeq`, with EC and Pruned exercised (a positive two-edge chance
node with a decision node below one edge), and the theorem applies.
Source: `adversary-repair.md` Claim B (its hypothesis class); audit r1 (adversarial) probe B
Kind: N+ -/
theorem coinSeq_claimB :
    StronglyFair coinSeq ∧ EventedChance coinSeq ∧ Pruned coinSeq ∧
      (∀ e ∈ queried coinSeq, RecordsForAll seqObs seqActEv coinSeq e) ∧
      (∀ e ∈ queried coinSeq, ∃ ℓ, Positive coinSeq ℓ ∧ world coinSeq ℓ ∈ seqObs e) ∧
      ∀ d, ∀ q ∈ fiber coinSeq d, ∀ q' ∈ fiber coinSeq d, q = q' := by
  have hrec : ∀ e ∈ queried coinSeq, RecordsForAll seqObs seqActEv coinSeq e := by
    intro e he
    rw [coinSeq_queried, Finset.mem_singleton] at he
    subst he
    exact coinSeq_records_d
  have hreal : ∀ e ∈ queried coinSeq, ∃ ℓ, Positive coinSeq ℓ ∧ world coinSeq ℓ ∈ seqObs e := by
    intro e he
    rw [coinSeq_queried, Finset.mem_singleton] at he
    subst he
    refine ⟨⟨0, ⟨.a, ()⟩⟩, coinSeq_pruned _, ?_⟩
    decide
  exact ⟨coinSeq_stronglyFair, coinSeq_eventedChance, coinSeq_pruned, hrec, hreal,
    singleton_fibers seqObs seqActEv coinSeq_stronglyFair coinSeq_eventedChance coinSeq_pruned
      (fun e he => hrec e he Proc.uniform) hreal⟩

/-! ### Realized observations are load-bearing in Claim B -/

/-- An `e`-node over two literally equal `d`-nodes.
Source: none: audit r1 (adversarial) probe C
Kind: D -/
def dd : Tree Unit GatePt (fun _ => Act2) ℚ :=
  .decision .e fun _ => .decision .d fun _ => .leaf () 0

/-- Empty observations. Source: none: audit r1 (adversarial) probe C. Kind: D -/
def emptyObs : GatePt → Finset Unit := fun _ => ∅

/-- Empty act events. Source: none: audit r1 (adversarial) probe C. Kind: D -/
def emptyActEv : (_ : GatePt) → Act2 → Finset Unit := fun _ _ => ∅

theorem dd_stronglyFair : StronglyFair dd := by
  intro p q hq q' hq'
  rw [mem_fiber] at hq hq'
  rcases q with _ | ⟨x, _ | ⟨y, e⟩⟩ <;> rcases q' with _ | ⟨x', _ | ⟨y', e'⟩⟩
  · exact LabIso.refl _
  · have h := hq.trans hq'.symm
    change GatePt.e = GatePt.d at h
    cases h
  · exact e'.elim
  · have h := hq.trans hq'.symm
    change GatePt.d = GatePt.e at h
    cases h
  · exact LabIso.refl _
  · exact e'.elim
  · exact e.elim
  · exact e.elim
  · exact e.elim

/-- With `obs ≡ ∅`, recording holds vacuously at every point for every procedure.
Source: none: audit r1 (adversarial) probe C
Kind: N− -/
theorem dd_records (p : GatePt) : RecordsForAll emptyObs emptyActEv dd p := by
  intro C ℓ _ h
  simp [emptyObs] at h

/-- **The realized-observation hypothesis cannot be dropped from `singleton_fibers`**: `dd`
satisfies the other four hypotheses and has a two-member `d`-fiber.
Source: none: audit r1 (adversarial) probe C
Kind: N+ -/
theorem hreal_load_bearing :
    StronglyFair dd ∧ EventedChance dd ∧ Pruned dd ∧
      (∀ e ∈ queried dd, RecordsForAll emptyObs emptyActEv dd e) ∧
      ¬ (∀ d, ∀ q ∈ fiber dd d, ∀ q' ∈ fiber dd d, q = q') := by
  refine ⟨dd_stronglyFair, fun _ _ => trivial, ?_, fun e _ => dd_records e, ?_⟩
  · rintro ⟨_, ⟨_, _⟩⟩
    show (0 : ℚ) < 1
    norm_num
  · decide

/-! ### Fork closure with a non-trivial world event: `gr3W` -/

/-- GR-9 (3), left member, with `Bool` worlds recording the outcome: `a → ⅓ (true, 1) / ⅔
(false, 3)`, `b → (false, 0)`.
Source: `grounding.md` GR-9 example (3) repaired, with worlds; audit r1 (adversarial) probe D
Kind: D -/
def gr3WL : Tree Bool Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => .chance 2 (FinDistr.coin (1/3) (by norm_num) (by norm_num))
        fun i => .leaf (i = 0) (if i = 0 then 1 else 3)
    | .b => .leaf Bool.false 0

/-- GR-9 (3), right member, with `Bool` worlds: `a → ⅓ (true, 1) / ⅓ (false, 3) / ⅓ (false, 3)`,
`b → (false, 0)`.
Source: `grounding.md` GR-9 example (3) repaired, with worlds; audit r1 (adversarial) probe D
Kind: D -/
def gr3WR : Tree Bool Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => .chance 3 FinDistr.third fun i => .leaf (i = 0) (if i = 0 then 1 else 3)
    | .b => .leaf Bool.false 0

/-- The two members on the branches of a fair coin.
Source: `grounding.md` GR-9 example (3); audit r1 (adversarial) probe D
Kind: D -/
def gr3W : Tree Bool Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i => Fin.cases gr3WL (fun _ => gr3WR) i

theorem gr3W_contLaw_eq (C : Proc Unit (fun _ => Act2) ℚ) : contLaw C gr3WL = contLaw C gr3WR := by
  have hL : contLaw C gr3WL = (C ()).w .a • ((1/3 : ℚ) • Finsupp.single (Bool.true, (1 : ℚ)) (1 : ℚ) +
      (1 - 1/3 : ℚ) • Finsupp.single (Bool.false, (3 : ℚ)) (1 : ℚ)) +
      (C ()).w .b • Finsupp.single (Bool.false, (0 : ℚ)) (1 : ℚ) := by
    unfold gr3WL
    rw [contLaw_decision, Act2.sum_univ]
    show (C ()).w .a • contLaw C (.chance 2 (FinDistr.coin (1/3) (by norm_num) (by norm_num))
        fun i => .leaf (decide (i = 0)) (if i = 0 then 1 else 3)) +
      (C ()).w .b • contLaw C (.leaf Bool.false 0) = _
    rw [contLaw_chance, Fin.sum_univ_two, coin_w_zero, coin_w_one]
    simp
  have hR : contLaw C gr3WR = (C ()).w .a • ((1/3 : ℚ) • Finsupp.single (Bool.true, (1 : ℚ)) (1 : ℚ) +
      (1/3 : ℚ) • Finsupp.single (Bool.false, (3 : ℚ)) (1 : ℚ) +
      (1/3 : ℚ) • Finsupp.single (Bool.false, (3 : ℚ)) (1 : ℚ)) +
      (C ()).w .b • Finsupp.single (Bool.false, (0 : ℚ)) (1 : ℚ) := by
    unfold gr3WR
    rw [contLaw_decision, Act2.sum_univ]
    show (C ()).w .a • contLaw C (.chance 3 FinDistr.third
        fun i => .leaf (decide (i = 0)) (if i = 0 then 1 else 3)) +
      (C ()).w .b • contLaw C (.leaf Bool.false 0) = _
    rw [contLaw_chance, Fin.sum_univ_three, third_w, third_w, third_w]
    simp
  rw [hL, hR]
  ext p
  simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> ring

theorem gr3W_subtree (q : gr3W.DecNode) : subtreeAt gr3W q = gr3WL ∨ subtreeAt gr3W q = gr3WR := by
  obtain ⟨i, q⟩ := q
  fin_cases i
  · change gr3WL.DecNode at q
    rcases q with _ | ⟨a, q⟩
    · exact Or.inl rfl
    · cases a
      · change (Tree.chance 2 (FinDistr.coin (1/3) (by norm_num) (by norm_num)) fun i =>
          Tree.leaf (i = 0) (if i = 0 then 1 else 3) : Tree Bool Unit (fun _ => Act2) ℚ).DecNode at q
        obtain ⟨i, q⟩ := q
        change Empty at q
        exact q.elim
      · change Empty at q
        exact q.elim
  · change gr3WR.DecNode at q
    rcases q with _ | ⟨a, q⟩
    · exact Or.inr rfl
    · cases a
      · change (Tree.chance 3 FinDistr.third fun i =>
          Tree.leaf (i = 0) (if i = 0 then 1 else 3) : Tree Bool Unit (fun _ => Act2) ℚ).DecNode at q
        obtain ⟨i, q⟩ := q
        change Empty at q
        exact q.elim
      · change Empty at q
        exact q.elim

/-- `gr3W` is law-fair (every procedure).
Source: `grounding.md` GR-9 example (3); audit r1 (adversarial) probe D
Kind: N+ -/
theorem gr3W_lawFair : LawFair gr3W := by
  intro d q _ q' _ C
  rcases gr3W_subtree q with h | h <;> rcases gr3W_subtree q' with h' | h' <;> rw [h, h']
  · exact gr3W_contLaw_eq C
  · exact (gr3W_contLaw_eq C).symm

/-- `gr3W` is not strongly fair (arity `2 ≠ 3`).
Source: `grounding.md` GR-9 example (3); audit r1 (adversarial) probe D
Kind: N+ -/
theorem gr3W_not_stronglyFair : ¬ StronglyFair gr3W := by
  intro h
  have := h () ⟨0, none⟩ (by simp [mem_fiber]) ⟨1, none⟩ (by simp [mem_fiber])
  change LabIso gr3WL gr3WR at this
  have h2 := (LabIso.decision_inj this) .a
  exact absurd (LabIso.chance_arity h2) (by decide)

/-- The two `d`-nodes of `gr3W` are distinct members of its fiber.
Source: none: audit r1 (adversarial) probe D
Kind: L -/
theorem gr3W_fiber_two :
    (⟨0, none⟩ : gr3W.DecNode) ∈ fiber gr3W () ∧ (⟨1, none⟩ : gr3W.DecNode) ∈ fiber gr3W () ∧
      (⟨0, none⟩ : gr3W.DecNode) ≠ ⟨1, none⟩ := by
  decide

/-- `X = {true}` is a non-trivial event on the members: `ν_{T_q}({true}) = 1/3` under `a`.
Source: none: audit r1 (adversarial) probe D
Kind: N+ -/
theorem gr3WL_nu_true : nu (pureProc .a) gr3WL {Bool.true} = 1/3 := by
  unfold nu mass worldEv gr3WL
  rw [Finset.sum_filter, sum_leaves_decision, Act2.sum_univ, sum_leaves_chance, Fin.sum_univ_two,
    Tree.sum_leaves_leaf, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
  simp [pureProc, coin_w_zero]

/-- **The fork-closure instance on a law-fair, not strongly fair, two-member fiber with a
non-trivial world event** (`X = {true}`, `ν_{T_q}(X) = 1/3` under `a`), for every procedure: the
`X`-mass of the `d`-runs factors through one fiber member. This is where `LawFair` is consumed,
which the `Unit`-world `gr3` never exercises.
Source: `equiv.md` EQ-5 / mandate T3(b) ("N+: GR-9 example (3) … with `X` non-trivial");
instantiates `LawFair.fork_closure_perRun`
Kind: N+ -/
theorem gr3W_fork_true (C : Proc Unit (fun _ => Act2) ℚ) :
    mass C gr3W (worldEv gr3W {Bool.true} ∩ occ () gr3W) =
      (∑ q ∈ minimalFiber gr3W (), reach C gr3W q) * nu C gr3WL {Bool.true} :=
  (gr3W_lawFair.fork_closure_perRun C () {Bool.true} gr3W_fiber_two.1).1

/-! ### `Closed.stronglyFair_output` between the trivial ends; FR-4 as stated refuted -/

/-- Claim B's T-branch: a `d`-node with an `e`-node below each answer; worlds `(heads, act_e)`.
Source: `adversary-repair.md` Claim B (the concrete witness)
Kind: D -/
def cbT : Tree SeqW GatePt (fun _ => Act2) ℚ :=
  .decision .d fun _ => .decision .e fun y => .leaf (.a, y) 0

/-- Claim B's H-branch: a hypothetical `d`-node over plain leaves.
Source: `adversary-repair.md` Claim B
Kind: D -/
def cbH : Tree SeqW GatePt (fun _ => Act2) ℚ :=
  .decision .d fun _ => .leaf (.b, .a) 0

/-- Claim B's tree: a fair coin over `cbT` / `cbH`.
Source: `adversary-repair.md` Claim B
Kind: D -/
def cb : Tree SeqW GatePt (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i => Fin.cases cbT (fun _ => cbH) i

/-- `cb` is not strongly fair: `F_d`'s members have an `e`-node vs a leaf under `a`.
Source: `adversary-repair.md` Claim B ("`F_d` is unfair")
Kind: N+ -/
theorem cb_not_stronglyFair : ¬ StronglyFair cb := by
  intro h
  have := h .d ⟨0, none⟩ (by decide) ⟨1, none⟩ (by decide)
  change LabIso cbT cbH at this
  have h2 := (LabIso.decision_inj this) .a
  cases h2

/-- Every `e`-node of `cb` has the same subtree.
Source: none: audit r1 (adversarial) probe E
Kind: L -/
theorem cb_e_subtree (q : cb.DecNode) (hq : pt cb q = .e) :
    subtreeAt cb q = .decision .e fun y => .leaf (.a, y) 0 := by
  obtain ⟨i, q⟩ := q
  fin_cases i
  · change cbT.DecNode at q
    rcases q with _ | ⟨x, _ | ⟨y, e⟩⟩
    · exact absurd hq (by decide)
    · rfl
    · exact e.elim
  · change cbH.DecNode at q
    rcases q with _ | ⟨x, e⟩
    · exact absurd hq (by decide)
    · exact e.elim

/-- `{d}` is closed for `cb`: `e`'s fiber is pairwise `≅` and no `d`-node lies below an `e`-node.
Source: `adversary-repair.md` Claim B ("`e` has no `U`-node below, so `e ∉ U`")
Kind: N+ -/
theorem cb_closed : Closed cb {.d} := by
  have he : ∀ e : GatePt, e ∉ ({.d} : Finset GatePt) → e = .e := by decide
  refine ⟨fun e hne q hq q' hq' => ?_, fun e hne q hq => ?_⟩
  · rw [mem_fiber] at hq hq'
    rw [cb_e_subtree q (hq.trans (he e hne)), cb_e_subtree q' (hq'.trans (he e hne))]
    exact LabIso.refl _
  · rw [mem_fiber] at hq
    rw [cb_e_subtree q (hq.trans (he e hne))]
    decide

/-- **T5 applies to `cb` with `U = {d}`**, a `U` that is neither `∅` nor `queried cb`, on an input
that is not strongly fair: the output, stamps projected away, is strongly fair.
Source: `fair-repair.md` FR-4 as repaired by Claim B; audit r1 (adversarial) probe E
Kind: N+ -/
theorem cb_output_stronglyFair : StronglyFair (mapWorld Prod.fst (relocRoot {.d} cb)) :=
  cb_closed.stronglyFair_output

theorem cb_queried : queried cb = {.d, .e} := by decide

/-- The `a`- and `b`-branch tuples of the relocated root.
Source: none: audit r1 (adversarial) probe E
Kind: D -/
def σa : (d : ↥({.d} : Finset GatePt)) → Act2 := fun _ => .a

/-- The `b`-branch tuple. Source: none: audit r1 (adversarial) probe E. Kind: D -/
def σb : (d : ↥({.d} : Finset GatePt)) → Act2 := fun _ => .b

/-- The two copies of the `e`-node in the output (one per `pol_d`-branch), both in the
`inl e`-fiber, distinct — so `cb_output_stronglyFair` has a two-member fiber to relate.
Source: `adversary-repair.md` Claim B ("two `e`-copies, one per `pol_d`-branch")
Kind: N+ -/
theorem cb_reloc_e_fiber_two :
    (some ⟨σa, ⟨0, none⟩⟩ : (relocRoot {.d} cb).DecNode) ∈ fiber (relocRoot {.d} cb) (.inl .e) ∧
    (some ⟨σb, ⟨0, none⟩⟩ : (relocRoot {.d} cb).DecNode) ∈ fiber (relocRoot {.d} cb) (.inl .e) ∧
    (some ⟨σa, ⟨0, none⟩⟩ : (relocRoot {.d} cb).DecNode) ≠ some ⟨σb, ⟨0, none⟩⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  · decide

/-- The relocated tree type of `cb`.
Source: none: audit r1 (adversarial) probe E
Kind: D -/
abbrev CbRT : Type :=
  Tree (RW SeqW (fun _ => Act2) {GatePt.d}) (GatePt ⊕ Unit) (actsR (fun _ => Act2) {GatePt.d}) ℚ

/-- One `e`-copy with stamp `σ`. Source: none: audit r1 (adversarial) probe E. Kind: D -/
def eCopy (σ : (d : ↥({.d} : Finset GatePt)) → Act2) : CbRT :=
  .decision (Sum.inl GatePt.e) fun y => .leaf ((Act2.a, y), σ) 0

/-- **FR-4 as stated is false**: with the `pol` stamps kept, the two copies of the `e`-node are
not `≅` — their leaf worlds differ in the stamp — so `relocRoot {d} cb` is not strongly fair on
the enriched worlds, although it is after `mapWorld Prod.fst` (`cb_output_stronglyFair`).
Source: `fair-repair.md` FR-4 (refuted claim); `adversary-repair.md` Claim B ("No
`(λ, r)`-preserving isomorphism exists")
Kind: N− -/
theorem cb_reloc_not_stronglyFair : ¬ StronglyFair (relocRoot {.d} cb) := by
  intro h
  obtain ⟨h1, h2, -⟩ := cb_reloc_e_fiber_two
  have := h (Sum.inl GatePt.e) _ h1 _ h2
  change LabIso (eCopy σa) (eCopy σb) at this
  have h3 := (LabIso.leaf_inj ((LabIso.decision_inj this) Act2.a)).1
  have h4 := congrFun (congrArg Prod.snd h3) ⟨.d, Finset.mem_singleton_self _⟩
  simp [σa, σb] at h4

end Cleanroom.Decision.DpFairnessReloc

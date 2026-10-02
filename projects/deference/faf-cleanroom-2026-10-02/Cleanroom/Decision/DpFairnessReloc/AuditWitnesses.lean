import Cleanroom.Decision.DpFairnessReloc.MoreWitnesses
import Cleanroom.Decision.DpFairnessReloc.LawSetsThms
import Cleanroom.Decision.DpFairnessReloc.RelationsChain

/-!
# Audit-round-2 witnesses: EQ-4's value and law clauses; load-bearing hypotheses (repair round 2)

Package `dp-fairness-reloc`, file 17. Constructions adopted from the round-2 audit probes
(`run/wp/dp-fairness-reloc/audit-r2-probes/`: `Eq4ValLaw.lean`, fidelity lens; `EcLoadBearing`,
`FairLoadBearing`, `PrunedLoadBearing`, `ClosureLoadBearing`, adversarial lens), re-documented:

* **EQ-4's `≈_val` clause, and the source's witness for it is wrong** (findings F13). `equiv.md`
  EQ-4 says nesting is not excluded "by `≈_val` … : E5". With `≈_val` = equal `V_T(C)` for every
  `C` (the package's `ValEq`, the source's own Definitions carried), E5's top is worth `(1−q)²`
  and its bottom `1−q` (`value_e5`, `value_e5Bot`), so E5 is **not** `Fair_{≈val}`
  (`e5_not_fairValEq`). The clause itself is true, witnessed by the payoff-degenerate nested tree
  `degen` of Claim F (`degen_fairValEq`); and E5 is value-fair in the mandate's *act-value* grade
  `Q(q, C, a) := V(C[d ↦ a])` (`e5_valueFair`) — the two value grades the package carries diverge
  exactly on E5: act-value fairness admits the non-degenerate nested E5, every-`C` value fairness
  admits only payoff-degenerate nesting (on this pair of witnesses).
* **EQ-4's `≈_law` clause** ("only up to law-spurious nesting"): a law-spurious nested tree is
  law-fair (`spur_lawFair`).
* **Claim B's hypotheses are each load-bearing**: `dup` (a fair coin over two literally equal
  `d`-nodes whose leaves record only the act) satisfies everything but EC and has a two-member
  fiber (`ec_load_bearing`); `coinDD` (a fair coin over two `d`-nodes whose leaves record the coin
  and the act) satisfies everything but strong fairness (`fair_load_bearing`). With
  `hreal_load_bearing` (`MoreWitnesses.lean`) this makes the theorem's mechanism explicit: under
  EC, `≅` fiber members cannot be separated by a chance node (their leaf worlds would coincide
  across disjoint edge events), so a multi-member strongly fair fiber must diverge at a decision
  node, which recording forbids.
* **`Pruned` is load-bearing in EQ-4 for `≃`, `≃_Δ`, `≈_tr`**: `zeroNestRoot`, a `d`-node over a
  `(1, 0)`-coin whose zero branch is a second `d`-node, is `Fair_≃` (hence `Fair_{≃Δ}`,
  `Fair_{≈tr}`) yet not almost fair (`pruned_load_bearing`).
* **The closure clause of `Closed` is load-bearing, and it is FR-3's mechanism in one step**:
  `chain` (`d` then `e` then a leaf recording both acts) has `unfair(chain) = {e}`; `U = {e}`
  satisfies the fiber clause of `Closed` but not the closure clause, and
  `(Rel_{{e}} chain).mapWorld Prod.fst` is not strongly fair — relocating the unfair fiber alone
  un-fairs the fair one (`closure_load_bearing`). This is the mandate's T5 "why `cl` is needed"
  item; full non-termination of the ping-pong is not stated.
-/

namespace Cleanroom.Decision.DpFairnessReloc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Finset

/-! ### EQ-4's `≈_val` clause: E5 is not the witness; `degen` is -/

/-- E5's value under the one-point procedure `q`: `(1 − q)²` (the top redraws at the bottom
node, so `V(top) = (1 − q) · V(bottom)`).
Source: `equiv.md` EQ-4 (E5); findings F13
Kind: L -/
theorem value_e5 (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (procQ q h0 h1) e5 = (1 - q) ^ 2 := by
  unfold value e5
  rw [sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, sum_leaves_decision, Act2.sum_univ,
    Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
  simp [procQ]
  ring

/-- E5's bottom node's value under the one-point procedure `q`: `1 − q`.
Source: `equiv.md` EQ-4 (E5); findings F13
Kind: L -/
theorem value_e5Bot (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (procQ q h0 h1) e5Bot = 1 - q := by
  unfold value e5Bot
  rw [sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
  simp [procQ]

/-- **E5's top and bottom are not `≈_val`**: `¼ ≠ ½` at `q = ½`.
Source: `equiv.md` EQ-4 ("not by `≈_val` … : E5" — refuted for this pair; findings F13)
Kind: N− (the source's witness fails the clause it is cited for) -/
theorem e5_not_valEq : ¬ ValEq e5 e5Bot := by
  intro h
  have := h (procQ (1/2) (by norm_num) (by norm_num))
  rw [value_e5, value_e5Bot] at this
  norm_num at this

/-- **E5 is not `Fair_{≈val}`** in the source's own sense (`≈_val` = equal `V_T(C)` for every
`C`, `equiv.md` Definitions carried): its one fiber `{top, bottom}` fails `ValEq`.
Source: `equiv.md` EQ-4 ("Nesting is excluded by … **not** by `≈_val` … : E5"); findings F13
Kind: N− (the source's witness fails)
Fidelity: exact (grade `≈_val` as the source defines it) -/
theorem e5_not_fairValEq : ¬ FairWrt (fun _ => ValEq) e5 := by
  intro h
  exact e5_not_valEq (h () none (by decide) (some ⟨.b, none⟩) (by decide))

/-- E5's top and bottom have equal act values: with `d ↦ a` both are worth `0`, with `d ↦ b`
both `1`.
Source: mandate §3 (act-value grade `Q(q, C, a)`); findings F13
Kind: L -/
theorem e5_value_dev (C : Proc Unit (fun _ => Act2) ℚ) (a : Act2) :
    value (C.deviatePure () a) e5 = value (C.deviatePure () a) e5Bot := by
  have hL : value (C.deviatePure () a) e5 =
      (C.deviatePure () a ()).w .a * 0 +
        (C.deviatePure () a ()).w .b * ((C.deviatePure () a ()).w .a * 0 +
          (C.deviatePure () a ()).w .b * 1) := by
    unfold value e5
    rw [sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, sum_leaves_decision,
      Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
    simp
  have hR : value (C.deviatePure () a) e5Bot =
      (C.deviatePure () a ()).w .a * 0 + (C.deviatePure () a ()).w .b * 1 := by
    unfold value e5Bot
    rw [sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
    simp
  rw [hL, hR]
  cases a <;> simp [Proc.deviatePure, Proc.deviate, FinDistr.pure]

/-- **E5 is `ValueFair`** (the mandate's act-value grade `Q(q, C, a) = V(C[d ↦ a])`) although not
`Fair_{≈val}`: the act-value grade does not exclude the non-degenerate nested E5, the every-`C`
value grade does (`e5_not_fairValEq`). This is the sharper form of EQ-4's `≈_val` clause.
Source: `equiv.md` EQ-4; mandate T8(c) ("`≈_val` and `∼_pure` do **not** [exclude nesting]:
E5"), read in the mandate's own act-value grade; findings F13
Kind: N+
Fidelity: variant: the grade is `ValueFair` (act values), not the source's `≈_val` -/
theorem e5_valueFair : ValueFair e5 := by
  intro d q _ q' _ C a
  rcases e5_subtree q with h | h <;> rcases e5_subtree q' with h' | h' <;> rw [h, h']
  · exact e5_value_dev C a
  · exact (e5_value_dev C a).symm

/-- The bottom node of Claim F's payoff-degenerate tree `degen`: a `d`-node over two `0`-leaves.
Source: `adversary-repair.md` Claim F
Kind: D -/
def degenBot : Tree Unit Unit (fun _ => Act2) ℚ := .decision () fun _ => .leaf () 0

/-- `degenBot` is worth `0` under every procedure.
Source: `adversary-repair.md` Claim F
Kind: L -/
theorem degenBot_value (C : Proc Unit (fun _ => Act2) ℚ) : value C degenBot = 0 := by
  unfold value degenBot
  rw [sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
  simp

/-- Every subtree of `degen` at a decision node is `degen` itself or `degenBot`.
Source: none: infrastructure
Kind: L -/
theorem degen_subtree (q : degen.DecNode) :
    subtreeAt degen q = degen ∨ subtreeAt degen q = degenBot := by
  rcases q with _ | ⟨a, q⟩
  · exact Or.inl rfl
  · cases a
    · change Empty at q
      exact q.elim
    · rcases q with _ | ⟨b, e⟩
      · exact Or.inr rfl
      · cases b <;> (change Empty at e; exact e.elim)

/-- **EQ-4's `≈_val` clause, with a witness that works**: the payoff-degenerate nested tree
`degen` is nested and `Fair_{≈val}` (every value is `0`) — `≈_val` does not exclude nesting.
Source: `equiv.md` EQ-4 ("**not** by `≈_val`"), witnessed by `adversary-repair.md` Claim F's
tree instead of the source's E5 (findings F13)
Kind: N+ (the clause's content: a nested tree passes the every-`C` value grade; the witness is
payoff-degenerate — see `e5_valueFair` for the non-degenerate act-value form)
Fidelity: exact (grade `≈_val` = `ValEq`) -/
theorem degen_fairValEq : FairWrt (fun _ => ValEq) degen ∧ Nested degen () := by
  refine ⟨fun d q _ q' _ C => ?_, degen_nested⟩
  rcases degen_subtree q with h | h <;> rcases degen_subtree q' with h' | h' <;>
    rw [h, h'] <;> simp only [degen_value, degenBot_value]

/-! ### EQ-4's `≈_law` clause: law-spurious nesting is law-fair -/

/-- A `d`-node over two `(( ), 1)`-leaves: the bottom of the law-spurious nested tree.
Source: `equiv.md` EQ-4 ("law-spurious nesting")
Kind: D -/
def spurBot : Tree Unit Unit (fun _ => Act2) ℚ := .decision () fun _ => .leaf () 1

/-- The law-spurious nested tree: a `d`-node over two copies of `spurBot` (every leaf reads
`(( ), 1)`, so the `d`-count is invisible to the `(λ, r)`-law).
Source: `equiv.md` EQ-4 ("by `≈_law` only up to law-spurious nesting")
Kind: D -/
def spur : Tree Unit Unit (fun _ => Act2) ℚ := .decision () fun _ => spurBot

/-- `spurBot`'s law is `δ_{(( ), 1)}` under every procedure.
Source: `equiv.md` EQ-4
Kind: L -/
theorem contLaw_spurBot (C : Proc Unit (fun _ => Act2) ℚ) :
    contLaw C spurBot = Finsupp.single ((), (1 : ℚ)) 1 := by
  unfold spurBot
  rw [contLaw_decision]
  simp only [contLaw_leaf]
  rw [← Finset.sum_smul, (C ()).sum_one, one_smul]

/-- `spur`'s law is `δ_{(( ), 1)}` under every procedure.
Source: `equiv.md` EQ-4
Kind: L -/
theorem contLaw_spur (C : Proc Unit (fun _ => Act2) ℚ) :
    contLaw C spur = Finsupp.single ((), (1 : ℚ)) 1 := by
  unfold spur
  rw [contLaw_decision]
  simp only [contLaw_spurBot]
  rw [← Finset.sum_smul, (C ()).sum_one, one_smul]

/-- `spur` is nested at its one point.
Source: `equiv.md` EQ-4
Kind: L -/
theorem spur_nested : Nested spur () := by
  refine ⟨by decide, ⟨.a, ⟨.a, ()⟩⟩, ?_, ?_⟩
  · unfold Positive spur spurBot; simp
  · unfold spur spurBot; simp

/-- Every subtree of `spur` at a decision node is `spur` itself or `spurBot`.
Source: none: infrastructure
Kind: L -/
theorem spur_subtree (q : spur.DecNode) :
    subtreeAt spur q = spur ∨ subtreeAt spur q = spurBot := by
  rcases q with _ | ⟨a, _ | ⟨b, e⟩⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact e.elim

/-- **EQ-4's `≈_law` clause, negative half**: a law-spurious nested tree is law-fair — `≈_law`
excludes nesting only up to law-spurious nesting, as the source says.
Source: `equiv.md` EQ-4 ("by `≈_law` only up to law-spurious nesting")
Kind: N+
Fidelity: exact (grade `≈_law` = `LawFair`; the positive half, that `≈_law` excludes non-spurious
nesting, is not stated — the source gives no precise definition of "law-spurious") -/
theorem spur_lawFair : LawFair spur ∧ Nested spur () := by
  refine ⟨fun d q _ q' _ C => ?_, spur_nested⟩
  rcases spur_subtree q with h | h <;> rcases spur_subtree q' with h' | h' <;>
    rw [h, h'] <;> simp only [contLaw_spur, contLaw_spurBot]

/-- **EQ-4's value and law clauses on one statement**: E5 fails `Fair_{≈val}` (the source's
witness is wrong), `degen` is nested and `Fair_{≈val}` (the clause holds), E5 is nested and
`ValueFair` (the act-value clause), `spur` is nested and law-fair (the `≈_law` clause).
Source: `equiv.md` EQ-4 (the `≈_val` and `≈_law` clauses); mandate T8(c); findings F13
Kind: N+ -/
theorem eq4_val_law_clauses :
    ¬ FairWrt (fun _ => ValEq) e5 ∧ (FairWrt (fun _ => ValEq) degen ∧ Nested degen ()) ∧
      (ValueFair e5 ∧ Nested e5 ()) ∧ (LawFair spur ∧ Nested spur ()) :=
  ⟨e5_not_fairValEq, degen_fairValEq, ⟨e5_valueFair, e5_nested⟩, spur_lawFair⟩

/-! ### Claim B: `EventedChance` is load-bearing (`dup`) -/

/-- A `d`-node whose leaf records the act.
Source: none: audit r2 (adversarial) probe A
Kind: D -/
def dNode : Tree Act2 GatePt (fun _ => Act2) ℚ := .decision .d fun x => .leaf x 0

/-- A fair coin over two literally equal copies of `dNode`: the worlds cannot see the coin.
Source: none: audit r2 (adversarial) probe A
Kind: D -/
def dup : Tree Act2 GatePt (fun _ => Act2) ℚ := .chance 2 FinDistr.fair fun _ => dNode

/-- `O_d = O_e = ⊤` for `dup`.
Source: none: audit r2 (adversarial) probe A
Kind: D -/
def dupObs : GatePt → Finset Act2 := fun _ => Finset.univ

/-- Act events for `dup`: the recorded act.
Source: none: audit r2 (adversarial) probe A
Kind: D -/
def dupActEv : GatePt → Act2 → Finset Act2 := fun _ v => Finset.univ.filter fun w => w = v

/-- Every decision subtree of `dup` is `dNode`.
Source: none: infrastructure
Kind: L -/
theorem dup_subtree (q : dup.DecNode) : subtreeAt dup q = dNode := by
  obtain ⟨i, q⟩ := q
  change dNode.DecNode at q
  rcases q with _ | ⟨x, e⟩
  · rfl
  · change Empty at e
    exact e.elim

/-- `dup` is strongly fair (its two `d`-copies are equal).
Source: none: audit r2 (adversarial) probe A
Kind: L -/
theorem dup_stronglyFair : StronglyFair dup := by
  intro d q _ q' _
  rw [dup_subtree q, dup_subtree q']
  exact LabIso.refl _

/-- `dup` is pruned.
Source: none: audit r2 (adversarial) probe A
Kind: L -/
theorem dup_pruned : Pruned dup := by
  intro ℓ
  obtain ⟨i, ℓ⟩ := ℓ
  change dNode.Leaves at ℓ
  obtain ⟨x, _⟩ := ℓ
  fin_cases i
  · show (0 : ℚ) < FinDistr.fair.w 0 * 1
    rw [show FinDistr.fair.w 0 = 1/2 from rfl]; norm_num
  · show (0 : ℚ) < FinDistr.fair.w 1 * 1
    rw [show FinDistr.fair.w 1 = 1 - 1/2 from rfl]; norm_num

/-- `dup` records at `d` for every procedure.
Source: none: audit r2 (adversarial) probe A
Kind: L -/
theorem dup_records_d : RecordsForAll dupObs dupActEv dup .d := by
  intro C ℓ _ hobs
  have key : ∀ ℓ : dup.Leaves, world dup ℓ ∈ dupObs .d →
      count .d dup ℓ = 1 ∧
      ∀ q : dup.DecNode, pt dup q = .d → ∀ a, edgeOf dup q ℓ = some a →
        (∀ ℓ' ∈ leavesBelow dup q, world dup ℓ' ∈ dupObs (pt dup q)) ∧
        world dup ℓ ∈ dupActEv (pt dup q) a ∧
        ∀ a', world dup ℓ ∈ dupActEv (pt dup q) a' → a' = a := by decide
  exact key ℓ hobs

/-- `queried dup = {d}`.
Source: none: infrastructure
Kind: L -/
theorem dup_queried : queried dup = {.d} := by decide

/-- EC fails on `dup`: the world `a` lies below both edges of the coin.
Source: none: audit r2 (adversarial) probe A
Kind: L -/
theorem dup_not_eventedChance : ¬ EventedChance dup := by
  intro h
  have := h.1 0 1 (by decide) (⟨.a, ()⟩ : dNode.Leaves) (⟨.a, ()⟩ : dNode.Leaves)
  exact this rfl

/-- `dup`'s `d`-fiber has two distinct members.
Source: none: infrastructure
Kind: L -/
theorem dup_fiber_two :
    (⟨0, none⟩ : dup.DecNode) ∈ fiber dup .d ∧ (⟨1, none⟩ : dup.DecNode) ∈ fiber dup .d ∧
      (⟨0, none⟩ : dup.DecNode) ≠ ⟨1, none⟩ := by
  decide

/-- **EC is load-bearing in `singleton_fibers`** (Claim B): `dup` satisfies the other four
hypotheses (strongly fair, pruned, records at every queried point for every procedure, realizes
the observation) and has a two-member `d`-fiber — it is exactly EC that rules out "perfect copies
under instance-blind chance".
Source: `adversary-repair.md` Claim B (the role of the evented-chance hypothesis); audit r2
(adversarial) probe A
Kind: N− (the hypothesis cannot be dropped) -/
theorem ec_load_bearing :
    StronglyFair dup ∧ Pruned dup ∧
      (∀ e ∈ queried dup, RecordsForAll dupObs dupActEv dup e) ∧
      (∀ e ∈ queried dup, ∃ ℓ, Positive dup ℓ ∧ world dup ℓ ∈ dupObs e) ∧
      ¬ EventedChance dup ∧
      ¬ (∀ d, ∀ q ∈ fiber dup d, ∀ q' ∈ fiber dup d, q = q') := by
  refine ⟨dup_stronglyFair, dup_pruned, ?_, ?_, dup_not_eventedChance, ?_⟩
  · intro e he
    rw [dup_queried, Finset.mem_singleton] at he
    subst he
    exact dup_records_d
  · intro e _
    exact ⟨⟨0, ⟨.a, ()⟩⟩, dup_pruned _, by simp [dupObs]⟩
  · intro h
    obtain ⟨h1, h2, h3⟩ := dup_fiber_two
    exact h3 (h .d _ h1 _ h2)

/-! ### Claim B: strong fairness is load-bearing (`coinDD`) -/

/-- Heads: a `d`-node whose leaves record `(heads, act_d)`.
Source: none: audit r2 (adversarial) probe B
Kind: D -/
def dH : Tree SeqW GatePt (fun _ => Act2) ℚ := .decision .d fun x => .leaf (.a, x) 0

/-- Tails: a `d`-node whose leaves record `(tails, act_d)`.
Source: none: audit r2 (adversarial) probe B
Kind: D -/
def dT : Tree SeqW GatePt (fun _ => Act2) ℚ := .decision .d fun x => .leaf (.b, x) 0

/-- A fair coin over `dH` / `dT`.
Source: none: audit r2 (adversarial) probe B
Kind: D -/
def coinDD : Tree SeqW GatePt (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i => Fin.cases dH (fun _ => dT) i

/-- `O_d = O_e = ⊤` on `SeqW` worlds.
Source: none: audit r2 (adversarial) probe B
Kind: D -/
def topObs : GatePt → Finset SeqW := fun _ => Finset.univ

/-- `coinDD` is evented: the two edges carry disjoint world sets.
Source: none: audit r2 (adversarial) probe B
Kind: L -/
theorem coinDD_eventedChance : EventedChance coinDD := by
  refine ⟨fun i j hij ℓ ℓ' => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · change dH.Leaves at ℓ; change dT.Leaves at ℓ'
      obtain ⟨x, _⟩ := ℓ
      obtain ⟨y, _⟩ := ℓ'
      show (Act2.a, x) ≠ (Act2.b, y)
      simp
    · change dT.Leaves at ℓ; change dH.Leaves at ℓ'
      obtain ⟨x, _⟩ := ℓ
      obtain ⟨y, _⟩ := ℓ'
      show (Act2.b, x) ≠ (Act2.a, y)
      simp
    · exact absurd rfl hij
  · fin_cases i
    · exact fun _ => trivial
    · exact fun _ => trivial

/-- `coinDD` is pruned.
Source: none: audit r2 (adversarial) probe B
Kind: L -/
theorem coinDD_pruned : Pruned coinDD := by
  intro ℓ
  obtain ⟨i, ℓ⟩ := ℓ
  fin_cases i
  · change dH.Leaves at ℓ
    obtain ⟨x, _⟩ := ℓ
    show (0 : ℚ) < FinDistr.fair.w 0 * 1
    rw [show FinDistr.fair.w 0 = 1/2 from rfl]; norm_num
  · change dT.Leaves at ℓ
    obtain ⟨x, _⟩ := ℓ
    show (0 : ℚ) < FinDistr.fair.w 1 * 1
    rw [show FinDistr.fair.w 1 = 1 - 1/2 from rfl]; norm_num

/-- `coinDD` records at `d` for every procedure (act events on the act coordinate).
Source: none: audit r2 (adversarial) probe B
Kind: L -/
theorem coinDD_records_d : RecordsForAll topObs seqActEv coinDD .d := by
  intro C ℓ _ hobs
  have key : ∀ ℓ : coinDD.Leaves, world coinDD ℓ ∈ topObs .d →
      count .d coinDD ℓ = 1 ∧
      ∀ q : coinDD.DecNode, pt coinDD q = .d → ∀ a, edgeOf coinDD q ℓ = some a →
        (∀ ℓ' ∈ leavesBelow coinDD q, world coinDD ℓ' ∈ topObs (pt coinDD q)) ∧
        world coinDD ℓ ∈ seqActEv (pt coinDD q) a ∧
        ∀ a', world coinDD ℓ ∈ seqActEv (pt coinDD q) a' → a' = a := by decide
  exact key ℓ hobs

/-- `queried coinDD = {d}`.
Source: none: infrastructure
Kind: L -/
theorem coinDD_queried : queried coinDD = {.d} := by decide

/-- `coinDD`'s `d`-fiber has two distinct members.
Source: none: infrastructure
Kind: L -/
theorem coinDD_fiber_two :
    (⟨0, none⟩ : coinDD.DecNode) ∈ fiber coinDD .d ∧
      (⟨1, none⟩ : coinDD.DecNode) ∈ fiber coinDD .d ∧
      (⟨0, none⟩ : coinDD.DecNode) ≠ ⟨1, none⟩ := by
  decide

/-- `coinDD` is not strongly fair: the members' leaf worlds differ in the coin coordinate.
Source: none: audit r2 (adversarial) probe B
Kind: L -/
theorem coinDD_not_stronglyFair : ¬ StronglyFair coinDD := by
  intro h
  have := h .d ⟨0, none⟩ (by decide) ⟨1, none⟩ (by decide)
  change LabIso dH dT at this
  have h2 := (LabIso.leaf_inj ((LabIso.decision_inj this) .a)).1
  exact absurd h2 (by decide)

/-- **Strong fairness is load-bearing in `singleton_fibers`** (Claim B): `coinDD` satisfies the
other four hypotheses (evented, pruned, records at every queried point for every procedure,
realizes the observation) and has a two-member `d`-fiber. Read with `ec_load_bearing`: under
EC a multi-member fiber can only be strongly fair by diverging at a decision node, which
recording then forbids — both halves are needed.
Source: `adversary-repair.md` Claim B (the role of the fairness hypothesis); audit r2
(adversarial) probe B
Kind: N− (the hypothesis cannot be dropped) -/
theorem fair_load_bearing :
    EventedChance coinDD ∧ Pruned coinDD ∧
      (∀ e ∈ queried coinDD, RecordsForAll topObs seqActEv coinDD e) ∧
      (∀ e ∈ queried coinDD, ∃ ℓ, Positive coinDD ℓ ∧ world coinDD ℓ ∈ topObs e) ∧
      ¬ StronglyFair coinDD ∧
      ¬ (∀ d, ∀ q ∈ fiber coinDD d, ∀ q' ∈ fiber coinDD d, q = q') := by
  refine ⟨coinDD_eventedChance, coinDD_pruned, ?_, ?_, coinDD_not_stronglyFair, ?_⟩
  · intro e he
    rw [coinDD_queried, Finset.mem_singleton] at he
    subst he
    exact coinDD_records_d
  · intro e _
    exact ⟨⟨0, ⟨.a, ()⟩⟩, coinDD_pruned _, by simp [topObs]⟩
  · intro h
    obtain ⟨h1, h2, h3⟩ := coinDD_fiber_two
    exact h3 (h .d _ h1 _ h2)

/-! ### EQ-4: `Pruned` is load-bearing for `≃`, `≃_Δ`, `≈_tr` (`zeroNestRoot`) -/

/-- The `(1, 0)` coin.
Source: none: audit r2 (adversarial) probe C
Kind: D -/
def oneZero : FinDistr ℚ (Fin 2) := FinDistr.coin 1 (by norm_num) (by norm_num)

/-- The inner `d`-node: a `(1, 0)`-coin over two leaves.
Source: none: audit r2 (adversarial) probe C
Kind: D -/
def zeroNestInner : Tree Unit Unit (fun _ => Unit) ℚ :=
  .decision () fun _ => .chance 2 oneZero fun _ => .leaf () 0

/-- The root `d`-node: a `(1, 0)`-coin whose zero branch is `zeroNestInner` — a zero-weight nested
copy.
Source: none: audit r2 (adversarial) probe C
Kind: D -/
def zeroNestRoot : Tree Unit Unit (fun _ => Unit) ℚ :=
  .decision () fun _ =>
    .chance 2 oneZero fun i => Fin.cases (.leaf () 0) (fun _ => zeroNestInner) i

/-- Every decision subtree of `zeroNestRoot` is the root or the inner node.
Source: none: infrastructure
Kind: L -/
theorem zeroNest_subtree (q : zeroNestRoot.DecNode) :
    subtreeAt zeroNestRoot q = zeroNestRoot ∨ subtreeAt zeroNestRoot q = zeroNestInner := by
  rcases q with _ | ⟨_, ⟨i, q⟩⟩
  · exact Or.inl rfl
  · fin_cases i
    · change Empty at q
      exact q.elim
    · change zeroNestInner.DecNode at q
      rcases q with _ | ⟨_, ⟨j, e⟩⟩
      · exact Or.inr rfl
      · change Empty at e
        exact e.elim

/-- The two `(1, 0)`-coins are bisimilar: all coupling mass on the pair of positive leaves.
Source: none: audit r2 (adversarial) probe C
Kind: L -/
theorem bisim_oneZero_coins :
    Bisim (.chance 2 oneZero fun i => Fin.cases (.leaf () 0) (fun _ => zeroNestInner) i :
        Tree Unit Unit (fun _ => Unit) ℚ)
      (.chance 2 oneZero fun _ => .leaf () 0) := by
  refine Bisim.chance oneZero oneZero _ _ (fun i j => if i = 0 ∧ j = 0 then 1 else 0) ?_ ?_ ?_ ?_
  · intro i j; split_ifs <;> norm_num
  · intro i
    fin_cases i
    · rw [Fin.sum_univ_two]
      show (if ((0 : Fin 2) = 0 ∧ (0 : Fin 2) = 0) then (1 : ℚ) else 0) +
        (if ((0 : Fin 2) = 0 ∧ (1 : Fin 2) = 0) then (1 : ℚ) else 0) = oneZero.w 0
      rw [show oneZero.w 0 = 1 from rfl]
      simp
    · rw [Fin.sum_univ_two]
      show (if ((1 : Fin 2) = 0 ∧ (0 : Fin 2) = 0) then (1 : ℚ) else 0) +
        (if ((1 : Fin 2) = 0 ∧ (1 : Fin 2) = 0) then (1 : ℚ) else 0) = oneZero.w 1
      rw [show oneZero.w 1 = 1 - 1 from rfl]
      simp
  · intro j
    fin_cases j
    · rw [Fin.sum_univ_two]
      show (if ((0 : Fin 2) = 0 ∧ (0 : Fin 2) = 0) then (1 : ℚ) else 0) +
        (if ((1 : Fin 2) = 0 ∧ (0 : Fin 2) = 0) then (1 : ℚ) else 0) = oneZero.w 0
      rw [show oneZero.w 0 = 1 from rfl]
      simp
    · rw [Fin.sum_univ_two]
      show (if ((0 : Fin 2) = 0 ∧ (1 : Fin 2) = 0) then (1 : ℚ) else 0) +
        (if ((1 : Fin 2) = 0 ∧ (1 : Fin 2) = 0) then (1 : ℚ) else 0) = oneZero.w 1
      rw [show oneZero.w 1 = 1 - 1 from rfl]
      simp
  · intro i j hij
    have hc : i = 0 ∧ j = 0 := by
      by_contra hc
      exact hij (if_neg hc)
    obtain ⟨rfl, rfl⟩ := hc
    exact Bisim.leaf () 0

/-- `zeroNestRoot ≃ zeroNestInner`.
Source: none: audit r2 (adversarial) probe C
Kind: L -/
theorem bisim_zeroNest : Bisim zeroNestRoot zeroNestInner :=
  Bisim.decision () _ _ fun _ => bisim_oneZero_coins

/-- `zeroNestRoot` is `Fair_≃` (its one fiber is `{root, inner}`).
Source: none: audit r2 (adversarial) probe C
Kind: L -/
theorem zeroNest_fairBisim : FairBisim zeroNestRoot := by
  intro d q _ q' _
  rcases zeroNest_subtree q with h | h <;> rcases zeroNest_subtree q' with h' | h' <;> rw [h, h']
  · exact Bisim.refl _
  · exact bisim_zeroNest
  · exact bisim_zeroNest.symm
  · exact Bisim.refl _

/-- The zero-weight leaf below the inner node, as a leaf of `zeroNestRoot`.
Source: none: infrastructure
Kind: D -/
def zeroNestLeaf : zeroNestRoot.Leaves := ⟨(), ⟨1, ⟨(), ⟨0, ()⟩⟩⟩⟩

/-- `zeroNestRoot` is not pruned.
Source: none: audit r2 (adversarial) probe C
Kind: L -/
theorem zeroNest_not_pruned : ¬ Pruned zeroNestRoot := by
  intro h
  have := h zeroNestLeaf
  change (0 : ℚ) < oneZero.w 1 * (oneZero.w 0 * 1) at this
  rw [show oneZero.w 1 = 1 - 1 from rfl] at this
  norm_num at this

/-- `zeroNestRoot` is not almost fair: the zero-weight leaf meets `d` twice.
Source: none: audit r2 (adversarial) probe C
Kind: L -/
theorem zeroNest_not_almostFair : ¬ AlmostFair zeroNestRoot := by
  intro h
  have := h () zeroNestLeaf
  change 1 + (1 + 0) ≤ 1 at this
  omega

/-- **`Pruned` is load-bearing in EQ-4** for `≃`, `≃_Δ` and `≈_tr`: an unpruned tree that is
fair under all three (zero-weight nesting is invisible to every relation of the chain up to
`≈_tr`) yet not almost fair — so `FairTr.almostFair`, `FairBisimΔ.almostFair`,
`FairBisim.almostFair` all need their `Pruned` hypothesis.
Source: `equiv.md` EQ-4 ("after pruning"); audit r2 (adversarial) probe C
Kind: N− (the hypothesis cannot be dropped) -/
theorem pruned_load_bearing :
    FairBisim zeroNestRoot ∧ FairBisimΔ zeroNestRoot ∧ FairTr zeroNestRoot ∧
      ¬ Pruned zeroNestRoot ∧ ¬ AlmostFair zeroNestRoot :=
  ⟨zeroNest_fairBisim, zeroNest_fairBisim.fairBisimΔ, zeroNest_fairBisim.fairBisimΔ.fairTr,
    zeroNest_not_pruned, zeroNest_not_almostFair⟩

/-! ### T5: the closure clause of `Closed` is load-bearing — FR-3's mechanism in one step -/

/-- `d` then `e` then a leaf recording `(act_d, act_e)`.
Source: `fair-repair.md` FR-3 (the ping-pong's first step); audit r2 (adversarial) probe D
Kind: D -/
def chain : Tree SeqW GatePt (fun _ => Act2) ℚ :=
  .decision .d fun x => .decision .e fun y => .leaf (x, y) 0

/-- The `d`-fiber of `chain` is a singleton.
Source: none: infrastructure
Kind: L -/
theorem chain_d_fiber_singleton : ∀ q ∈ fiber chain .d, ∀ q' ∈ fiber chain .d, q = q' := by
  decide

/-- The `e`-node of `chain` below `d`'s answer `x`.
Source: none: infrastructure
Kind: D -/
def chainE (x : Act2) : Tree SeqW GatePt (fun _ => Act2) ℚ := .decision .e fun y => .leaf (x, y) 0

/-- `chain` is not strongly fair: its `e`-fiber's two members read `(a, y)` vs `(b, y)`.
Source: audit r2 (adversarial) probe D
Kind: L -/
theorem chain_not_stronglyFair : ¬ StronglyFair chain := by
  intro h
  have := h .e (some ⟨.a, none⟩) (by decide) (some ⟨.b, none⟩) (by decide)
  change LabIso (chainE .a) (chainE .b) at this
  have h2 := (LabIso.leaf_inj ((LabIso.decision_inj this) Act2.a)).1
  exact absurd h2 (by decide)

/-- The fiber clause of `Closed chain {e}` holds (`d`'s fiber is a singleton): `{e}` contains
every unfair fiber.
Source: audit r2 (adversarial) probe D
Kind: L -/
theorem chain_closed_clause1 :
    ∀ p, p ∉ ({.e} : Finset GatePt) → ∀ q ∈ fiber chain p, ∀ q' ∈ fiber chain p,
      LabIso (subtreeAt chain q) (subtreeAt chain q') := by
  intro p hp q hq q' hq'
  have hall : ∀ p : GatePt, p ∉ ({.e} : Finset GatePt) → p = .d := by decide
  have hd := hall p hp
  subst hd
  rw [chain_d_fiber_singleton q hq q' hq']
  exact LabIso.refl _

/-- The closure clause fails: the `d`-node has the `U`-point `e` below it.
Source: audit r2 (adversarial) probe D
Kind: L -/
theorem chain_closed_clause2_fails :
    ¬ (∀ p, p ∉ ({.e} : Finset GatePt) → ∀ q ∈ fiber chain p,
      Disjoint (queried (subtreeAt chain q)) {.e}) := by
  intro h
  have := h .d (by decide) none (by decide)
  exact absurd this (by decide)

/-- `{e}` is not closed for `chain`.
Source: audit r2 (adversarial) probe D
Kind: L -/
theorem chain_not_closed : ¬ Closed chain {.e} := fun h => chain_closed_clause2_fails h.2

/-- The constant root tuple `pol_e = v`.
Source: none: infrastructure
Kind: D -/
def σe (v : Act2) : (d : ↥({.e} : Finset GatePt)) → Act2 := fun _ => v

/-- The `d`-copy in the branch `pol_e = v`, stamps projected away.
Source: none: infrastructure
Kind: D -/
def chainDCopy (v : Act2) :
    Tree SeqW (GatePt ⊕ Unit) (actsR (fun _ => Act2) {GatePt.e}) ℚ :=
  .decision (Sum.inl GatePt.d) fun x => .leaf (x, v) 0

/-- **The output of relocating `{e}` alone is not strongly fair**, stamps projected away: the two
`d`-copies read `(x, a)` and `(x, b)` at their leaves.
Source: `fair-repair.md` FR-3 (relocating the unfair fiber un-fairs the fair one); audit r2
(adversarial) probe D
Kind: L -/
theorem chain_output_not_stronglyFair :
    ¬ StronglyFair (mapWorld Prod.fst (relocRoot {.e} chain)) := by
  intro h
  have := h (Sum.inl GatePt.d) (some ⟨σe .a, none⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩) (some ⟨σe .b, none⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
  change LabIso (chainDCopy .a) (chainDCopy .b) at this
  have h3 := (LabIso.leaf_inj ((LabIso.decision_inj this) Act2.a)).1
  exact absurd h3 (by decide)

/-- **The closure clause of `Closed` is load-bearing, and it is FR-3's mechanism in one step**:
`chain`'s only unfair fiber is `e`'s; `U = {e}` (exactly the unfair set) satisfies the fiber
clause of `Closed` but not the closure clause; and `(Rel_{{e}} chain).mapWorld Prod.fst` is not
strongly fair — relocating the unfair fiber alone un-fairs the fair one. So
`Closed.stronglyFair_output` cannot be weakened to `U ⊇ unfair(B)`; this is the mandate's "why
`cl` is needed" (full non-termination of the ping-pong is not stated).
Source: `fair-repair.md` FR-3 ("ping-pong"), Exit E2 (the entanglement closure); mandate T5;
audit r2 (adversarial) probe D
Kind: N+ (the hypothesis exercised on the smallest tree that needs it) -/
theorem closure_load_bearing :
    ¬ StronglyFair chain ∧
      (∀ p, p ∉ ({.e} : Finset GatePt) → ∀ q ∈ fiber chain p, ∀ q' ∈ fiber chain p,
        LabIso (subtreeAt chain q) (subtreeAt chain q')) ∧
      ¬ Closed chain {.e} ∧
      ¬ StronglyFair (mapWorld Prod.fst (relocRoot {.e} chain)) :=
  ⟨chain_not_stronglyFair, chain_closed_clause1, chain_not_closed, chain_output_not_stronglyFair⟩

end Cleanroom.Decision.DpFairnessReloc

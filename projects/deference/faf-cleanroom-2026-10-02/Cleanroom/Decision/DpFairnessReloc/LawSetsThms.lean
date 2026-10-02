import Cleanroom.Decision.DpFairnessReloc.LawSets
import Cleanroom.Decision.DpFairnessReloc.Relations

/-!
# EQ-10 at the function level; E5 as the nesting witness (repair round 1)

Package `dp-fairness-reloc`, file 14. Over `LawSets.lean`:

* **EQ-10, `∼^f_pure ⟹ ∼^f_beh` on almost-fair trees** (`AlmostFair.lawOfW_eq_of_pure_eq`): if
  two almost-fair trees have the same pure-law map (every deterministic profile gives the same
  `(λ, r)`-law on the shared world type), they have the same law under every procedure. Proof:
  Definition 6 on an almost-fair tree is Definition 6′ (`lawOfW_eq_lawOfW'_of_almostFair`), and
  Definition 6′ is the product mixture of the pure laws over any set of points containing the
  queried ones (`lawOfW'_eq_pureOn_mixture`, `dp-core-tree`'s SE-1(a)); the two mixtures are
  taken over the union of the queried sets and agree term by term. The correspondence `φ` of the
  source is the identity on a shared point type (both trees over `ι'`, `acts'`).
* **E5 refutes EQ-10 with nesting and shows the pure grade does not exclude nesting** (the
  pure-grade clause of EQ-4's negative half): E5's top and bottom `d`-subtrees have identical
  pure laws profile by profile (`e5_pure_eq`) — so E5 is `Fair_{∼pure}` (`e5_pureFair`) — while
  E5 is nested (`e5_nested`) and the two subtrees are not `≈_law` (`e5_not_lawEq`: mass `¾` vs
  `½` on `(o1, 0)` at `q = ½`). EQ-4's `≈_val` and `≈_law` clauses are in `AuditWitnesses.lean`
  (repair round 2), where E5 is shown **not** to be the `≈_val` witness the source cites.
-/

namespace Cleanroom.Decision.DpFairnessReloc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Finset

variable {Ω : Type} {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### EQ-10 at the function level -/

section eq10

variable {Ω' ι' : Type} {acts' : ι' → Type} [∀ d, Fintype (acts' d)] [DecidableEq ι']
  [∀ d, DecidableEq (acts' d)]

/-- Definition 6′'s leaf law as the product mixture of the pure laws over any `S ⊇ queried B`.
Source: `seeds.md` SE-1(a) (`dp-core-tree`'s `leafLawSeed_eq_mixture` at the empty environment)
Kind: L -/
theorem leafLaw'_eq_pureOn_mixture (C : Proc ι' acts' K) (B : Tree Ω' ι' acts' K) (S : Finset ι')
    (hS : queried B ⊆ S) (ℓ : B.Leaves) :
    leafLaw' C B ℓ =
      ∑ π : (d : ↥S) → acts' d, (∏ d : ↥S, (C d).w (π d)) * leafLaw (Proc.pureOn C S π) B ℓ := by
  unfold leafLaw'
  rw [leafLawSeed_eq_mixture C S B hS _ ℓ]
  simp only [seedW_none]

/-- Definition 6′'s law as the product mixture of the pure laws over any `S ⊇ queried B`.
Source: `seeds.md` SE-1(a); `equiv.md` EQ-10 ("a multiaffine `f` equals
`∑_π ∏_d C(d)(π(d)) f(π)`")
Kind: L -/
theorem lawOfW'_eq_pureOn_mixture (f : Ω' → Ω) (C : Proc ι' acts' K) (B : Tree Ω' ι' acts' K)
    (S : Finset ι') (hS : queried B ⊆ S) :
    lawOfW' f C B =
      ∑ π : (d : ↥S) → acts' d, (∏ d : ↥S, (C d).w (π d)) • lawOfW f (Proc.pureOn C S π) B := by
  unfold lawOfW'
  simp only [leafLaw'_eq_pureOn_mixture C B S hS, Finsupp.single_finsetSum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  unfold lawOfW
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finsupp.smul_single, smul_eq_mul]

/-- **EQ-10, `∼^f_pure ⟹ ∼^f_beh` on almost-fair trees**: two almost-fair trees over a shared
point type whose pure-law maps agree profile by profile have the same `(λ, r)`-law under every
procedure. (The converse, `∼^f_beh ⟹ ∼^f_pure`, is the specialisation to `ofFun π`.) Fails with
nesting: `e5_pure_eq` with `e5_not_lawEq`.
Source: `equiv.md` EQ-10 ("when both trees are non-nested, `∼^f_pure ⟹ ∼^f_beh`: under
Definition 6 each `C(d)(·)` appears at most once per leaf, so `C ↦ law_B(C)` is multiaffine, and
a multiaffine `f` equals `∑_π ∏_d C(d)(π(d)) f(π)`; apply to `law_B − law_{B'} ∘ φ`")
Kind: P
Fidelity: variant: the correspondence `φ` is the identity on a shared point type; "non-nested" is
`AlmostFair` (count level)
Hyps: none -/
theorem AlmostFair.lawOfW_eq_of_pure_eq [∀ d, Nonempty (acts' d)] (f f' : Ω' → Ω)
    {B B' : Tree Ω' ι' acts' K} (h : AlmostFair B) (h' : AlmostFair B')
    (hpure : ∀ π₀ : (d : ι') → acts' d,
      lawOfW f (Proc.ofFun π₀) B = lawOfW f' (Proc.ofFun π₀) B')
    (C : Proc ι' acts' K) : lawOfW f C B = lawOfW f' C B' := by
  classical
  rw [lawOfW_eq_lawOfW'_of_almostFair f h C, lawOfW_eq_lawOfW'_of_almostFair f' h' C,
    lawOfW'_eq_pureOn_mixture f C B (queried B ∪ queried B') Finset.subset_union_left,
    lawOfW'_eq_pureOn_mixture f' C B' (queried B ∪ queried B') Finset.subset_union_right]
  refine Finset.sum_congr rfl fun π _ => ?_
  congr 1
  let π₀ : (d : ι') → acts' d := fun d =>
    if hd : d ∈ queried B ∪ queried B' then π ⟨d, hd⟩ else Classical.arbitrary _
  have hagree : ∀ d ∈ queried B ∪ queried B',
      Proc.pureOn C (queried B ∪ queried B') π d = Proc.ofFun π₀ d := by
    intro d hd
    rw [Proc.pureOn_of_mem C _ π hd]
    show FinDistr.pure (π ⟨d, hd⟩) = FinDistr.pure (π₀ d)
    simp only [π₀]
    rw [dif_pos hd]
  rw [lawOfW_congr_queried f B (fun d hd => hagree d (Finset.mem_union_left _ hd)),
    lawOfW_congr_queried f' B' (fun d hd => hagree d (Finset.mem_union_right _ hd)), hpure π₀]

end eq10

/-! ### E5: the pure grade does not exclude nesting; EQ-10 fails with nesting -/

/-- E5's bottom `d`-node: `a → (o1, 0)`, `b → (o2, 1)` (the subtree at E5's second node).
Source: `equiv.md` Definitions carried (E5 `degenerate_amd`, "bottom")
Kind: D -/
def e5Bot : Tree E5W Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => .leaf .o1 0
    | .b => .leaf .o2 1

/-- `Fair_{∼pure}`: every fiber pairwise equal in pure-law image.
Source: `equiv.md` EQ-4 ("the pure-grade relation")
Kind: D -/
def PureFair {Ω ι : Type} {acts : ι → Type} [DecidableEq ι] [∀ d, Fintype (acts d)]
    [∀ d, DecidableEq (acts d)] (B : Tree Ω ι acts K) : Prop :=
  FairWrt (fun _ T T' => LPure id T = LPure id T') B

/-- Every subtree of E5 at a decision node is E5 itself or its bottom node.
Source: none: infrastructure
Kind: L -/
theorem e5_subtree (q : e5.DecNode) : subtreeAt e5 q = e5 ∨ subtreeAt e5 q = e5Bot := by
  rcases q with _ | ⟨a, q⟩
  · exact Or.inl rfl
  · cases a
    · change Empty at q
      exact q.elim
    · rcases q with _ | ⟨b, e⟩
      · exact Or.inr rfl
      · cases b <;> (change Empty at e; exact e.elim)

/-- **E5's two `d`-subtrees have the same pure law, profile by profile**: playing `a` gives
`δ_{(o1,0)}` on both, playing `b` gives `δ_{(o2,1)}` on both.
Source: `equiv.md` EQ-4 ("E5's top and bottom subtrees have identical laws at both pure
profiles")
Kind: N+ -/
theorem e5_pure_eq (π : Unit → Act2) :
    lawOfW id (Proc.ofFun π) e5 = lawOfW id (Proc.ofFun π) e5Bot := by
  rw [lawOfW_id, lawOfW_id]
  unfold e5 e5Bot
  rcases hπ : π () with _ | _ <;>
    simp [contLaw_decision, contLaw_leaf, Proc.ofFun_w, hπ]

/-- E5's bottom node's Definition-6 law at `q`: `q δ_{(o1,0)} + (1−q) δ_{(o2,1)}`.
Source: `equiv.md` EQ-4 ("Definition-6 mass `2q − q²` vs `q` on the shared leaf")
Kind: L -/
theorem lawOfW_e5Bot (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    lawOfW id (procQ q h0 h1) e5Bot =
      q • Finsupp.single (E5W.o1, (0 : ℚ)) (1 : ℚ) +
        (1 - q) • Finsupp.single (E5W.o2, (1 : ℚ)) (1 : ℚ) := by
  rw [lawOfW_id]
  unfold e5Bot
  simp only [contLaw_decision, contLaw_leaf, Act2.sum_univ, procQ, FinDistr.act2_a,
    FinDistr.act2_b]

/-- **E5's two `d`-subtrees are not law-equivalent**: at `q = ½` the top puts `¾` on `(o1, 0)`,
the bottom `½`.
Source: `equiv.md` EQ-4 ("Definition-6 mass `2q − q²` vs `q` on the shared leaf, difference
`q(1−q)`")
Kind: N+ -/
theorem e5_not_lawEq : ¬ LawEq e5 e5Bot := by
  intro h
  have := h (procQ (1/2) (by norm_num) (by norm_num))
  rw [← lawOfW_id, ← lawOfW_id, lawOfW_e5, lawOfW_e5Bot] at this
  have h1 := congrArg (fun L => L (E5W.o1, (0 : ℚ))) this
  simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul] at h1
  norm_num at h1

/-- **E5 is `Fair_{∼pure}`** (its one fiber, `{top, bottom}`, has equal pure-law images) …
Source: `equiv.md` EQ-4 ("a stratified recursion with a `∼_pure` base certifies the nested E5
as fair")
Kind: N+ -/
theorem e5_pureFair : PureFair e5 := by
  intro d q _ q' _
  have hset : LPure id e5 = LPure id e5Bot := by
    ext L
    constructor
    · rintro ⟨π, rfl⟩; exact ⟨π, (e5_pure_eq π).symm⟩
    · rintro ⟨π, rfl⟩; exact ⟨π, e5_pure_eq π⟩
  rcases e5_subtree q with h | h <;> rcases e5_subtree q' with h' | h' <;> rw [h, h']
  · exact hset
  · exact hset.symm

/-- … while E5 is not law-fair (so not `≈_tr`-, `≃_Δ`-, `≃`- or `≅`-fair).
Source: `equiv.md` EQ-4
Kind: N+ -/
theorem e5_not_lawFair : ¬ LawFair e5 := by
  intro h
  have := h () none (by decide) (some ⟨.b, none⟩) (by decide)
  exact e5_not_lawEq this

/-- **EQ-4's pure-grade clause and EQ-10's nesting failure on one witness**: E5 is nested, its
`d`-fiber is pure-law-fair, and its two members agree on every pure profile yet differ in law
under the procedure `(½, ½)` — the pure grade does not exclude nesting, and `∼^f_pure ⟹ ∼^f_beh`
needs the non-nesting hypothesis of `AlmostFair.lawOfW_eq_of_pure_eq`. This is the pure-grade
clause of EQ-4's negative half only: the `≈_val` clause is in `AuditWitnesses.lean`
(`degen_fairValEq`; E5 is **not** its witness, `e5_not_fairValEq`, findings F13) and the `≈_law`
clause there too (`spur_lawFair`).
Source: `equiv.md` EQ-4 ("**not** by … the pure-grade relation: E5"); EQ-10 ("Fails with
nesting (E5 …)")
Kind: N+ -/
theorem e5_eq4_eq10_witness :
    Nested e5 () ∧ PureFair e5 ∧ ¬ LawFair e5 ∧
      (∀ π : Unit → Act2, lawOfW id (Proc.ofFun π) e5 = lawOfW id (Proc.ofFun π) e5Bot) ∧
      ¬ LawEq e5 e5Bot :=
  ⟨e5_nested, e5_pureFair, e5_not_lawFair, e5_pure_eq, e5_not_lawEq⟩

end Cleanroom.Decision.DpFairnessReloc

import Cleanroom.Decision.DpFairnessReloc.Fork
import Cleanroom.Decision.DpFairnessReloc.RelocateThms
import Cleanroom.Decision.DpFairnessReloc.Singleton

/-!
# Witnesses and refutations for T2, T3(c) and T4 (GR-9, Claim 1.2/L2, the AMD, Claim B)

Package `dp-fairness-reloc`, file 8. Every tree is over `ℚ`, rebuilt from the sources'
one-line descriptions.

* **GR-9 example (2)** (`gr2`): one point on two branches of a fair coin; left member
  `a → ½/½ → 1, 3`, `b → 0`; right member `a → 2`, `b → 0`. Value-fair, not law-fair: the converse
  of "law-fair ⟹ value-fair" is **refuted**.
* **GR-9 example (3), repaired** (`gr3`, no `side` coordinate): `a`-children `⅓/⅔ → (1, 3)` vs
  `⅓/⅓/⅓ → (1, 3, 3)`, `b → 0`. Law-fair under every procedure, not strongly fair (arity
  `2 ≠ 3`): the converse of "strongly fair ⟹ law-fair" is **refuted**.
* **Claim 1.2 / L2 on the AMD** (`amd_thetaAt_eq_iff`): the two nested nodes' continuation laws
  coincide iff `C(d)(a) = 0`, where the value is `1 < 4/3`; the AMD is not strongly fair. "Same
  statistics ⟹ equivalent subtrees" (L2) is **refuted**; the surviving neighbour is T3
  (law-fairness ⟹ equal statistics).
* **T4(d)**: the null repair `U = ∅` is the identity on values (`value_relocRoot_empty`), so on
  the AMD it keeps `(1−q)(3q+1)` and SE-7′'s identity fails without `U ⊇ {nested}`; the
  payoff-degenerate nested tree (`degen`) preserves value under every relocation although it is
  nested — FR-7(b)'s "iff" is an "if" (Claim F).
* **T4(e)**: the relocated AMD's value under `lift (procQ q)` is `1 − q` (`amd_reloc_value`), so
  the lifted family tops out at `1 < 4/3`; and no almost-fair tree matches the AMD's mixed value
  function through a point/action correspondence (`amd_no_almostFair_match`): an affine function
  through `(0, 1)` and `(1, 0)` misses `(1/3, 4/3)`.
* **Claim B witnesses**: the mugging `B₁` is not strongly fair (it violates the hypothesis, so
  Claim B does not apply to it); the two-point sequential tree `twoSeq` satisfies every
  hypothesis of Claim B jointly (N+), with singleton fibers.
-/

namespace Cleanroom.Decision.DpFairnessReloc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Finset

/-! ### Inversion lemmas for `≅` -/

section inversion

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

theorem LabIso.leaf_inj {ω ω' : Ω} {r r' : K}
    (h : LabIso (.leaf ω r : Tree Ω ι acts K) (.leaf ω' r')) : ω = ω' ∧ r = r' := by
  cases h; exact ⟨rfl, rfl⟩

theorem LabIso.decision_inj {d : ι} {child child' : acts d → Tree Ω ι acts K}
    (h : LabIso (.decision d child) (.decision d child')) : ∀ a, LabIso (child a) (child' a) := by
  cases h; assumption

theorem LabIso.chance_arity {n n' : ℕ} {β : FinDistr K (Fin n)} {β' : FinDistr K (Fin n')}
    {child : Fin n → Tree Ω ι acts K} {child' : Fin n' → Tree Ω ι acts K}
    (h : LabIso (.chance n β child) (.chance n' β' child')) : n = n' := by
  cases h; rfl

end inversion

/-! ### GR-9 example (2): value-fair, not law-fair -/

/-- The procedure playing `a` deterministically at the single point.
Source: none: infrastructure
Kind: D -/
def pureProc (a : Act2) : Proc Unit (fun _ => Act2) ℚ := fun _ => FinDistr.pure a

theorem deviatePure_unit (C : Proc Unit (fun _ => Act2) ℚ) (a : Act2) :
    C.deviatePure () a = pureProc a := by
  funext u; cases u; simp [Proc.deviatePure, Proc.deviate, pureProc]

/-- GR-9 (2), left member: `a → ½/½ → payoffs 1, 3`; `b → 0`.
Source: `grounding.md` GR-9 example (2)
Kind: D -/
def gr2L : Tree Unit Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => .chance 2 FinDistr.fair fun i => .leaf () (if i = 0 then 1 else 3)
    | .b => .leaf () 0

/-- GR-9 (2), right member: `a → 2`; `b → 0`.
Source: `grounding.md` GR-9 example (2)
Kind: D -/
def gr2R : Tree Unit Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => .leaf () 2
    | .b => .leaf () 0

/-- GR-9 (2): the two members on the two branches of a fair coin.
Source: `grounding.md` GR-9 example (2) ("one point `d` (`O_d = ⊤`) on two evented branches")
Kind: D -/
def gr2 : Tree Unit Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i => Fin.cases gr2L (fun _ => gr2R) i

theorem coin_w_zero (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : (FinDistr.coin p h0 h1).w 0 = p := rfl
theorem coin_w_one (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : (FinDistr.coin p h0 h1).w 1 = 1 - p := rfl
theorem third_w (i : Fin 3) : FinDistr.third.w i = 1/3 := by fin_cases i <;> rfl

theorem gr2L_value (a : Act2) : value (pureProc a) gr2L = value (pureProc a) gr2R := by
  cases a <;>
  · unfold value gr2L gr2R
    rw [sum_leaves_decision, Act2.sum_univ, sum_leaves_chance, Fin.sum_univ_two,
      Tree.sum_leaves_leaf, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf,
      sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
    norm_num [pureProc, FinDistr.fair, coin_w_zero, coin_w_one]
    try (split_ifs <;> norm_num)

/-- Every node of `gr2` carries the point and has subtree `gr2L` or `gr2R`.
Source: none: infrastructure
Kind: L -/
theorem gr2_subtree (q : gr2.DecNode) : subtreeAt gr2 q = gr2L ∨ subtreeAt gr2 q = gr2R := by
  obtain ⟨i, q⟩ := q
  fin_cases i
  · change gr2L.DecNode at q
    rcases q with _ | ⟨a, q⟩
    · exact Or.inl rfl
    · cases a
      · change (Tree.chance 2 FinDistr.fair fun i =>
          Tree.leaf () (if i = 0 then 1 else 3) : Tree Unit Unit (fun _ => Act2) ℚ).DecNode at q
        obtain ⟨i, q⟩ := q
        change Empty at q
        exact q.elim
      · change Empty at q
        exact q.elim
  · change gr2R.DecNode at q
    rcases q with _ | ⟨a, q⟩
    · exact Or.inr rfl
    · cases a <;> (change Empty at q; exact q.elim)

/-- **GR-9 (2) is value-fair**: both members have act values `2` at `a` and `0` at `b` under every
procedure.
Source: `grounding.md` GR-9 example (2) ("values agree for every `C`")
Kind: N+ -/
theorem gr2_valueFair : ValueFair gr2 := by
  intro d q _ q' _ C a
  cases d
  rw [deviatePure_unit]
  rcases gr2_subtree q with h | h <;> rcases gr2_subtree q' with h' | h' <;> rw [h, h']
  · exact gr2L_value a
  · exact (gr2L_value a).symm

/-- **GR-9 (2) is not law-fair**: under `a` the left member's law is `½δ_1 + ½δ_3`, the right's
is `δ_2`.
Source: `grounding.md` GR-9 example (2) ("laws differ")
Kind: N+ -/
theorem gr2_not_lawFair : ¬ LawFair gr2 := by
  intro h
  have := h () ⟨0, none⟩ (by simp [mem_fiber]) ⟨1, none⟩ (by simp [mem_fiber]) (pureProc .a)
  have h2 := congrArg (fun f => f ((), 2)) this
  change contLaw (pureProc .a) gr2L ((), 2) = contLaw (pureProc .a) gr2R ((), 2) at h2
  rw [contLaw_apply, contLaw_apply] at h2
  unfold gr2L gr2R at h2
  rw [sum_leaves_decision, Act2.sum_univ, sum_leaves_chance, Fin.sum_univ_two,
    Tree.sum_leaves_leaf, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf,
    sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf] at h2
  norm_num [pureProc, reduceCtorEq] at h2

/-- **The converse of "law-fair ⟹ value-fair" is refuted**: `gr2` is value-fair and not law-fair.
Source: `grounding.md` GR-9 ("both converses fail"); mandate T2(b)
Kind: N+
Fidelity: exact (worlds are `Unit`; `O_d = ⊤`) -/
theorem valueFair_not_lawFair : ∃ B : Tree Unit Unit (fun _ => Act2) ℚ, ValueFair B ∧ ¬ LawFair B :=
  ⟨gr2, gr2_valueFair, gr2_not_lawFair⟩

/-! ### GR-9 example (3), repaired: law-fair, not strongly fair -/

/-- GR-9 (3), left member: `a → ⅓/⅔ → (1, 3)`; `b → 0`.
Source: `grounding.md` GR-9 example (3) (repaired, no `side` coordinate)
Kind: D -/
def gr3L : Tree Unit Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => .chance 2 (FinDistr.coin (1/3) (by norm_num) (by norm_num))
        fun i => .leaf () (if i = 0 then 1 else 3)
    | .b => .leaf () 0

/-- GR-9 (3), right member: `a → ⅓/⅓/⅓ → (1, 3, 3)`; `b → 0`.
Source: `grounding.md` GR-9 example (3)
Kind: D -/
def gr3R : Tree Unit Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => .chance 3 FinDistr.third fun i => .leaf () (if i = 0 then 1 else 3)
    | .b => .leaf () 0

/-- GR-9 (3): the two members on the two branches of a fair coin.
Source: `grounding.md` GR-9 example (3)
Kind: D -/
def gr3 : Tree Unit Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i => Fin.cases gr3L (fun _ => gr3R) i

/-- The two members of GR-9 (3) have the same continuation law under every procedure.
Source: `grounding.md` GR-9 example (3) ("identical `(λ,r)`-laws under every procedure")
Kind: N+ -/
theorem gr3_contLaw_eq (C : Proc Unit (fun _ => Act2) ℚ) : contLaw C gr3L = contLaw C gr3R := by
  have hL : contLaw C gr3L = (C ()).w .a • ((1/3 : ℚ) • Finsupp.single ((), (1 : ℚ)) (1 : ℚ) +
      (1 - 1/3 : ℚ) • Finsupp.single ((), (3 : ℚ)) (1 : ℚ)) +
      (C ()).w .b • Finsupp.single ((), (0 : ℚ)) (1 : ℚ) := by
    unfold gr3L
    rw [contLaw_decision, Act2.sum_univ]
    show (C ()).w .a • contLaw C (.chance 2 (FinDistr.coin (1/3) (by norm_num) (by norm_num))
        fun i => .leaf () (if i = 0 then 1 else 3)) + (C ()).w .b • contLaw C (.leaf () 0) = _
    rw [contLaw_chance, Fin.sum_univ_two, coin_w_zero, coin_w_one]
    simp only [contLaw_leaf, Fin.isValue, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false,
      if_true]
  have hR : contLaw C gr3R = (C ()).w .a • ((1/3 : ℚ) • Finsupp.single ((), (1 : ℚ)) (1 : ℚ) +
      (1/3 : ℚ) • Finsupp.single ((), (3 : ℚ)) (1 : ℚ) +
      (1/3 : ℚ) • Finsupp.single ((), (3 : ℚ)) (1 : ℚ)) +
      (C ()).w .b • Finsupp.single ((), (0 : ℚ)) (1 : ℚ) := by
    unfold gr3R
    rw [contLaw_decision, Act2.sum_univ]
    show (C ()).w .a • contLaw C (.chance 3 FinDistr.third
        fun i => .leaf () (if i = 0 then 1 else 3)) + (C ()).w .b • contLaw C (.leaf () 0) = _
    rw [contLaw_chance, Fin.sum_univ_three, third_w, third_w, third_w]
    simp only [contLaw_leaf, Fin.isValue, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, Fin.reduceEq,
      if_false, if_true]
  rw [hL, hR]
  ext p
  simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> ring

theorem gr3_subtree (q : gr3.DecNode) : subtreeAt gr3 q = gr3L ∨ subtreeAt gr3 q = gr3R := by
  obtain ⟨i, q⟩ := q
  fin_cases i
  · change gr3L.DecNode at q
    rcases q with _ | ⟨a, q⟩
    · exact Or.inl rfl
    · cases a
      · change (Tree.chance 2 (FinDistr.coin (1/3) (by norm_num) (by norm_num)) fun i =>
          Tree.leaf () (if i = 0 then 1 else 3) : Tree Unit Unit (fun _ => Act2) ℚ).DecNode at q
        obtain ⟨i, q⟩ := q
        change Empty at q
        exact q.elim
      · change Empty at q
        exact q.elim
  · change gr3R.DecNode at q
    rcases q with _ | ⟨a, q⟩
    · exact Or.inr rfl
    · cases a
      · change (Tree.chance 3 FinDistr.third fun i =>
          Tree.leaf () (if i = 0 then 1 else 3) : Tree Unit Unit (fun _ => Act2) ℚ).DecNode at q
        obtain ⟨i, q⟩ := q
        change Empty at q
        exact q.elim
      · change Empty at q
        exact q.elim

/-- **GR-9 (3) is law-fair.**
Source: `grounding.md` GR-9 example (3)
Kind: N+ -/
theorem gr3_lawFair : LawFair gr3 := by
  intro d q _ q' _ C
  rcases gr3_subtree q with h | h <;> rcases gr3_subtree q' with h' | h' <;> rw [h, h']
  · exact gr3_contLaw_eq C
  · exact (gr3_contLaw_eq C).symm

/-- The two members are not isomorphic (arity `2 ≠ 3` at the `a`-children; a chance permutation
cannot repair an arity mismatch).
Source: `grounding.md` GR-9 example (3) ("not isomorphic (arity)")
Kind: N+ -/
theorem gr3_not_iso : ¬ LabIso gr3L gr3R := by
  intro h
  have := (LabIso.decision_inj h) .a
  have := LabIso.chance_arity this
  omega

/-- **GR-9 (3) is not strongly fair.**
Source: `grounding.md` GR-9 example (3)
Kind: N+ -/
theorem gr3_not_stronglyFair : ¬ StronglyFair gr3 := by
  intro h
  exact gr3_not_iso (h () ⟨0, none⟩ (by simp [mem_fiber]) ⟨1, none⟩ (by simp [mem_fiber]))

/-- **The converse of "strongly fair ⟹ law-fair" is refuted**: `gr3` is law-fair and not strongly
fair.
Source: `grounding.md` GR-9 ("both converses fail"); mandate T2(b)
Kind: N+
Fidelity: exact (worlds are `Unit`; no `side` coordinate, per the repair) -/
theorem lawFair_not_stronglyFair :
    ∃ B : Tree Unit Unit (fun _ => Act2) ℚ, LawFair B ∧ ¬ StronglyFair B :=
  ⟨gr3, gr3_lawFair, gr3_not_stronglyFair⟩

/-! ### Claim 1.2 / L2 on the AMD -/

/-- The AMD's lower node (below `b`): `a → 4`, `b → 1`.
Source: [[decision-problems-v2]] Proposition 5(c)
Kind: D -/
def amdBot : Tree AmdW Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => .leaf .sba 4
    | .b => .leaf .sbb 1

theorem amd_subtree_bot : subtreeAt amd (some ⟨.b, none⟩) = amdBot := rfl

/-- **Claim 1.2 (weak node-level statistics admit the AMD)**: the continuation laws of the AMD's
two nested nodes coincide iff `q := C(d)(a) = 0` — weak node-level equality of statistics does
not reject the nested tree; it selects "always `b`", whose value `1` is dominated by `4/3`.
Source: `fable-slop-notes.md` Claim 1.2 ("`θ₁ = θ₂` iff `x = 0` … admits the AMD tree, but
only for the procedure 'always continue', value `1 < 4/3`")
Kind: N+
Fidelity: exact -/
theorem amd_thetaAt_eq_iff (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    thetaAt (procQ q h0 h1) amd none = thetaAt (procQ q h0 h1) amd (some ⟨.b, none⟩) ↔ q = 0 := by
  unfold thetaAt
  rw [amd_subtree_bot]
  change contLaw (procQ q h0 h1) amd = contLaw (procQ q h0 h1) amdBot ↔ q = 0
  constructor
  · intro h
    have this : contLaw (procQ q h0 h1) amd (.sa, 0) = contLaw (procQ q h0 h1) amdBot (.sa, 0) := by
      rw [h]
    rw [contLaw_apply, contLaw_apply] at this
    unfold amd amdBot at this
    rw [sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, sum_leaves_decision,
      Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf, sum_leaves_decision,
      Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf] at this
    simpa [procQ] using this
  · rintro rfl
    ext ⟨w, r⟩
    rw [contLaw_apply, contLaw_apply]
    unfold amd amdBot
    rw [sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, sum_leaves_decision,
      Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf, sum_leaves_decision,
      Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
    simp [procQ]

/-- The AMD is not strongly fair (it is nested, FR-1(i)).
Source: `fable-slop-notes.md` Claim 1.2 ("Strong fairness rejects the tree outright")
Kind: N+ -/
theorem amd_not_stronglyFair : ¬ StronglyFair amd := fun h => h.not_nested () amd_nested

/-- **L2 refuted / Claim 1.2**: the AMD has equal node-level statistics at `q = 0` with value `1`,
while its optimum is `4/3` and it is not strongly fair — equal statistics do not give equivalent
(isomorphic) subtrees, nor a good procedure.
Source: `fable-slop-notes.md` Claim 1.2; mandate T2(d) (L2, dp-cf-036)
Kind: N+ -/
theorem l2_refuted :
    thetaAt (procQ 0 le_rfl zero_le_one) amd none =
        thetaAt (procQ 0 le_rfl zero_le_one) amd (some ⟨.b, none⟩) ∧
      value (procQ 0 le_rfl zero_le_one) amd = 1 ∧
      value (procQ (1/3) (by norm_num) (by norm_num)) amd = 4/3 ∧ ¬ StronglyFair amd :=
  ⟨(amd_thetaAt_eq_iff 0 le_rfl zero_le_one).mpr rfl, by rw [amd_value]; norm_num,
    amd_at_third.1, amd_not_stronglyFair⟩

/-! ### T4(e): the relocated AMD -/

/-- **The relocated AMD's value is `1 − q`**: with `U = {d}` (the nested point), Definition 6 on
the output is Definition 6′ on the input, whose value is `1 − q` (`amd_value'`).
Source: `fair-repair.md` FR-7(b) ("the relocated tree … has `V(x) = 1 − x`, sup `= 1 ≠ 4/3`")
Kind: C -/
theorem amd_reloc_value (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (lift {()} (procQ q h0 h1)) (relocRoot {()} amd) = 1 - q := by
  rw [value_relocRoot {()} (procQ q h0 h1) amd (fun d _ => by simp), amd_value']

/-- The lifted family on the relocated AMD tops out at `1`, below the AMD's `4/3`.
Source: `fair-repair.md` FR-7(b) ("sup `= 1 ≠ 4/3`")
Kind: N+ -/
theorem amd_reloc_le_one (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (lift {()} (procQ q h0 h1)) (relocRoot {()} amd) ≤ 1 ∧
      value (procQ (1/3) (by norm_num) (by norm_num)) amd = 4/3 :=
  ⟨by rw [amd_reloc_value]; linarith, amd_at_third.1⟩

/-- The mixed action `q·δ_x + (1−q)·δ_y` on a finite action type.
Source: none: infrastructure (a point/action correspondence carrying `(q, 1−q)`)
Kind: D -/
def FinDistr.mix2 {α : Type} [Fintype α] [DecidableEq α] (x y : α) (q : ℚ) (h0 : 0 ≤ q)
    (h1 : q ≤ 1) : FinDistr ℚ α where
  w z := q * (if z = x then 1 else 0) + (1 - q) * (if z = y then 1 else 0)
  nonneg z := by split_ifs <;> linarith
  sum_one := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    simp

/-- On an almost-fair tree the value at a two-point mixture is the mixture of the pure values
(multiaffinity in one coordinate).
Source: [[decision-problems-v2]] Definition 21 ("multiaffine in the tied variables")
Kind: C -/
theorem AlmostFair.value_mix2 {Ω' ι' : Type} {acts' : ι' → Type} [DecidableEq ι']
    [∀ d, Fintype (acts' d)] [∀ d, DecidableEq (acts' d)] {B : Tree Ω' ι' acts' ℚ}
    (h : AlmostFair B) (C : Proc ι' acts' ℚ) (d : ι') (x y : acts' d) (q : ℚ) (h0 : 0 ≤ q)
    (h1 : q ≤ 1) :
    value (C.deviate d (FinDistr.mix2 x y q h0 h1)) B =
      q * value (C.deviatePure d x) B + (1 - q) * value (C.deviatePure d y) B := by
  rw [h.value_eq_value', value'_deviate_sum _ B d]
  have hdev : ∀ a, (C.deviate d (FinDistr.mix2 x y q h0 h1)).deviatePure d a = C.deviatePure d a := by
    intro a
    funext e
    by_cases hed : e = d
    · subst hed; simp [Proc.deviatePure, Proc.deviate]
    · simp [Proc.deviatePure, Proc.deviate, Function.update_of_ne hed]
  simp only [hdev, Proc.deviate_same]
  have hx : ∀ a, (FinDistr.mix2 x y q h0 h1).w a * value' (C.deviatePure d a) B =
      q * (if a = x then value' (C.deviatePure d x) B else 0) +
        (1 - q) * (if a = y then value' (C.deviatePure d y) B else 0) := by
    intro a
    show (q * (if a = x then 1 else 0) + (1 - q) * (if a = y then 1 else 0)) * _ = _
    split_ifs <;> subst_vars <;> ring
  simp only [hx, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  rw [← h.value_eq_value', ← h.value_eq_value']

/-- **No almost-fair tree matches the AMD's mixed value function** (FR-7(c)): for every
almost-fair `B'`, every point `d'` of it, every pair of actions `x, y` playing the roles of the
AMD's `a, b`, and every `C'`, if the two pure act values match the AMD's (`0` at `a`, `1` at `b`)
then the value at the mixture `(1/3, 2/3)` is `2/3`, not the AMD's `4/3`: on almost-fair trees
`V` is affine in each coordinate, the AMD's is quadratic. (An arbitrary map of procedures that
agrees on the two pure profiles is *not* enough — the correspondence must act through a point
and its actions; see the findings.)
Source: `fair-repair.md` FR-7(c) ("no fair tree matches its mixed value function under any
correspondence"); `adversary-repair.md` C.1 ("a fair tree's `V` is multiaffine, the AMD's
`V(x) = (1−x)(3x+1)` is quadratic in one coordinate")
Kind: P
Fidelity: exact (the correspondence is a point/action map)
Hyps: none -/
theorem amd_no_almostFair_match {Ω' ι' : Type} {acts' : ι' → Type} [DecidableEq ι']
    [∀ d, Fintype (acts' d)] [∀ d, DecidableEq (acts' d)] {B' : Tree Ω' ι' acts' ℚ}
    (h : AlmostFair B') (d' : ι') (x y : acts' d') (C' : Proc ι' acts' ℚ)
    (hx : value (C'.deviatePure d' x) B' = value (procQ 1 zero_le_one le_rfl) amd)
    (hy : value (C'.deviatePure d' y) B' = value (procQ 0 le_rfl zero_le_one) amd) :
    value (C'.deviate d' (FinDistr.mix2 x y (1/3) (by norm_num) (by norm_num))) B' ≠
      value (procQ (1/3) (by norm_num) (by norm_num)) amd := by
  rw [AlmostFair.value_mix2 h, hx, hy, amd_value, amd_value, amd_value]
  norm_num

/-! ### T4(d): the null repair is the identity; payoff-degenerate nesting -/

section nullRepair

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [DecidableEq ι] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
  {Ω' : Type}

/-- With no relocated point, resolution is the identity on Definition-6 laws.
Source: `spectrum.md` SP-2 ("The null repair is the identity")
Kind: L -/
theorem leafLaw_resolveW_empty (C : Proc ι acts K) (g : Ω → Ω') (σ : (d : ↥(∅ : Finset ι)) → acts d) :
    (B : Tree Ω ι acts K) → ∀ ℓ',
      leafLaw (lift ∅ C) (resolveW ∅ g σ B) ℓ' = leafLaw C B (leafMapW ∅ g σ B ℓ')
  | .leaf _ _ => fun _ => rfl
  | .chance _ β child => by
      unfold resolveW leafMapW; rw [resolveAux_chance]; dsimp only
      rintro ⟨i, ℓ'⟩
      have ih := leafLaw_resolveW_empty C g σ (child i) ℓ'
      unfold resolveW leafMapW at ih
      show β.w i * leafLaw (lift ∅ C) (resolveAux ∅ g σ (child i)).1 ℓ' =
        β.w i * leafLaw C (child i) ((resolveAux ∅ g σ (child i)).2.1 ℓ')
      rw [ih]
  | .decision d child => by
      unfold resolveW leafMapW; rw [resolveAux_decision, dif_neg (Finset.notMem_empty d)]
      dsimp only
      rintro ⟨b, ℓ'⟩
      have ih := leafLaw_resolveW_empty C g σ (child b) ℓ'
      unfold resolveW leafMapW at ih
      show (C d).w b * leafLaw (lift ∅ C) (resolveAux ∅ g σ (child b)).1 ℓ' =
        (C d).w b * leafLaw C (child b) ((resolveAux ∅ g σ (child b)).2.1 ℓ')
      rw [ih]

/-- With no relocated point the leaf map is onto.
Source: none: infrastructure
Kind: L -/
theorem leafMapW_empty_surjective (g : Ω → Ω') (σ : (d : ↥(∅ : Finset ι)) → acts d) :
    (B : Tree Ω ι acts K) → ∀ ℓ, ∃ ℓ', leafMapW ∅ g σ B ℓ' = ℓ
  | .leaf _ _ => fun _ => ⟨(), rfl⟩
  | .chance _ _ child => by
      unfold resolveW leafMapW; rw [resolveAux_chance]; dsimp only
      rintro ⟨i, ℓ⟩
      obtain ⟨ℓ', hℓ'⟩ := leafMapW_empty_surjective g σ (child i) ℓ
      unfold leafMapW at hℓ'
      exact ⟨⟨i, ℓ'⟩, by rw [← hℓ']⟩
  | .decision d child => by
      unfold resolveW leafMapW; rw [resolveAux_decision, dif_neg (Finset.notMem_empty d)]
      dsimp only
      rintro ⟨b, ℓ⟩
      obtain ⟨ℓ', hℓ'⟩ := leafMapW_empty_surjective g σ (child b) ℓ
      unfold leafMapW at hℓ'
      exact ⟨⟨b, ℓ'⟩, by rw [← hℓ']⟩

/-- **SP-2: the null repair is the identity on values** — `V_{Rel_∅ B}(lift C) = V_B(C)` on every
tree (Definition 6 on both sides; the unary root draws the empty tuple with weight one).
Source: `spectrum.md` SP-2 ("The null repair is the identity")
Kind: P
Fidelity: exact -/
theorem value_relocRoot_empty (C : Proc ι acts K) (B : Tree Ω ι acts K) :
    value (lift ∅ C) (relocRoot ∅ B) = value C B := by
  rw [value_eq_push]
  unfold value
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  congr 1
  refine sum_preimage_eq (leafMap ∅ B) ?_ _ _ ?_ ?_ ℓ
  · rintro ⟨σ, ℓ₁⟩ ⟨σ', ℓ₂⟩ h
    have hσ : σ = σ' := Subsingleton.elim _ _
    subst hσ
    have := leafMapW_injective ∅ (fun ω => (ω, σ)) σ B h
    exact Sigma.ext rfl (heq_of_eq this)
  · rintro ⟨σ, ℓ'⟩
    show (lift ∅ C (Sum.inr ())).w σ * leafLaw (lift ∅ C) (resolve ∅ σ B) ℓ' = _
    have hw : (lift ∅ C (Sum.inr ())).w σ = 1 := by simp [lift_inr, FinDistr.pi_w]
    rw [hw, one_mul]
    exact leafLaw_resolveW_empty C _ σ B ℓ'
  · intro ℓ h
    exfalso
    let σ₀ : (d : ↥(∅ : Finset ι)) → acts d := fun d => (Finset.notMem_empty d.1 d.2).elim
    obtain ⟨ℓ', hℓ'⟩ := leafMapW_empty_surjective (fun ω => (ω, σ₀)) σ₀ B ℓ
    exact h ⟨σ₀, ℓ'⟩ hℓ'

end nullRepair

/-- **SE-7′'s hypothesis is necessary**: relocating nothing on the AMD keeps the Definition-6
value `(1−q)(3q+1)`, which at `q = 1/3` is `4/3 ≠ 2/3 = V'`.
Source: `seeds.md` SE-7′ ("with Definition 6 on the output it fails"); mandate T4(d) ("simply
`U = ∅` on the AMD")
Kind: N− -/
theorem amd_reloc_empty_value :
    value (lift ∅ (procQ (1/3) (by norm_num) (by norm_num))) (relocRoot ∅ amd) = 4/3 ∧
      value' (procQ (1/3) (by norm_num) (by norm_num)) amd = 2/3 := by
  rw [value_relocRoot_empty]; exact amd_at_third

/-- The payoff-degenerate nested tree of Claim F: first node `a → 0`, `b →` [second: `a → 0`,
`b → 0`].
Source: `adversary-repair.md` Claim F
Kind: D -/
def degen : Tree Unit Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => .leaf () 0
    | .b => .decision () fun _ => .leaf () 0

theorem degen_nested : Nested degen () := by
  refine ⟨by decide, ⟨.b, ⟨.a, ()⟩⟩, ?_, ?_⟩
  · unfold Positive degen; simp
  · unfold degen; simp

theorem degen_value (C : Proc Unit (fun _ => Act2) ℚ) : value C degen = 0 := by
  unfold value degen
  rw [sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, sum_leaves_decision, Act2.sum_univ,
    Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
  simp

/-- **FR-7(b)'s "iff" is an "if" (Claim F)**: the payoff-degenerate nested tree has value `0`
before and after every relocation, although it is nested — preservation *for this problem* does
not force non-nesting; only the class-level converse holds.
Source: `adversary-repair.md` Claim F ("a payoff-degenerate nested fiber … has `V ≡ 0` before
and after relocation"); `equiv.md` Dead 6
Kind: N− -/
theorem degen_reloc_value (U : Finset Unit) (C : Proc Unit (fun _ => Act2) ℚ) :
    value (lift U C) (relocRoot U degen) = value C degen ∧ Nested degen () := by
  refine ⟨?_, degen_nested⟩
  rw [value_eq_push, degen_value]
  apply Finset.sum_eq_zero
  intro ℓ _
  have : payoff degen ℓ = 0 := by
    obtain ⟨a, ℓ⟩ := ℓ
    cases a
    · rfl
    · change (Tree.decision () fun _ => Tree.leaf () 0 : Tree Unit Unit (fun _ => Act2) ℚ).Leaves at ℓ
      obtain ⟨b, ℓ⟩ := ℓ; rfl
  rw [this, mul_zero]

/-! ### Claim B witnesses -/

/-- The mugging `B₁` is not strongly fair: the `T`-node and the `H`-node have different leaf
worlds (Claim B does not apply to it; its two-member fiber is exactly the unfairness relocation
repairs).
Source: `fair-repair.md` FR-2 (the fiber `{T-node, H-node}`); `equiv.md` EQ-15 ("Mugging `B₁`
… UNFAIR all six")
Kind: N+ -/
theorem mug1_not_stronglyFair (x y : ℚ) : ¬ StronglyFair (mug1 x y) := by
  intro h
  have := h () ⟨0, none⟩ (by simp [mem_fiber]) ⟨1, none⟩ (by simp [mem_fiber])
  change LabIso (Tree.decision () (fun act : Act2 => Tree.leaf (mugWorld1 0 act)
      (mugPay x y (mugWorld1 0 act))) : Tree MugW Unit (fun _ => Act2) ℚ)
    (Tree.decision () fun act : Act2 => Tree.leaf (mugWorld1 1 act) (mugPay x y (mugWorld1 1 act)))
    at this
  have h2 := (LabIso.decision_inj this) .a
  have h3 := (LabIso.leaf_inj h2).1
  exact absurd h3 (by decide)

/-- Two-point sequential worlds `(act_e, act_d)`.
Source: mandate T3(c) ("a two-point sequential tree where every fiber is a singleton")
Kind: D -/
abbrev SeqW : Type := Act2 × Act2

/-- **The two-point sequential tree**: at `e`, `a → ` a `d`-node (`x ↦ (a, x)`), `b → (b, a)`.
Source: mandate T3(c)
Kind: D -/
def twoSeq : Tree SeqW GatePt (fun _ => Act2) ℚ :=
  .decision .e fun
    | .a => .decision .d fun x => .leaf (.a, x) 0
    | .b => .leaf (.b, .a) 0

/-- `O_e = ⊤`, `O_d = {act_e = a}`. Source: mandate T3(c). Kind: D -/
def seqObs : GatePt → Finset SeqW
  | .e => Finset.univ
  | .d => Finset.univ.filter fun w => w.1 = .a

/-- Act events: `e`'s on the first coordinate, `d`'s on the second. Source: mandate T3(c). Kind: D -/
def seqActEv : (p : GatePt) → Act2 → Finset SeqW
  | .e, v => Finset.univ.filter fun w => w.1 = v
  | .d, v => Finset.univ.filter fun w => w.2 = v

theorem twoSeq_fibers_singleton :
    ∀ d, ∀ q ∈ fiber twoSeq d, ∀ q' ∈ fiber twoSeq d, q = q' := by
  decide

/-- `twoSeq` is strongly fair (all fibers are singletons).
Source: mandate T3(c)
Kind: N+ -/
theorem twoSeq_stronglyFair : StronglyFair twoSeq := by
  intro d q hq q' hq'
  rw [twoSeq_fibers_singleton d q hq q' hq']
  exact LabIso.refl _

theorem twoSeq_eventedChance : EventedChance twoSeq := by
  intro a
  cases a
  · exact fun _ => trivial
  · exact trivial

theorem twoSeq_pruned : Pruned twoSeq := by
  intro ℓ
  obtain ⟨a, ℓ⟩ := ℓ
  cases a
  · obtain ⟨x, ℓ⟩ := ℓ
    show (0 : ℚ) < 1; norm_num
  · show (0 : ℚ) < 1; norm_num

theorem twoSeq_records_d : RecordsForAll seqObs seqActEv twoSeq .d := by
  intro C ℓ _ hobs
  have key : ∀ ℓ : twoSeq.Leaves, world twoSeq ℓ ∈ seqObs .d →
      count .d twoSeq ℓ = 1 ∧
      ∀ q : twoSeq.DecNode, pt twoSeq q = .d → ∀ a, edgeOf twoSeq q ℓ = some a →
        (∀ ℓ' ∈ leavesBelow twoSeq q, world twoSeq ℓ' ∈ seqObs (pt twoSeq q)) ∧
        world twoSeq ℓ ∈ seqActEv (pt twoSeq q) a ∧
        ∀ a', world twoSeq ℓ ∈ seqActEv (pt twoSeq q) a' → a' = a := by decide
  exact key ℓ hobs

theorem twoSeq_records_e : RecordsForAll seqObs seqActEv twoSeq .e := by
  intro C ℓ _ hobs
  have key : ∀ ℓ : twoSeq.Leaves, world twoSeq ℓ ∈ seqObs .e →
      count .e twoSeq ℓ = 1 ∧
      ∀ q : twoSeq.DecNode, pt twoSeq q = .e → ∀ a, edgeOf twoSeq q ℓ = some a →
        (∀ ℓ' ∈ leavesBelow twoSeq q, world twoSeq ℓ' ∈ seqObs (pt twoSeq q)) ∧
        world twoSeq ℓ ∈ seqActEv (pt twoSeq q) a ∧
        ∀ a', world twoSeq ℓ ∈ seqActEv (pt twoSeq q) a' → a' = a := by decide
  exact key ℓ hobs

/-- **Claim B's hypotheses are jointly satisfiable on a chance-free tree (N−)**: `twoSeq` is
strongly fair, evented, pruned, records at both points for every procedure and realizes both
observations — and its fibers are singletons, as the theorem says. Graded N− (audit r1): the tree
has no chance node, so `EventedChance` and `Pruned` hold for every tree of its shape
(`NoChance.eventedChance`, `NoChance.pruned`, `twoSeq_noChance` in `MoreWitnesses.lean`) and
strong fairness is `LabIso.refl` on singleton fibers; only recording is exercised. The N+ with a
chance node is `coinSeq_claimB`.
Source: mandate T3(c)
Kind: N− -/
theorem twoSeq_claimB :
    StronglyFair twoSeq ∧ EventedChance twoSeq ∧ Pruned twoSeq ∧
      (∀ e ∈ queried twoSeq, RecordsForAll seqObs seqActEv twoSeq e) ∧
      (∀ e ∈ queried twoSeq, ∃ ℓ, Positive twoSeq ℓ ∧ world twoSeq ℓ ∈ seqObs e) ∧
      ∀ d, ∀ q ∈ fiber twoSeq d, ∀ q' ∈ fiber twoSeq d, q = q' := by
  refine ⟨twoSeq_stronglyFair, twoSeq_eventedChance, twoSeq_pruned, ?_, ?_, ?_⟩
  · intro e _
    cases e
    · exact twoSeq_records_e
    · exact twoSeq_records_d
  · intro e _
    refine ⟨⟨.a, ⟨.a, ()⟩⟩, twoSeq_pruned _, ?_⟩
    cases e <;> decide
  · exact singleton_fibers_of_recordsForAll seqObs seqActEv twoSeq_stronglyFair
      twoSeq_eventedChance twoSeq_pruned
      (fun e _ => by cases e; exact twoSeq_records_e; exact twoSeq_records_d)
      (fun e _ => ⟨⟨.a, ⟨.a, ()⟩⟩, twoSeq_pruned _, by cases e <;> decide⟩)

end Cleanroom.Decision.DpFairnessReloc

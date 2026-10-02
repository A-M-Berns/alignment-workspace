import Cleanroom.Decision.DpEdtUdtFair.Theorem3

/-!
# A fiber whose members are isomorphic but not equal (audit round 1, NB8)

Every `𝔉`-witness of round 0 had singleton fibers or literally equal members (`dupPay`), so the
fiber isomorphism `LabIso.contLaw_eq` was exercised only through `LabIso.refl`. `permPay` fixes
that: a fair coin over two `d`-nodes whose subtrees are `decision d (act ↦ chance β_i [leaf
(act, j = i)])` with `β_0 = (⅓, ⅔)` and `β_1 = (⅔, ⅓)` — the same continuation law
(`(act, true)` w.p. `⅓`, `(act, false)` w.p. `⅔`) with the chance children in the other order, so
the members are `LabIso` through the swap `σ = (0 1)` and are **not** equal trees. Worlds are
`(act, coin₂)`, so the tree records (`O = ⊤`, act events `{act = v}`) and is in `𝔉`; payoffs
`a ↦ 3, 1` and `b ↦ 1, 1`, so `Q(a) = 5/3 > 1 = Q(b)`: `δ_a` is D2-consistent and optimal,
`δ_b` is not optimal (`permPay_theorem3_witness`).
-/

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace Cleanroom.Decision.DpEdtUdtFair

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt
open Cleanroom.Decision.DpCalibration

section permPay

/-- Worlds `(act, coin₂)`. Source: audit round 1 NB8. Kind: D -/
abbrev PermW : Type := Act2 × Bool

/-- Payoffs: `a ↦ 3` on `true`, `1` on `false`; `b ↦ 1`. Source: audit round 1 NB8. Kind: D -/
def permPayoff (act : Act2) (b : Bool) : ℚ := if act = .a then (if b then 3 else 1) else 1

/-- The two chance laws `(⅓, ⅔)` and `(⅔, ⅓)`. Source: audit round 1 NB8. Kind: D -/
def permβ : Fin 2 → FinDistr ℚ (Fin 2) :=
  ![FinDistr.coin (1 / 3) (by norm_num) (by norm_num),
    FinDistr.coin (2 / 3) (by norm_num) (by norm_num)]

/-- **`permPay`**: a fair coin over two `d`-nodes whose subtrees are isomorphic through a swap of
the chance children and not equal.
Source: audit round 1 NB8 ("a two-member fiber whose members are isomorphic but not equal");
`fair-repair.md` FR-1(ii) (the continuation law is what fairness preserves)
Kind: D -/
def permMember (i : Fin 2) : Tree PermW Unit (fun _ => Act2) ℚ :=
  .decision () fun act =>
    .chance 2 (permβ i) fun j => .leaf (act, decide (j = i)) (permPayoff act (decide (j = i)))

/-- **`permPay`** proper: the fair coin over the two members. Source: audit round 1 NB8. Kind: D -/
def permPay : Tree PermW Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i => permMember i

/-- `O_d = ⊤`. Source: audit round 1 NB8. Kind: D -/
def permObs : Unit → Finset PermW := fun _ => Finset.univ

/-- Act events `{act = v}`. Source: audit round 1 NB8. Kind: D -/
def permActEv : Unit → Act2 → Finset PermW := fun _ v => Finset.univ.filter fun w => w.1 = v

/-- The two members are labelled-isomorphic through the swap of the chance children.
Source: audit round 1 NB8
Kind: L -/
theorem permPay_iso01 : LabIso (subtreeAt permPay ⟨0, none⟩) (subtreeAt permPay ⟨1, none⟩) := by
  show LabIso (permMember 0) (permMember 1)
  unfold permMember
  refine LabIso.decision () _ _ fun act => ?_
  refine LabIso.chance _ _ _ _ (Equiv.swap 0 1) ?_ ?_
  · intro i; fin_cases i <;> simp [permβ, FinDistr.coin] <;> norm_num
  · intro j; fin_cases j <;> exact LabIso.of_eq (by simp)

/-- The two members are not equal trees (their chance laws differ).
Source: audit round 1 NB8
Kind: L -/
theorem permPay_members_ne : subtreeAt permPay ⟨0, none⟩ ≠ subtreeAt permPay ⟨1, none⟩ := by
  intro h
  change permMember 0 = permMember 1 at h
  unfold permMember at h
  have h1 := congrFun (eq_of_heq (Tree.decision.inj h).2) Act2.a
  have h2 := eq_of_heq (Tree.chance.inj h1).2.1
  have h3 := congrArg (fun β : FinDistr ℚ (Fin 2) => β.w 0) h2
  simp [permβ, FinDistr.coin] at h3
  norm_num at h3

/-- `permPay` is strongly fair: its only fiber has the two members, isomorphic by
`permPay_iso01`.
Source: audit round 1 NB8
Kind: N+ -/
theorem permPay_stronglyFair : StronglyFair permPay := by
  intro d q _ q' _
  obtain ⟨i, q⟩ := q
  obtain ⟨i', q'⟩ := q'
  rcases q with _ | ⟨x, q⟩
  · rcases q' with _ | ⟨x', q'⟩
    · fin_cases i <;> fin_cases i'
      · exact LabIso.refl _
      · exact permPay_iso01
      · exact permPay_iso01.symm
      · exact LabIso.refl _
    · obtain ⟨j, e⟩ := q'; exact e.elim
  · obtain ⟨j, e⟩ := q; exact e.elim

/-- `permPay` records at its point for every procedure (`O = ⊤`, the world carries the act).
Source: audit round 1 NB8
Kind: N+ -/
theorem permPay_recordsForAll : RecordsForAll permObs permActEv permPay () := by
  intro C ℓ _ _
  unfold permPay permMember at ℓ ⊢
  obtain ⟨i, act, j, _⟩ := ℓ
  refine ⟨by simp [count_chance, count_decision, count_leaf], ?_⟩
  rintro ⟨i', (_ | ⟨b, q⟩)⟩ hq a ha
  · by_cases hi : i = i'
    · subst hi
      simp only [edgeOf_chance, dite_true, edgeOf_decision_none, Option.some.injEq] at ha
      subst ha
      refine ⟨fun _ _ => by simp [permObs], ?_, ?_⟩
      · simp [permActEv, world_chance, world_decision, world_leaf]
      · intro a' ha'
        simp [permActEv, world_chance, world_decision, world_leaf] at ha'
        exact ha'.symm
    · simp [edgeOf_chance, hi] at ha
  · obtain ⟨j', e⟩ := q; exact e.elim

/-- `permPay` is pruned. Source: none: infrastructure. Kind: L -/
theorem permPay_pruned : Pruned permPay := by
  rintro ⟨i, act, j, _⟩
  unfold Positive permPay permMember
  simp only [chanceWeight_chance, chanceWeight_decision, chanceWeight_leaf, mul_one]
  fin_cases i <;> fin_cases j <;> simp [FinDistr.fair, FinDistr.coin, permβ] <;> norm_num

/-- **`permPay ∈ 𝔉`** with a two-member fiber of isomorphic, unequal members.
Source: audit round 1 NB8
Kind: N+ -/
theorem permPay_fairClass : FairClass permObs permActEv permPay where
  stronglyFair := permPay_stronglyFair
  frec := fun d _ => by cases d; exact permPay_recordsForAll
  pruned := permPay_pruned
  realized := fun d _ => by
    cases d
    exact ⟨⟨0, .a, 0, ()⟩, permPay_pruned _, by simp [permObs]⟩

/-- `Q` on `permPay`: `Q(a) = 5/3`, `Q(b) = 1` (read at the first member; the second gives the
same by `stronglyFair_value_eq_Q`, through the swap).
Source: audit round 1 NB8
Kind: L -/
theorem permPay_Q (C : Proc Unit (fun _ => Act2) ℚ) :
    Q C permPay () .a = 5 / 3 ∧ Q C permPay () .b = 1 := by
  constructor <;>
  · rw [← stronglyFair_value_eq_Q permPay_stronglyFair C (q := ⟨0, none⟩) (d := ())
      (c := fun act => .chance 2 (permβ 0) fun j =>
        .leaf (act, decide (j = 0)) (permPayoff act (decide (j = 0)))) rfl]
    simp [DpLocalOpt.value_chance, DpLocalOpt.value_leaf, Fin.sum_univ_two, permβ, FinDistr.coin,
      permPayoff]
    try norm_num

/-- Values on `permPay`: `V(δ_a) = 5/3`, `V(δ_b) = 1`. Source: audit round 1 NB8. Kind: L -/
theorem permPay_values :
    value (Proc.ofFun fun _ => Act2.a) permPay = 5 / 3 ∧
    value (Proc.ofFun fun _ => Act2.b) permPay = 1 := by
  constructor <;>
  · simp [permPay, permMember, DpLocalOpt.value_chance, DpLocalOpt.value_decision,
      DpLocalOpt.value_leaf, Fin.sum_univ_two, Act2.sum_univ, Proc.ofFun_w, FinDistr.fair,
      FinDistr.coin, permβ, permPayoff]
    try norm_num

/-- **Theorem 3's witness on a fiber of isomorphic, unequal members**: `permPay ∈ 𝔉`, its two
`d`-nodes are `LabIso` (through a non-identity permutation of chance children) and not equal,
`δ_a` is D2-consistent and optimal (`V = 5/3`), `δ_b` is not optimal (`V = 1`). Here
`stronglyFair_value_eq_Q` and `sum_drew_eq` genuinely use `LabIso.contLaw_eq` through the swap.
Source: audit round 1 NB8; `fair-repair.md` FR-1(ii)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem permPay_theorem3_witness :
    FairClass permObs permActEv permPay ∧
    LabIso (subtreeAt permPay ⟨0, none⟩) (subtreeAt permPay ⟨1, none⟩) ∧
    subtreeAt permPay ⟨0, none⟩ ≠ subtreeAt permPay ⟨1, none⟩ ∧
    EventTrembleEdtConsistent permObs permActEv (Proc.ofFun fun _ => Act2.a) permPay ∧
    IsOptimal (Proc.ofFun fun _ => Act2.a) permPay ∧
    value (Proc.ofFun fun _ => Act2.a) permPay = 5 / 3 ∧
    ¬ IsOptimal (Proc.ofFun fun _ => Act2.b) permPay := by
  have hD2 : EventTrembleEdtConsistent permObs permActEv (Proc.ofFun fun _ => Act2.a) permPay := by
    rw [permPay_fairClass.eventTremble_iff_Q]
    refine ⟨1, one_pos, fun ε h0 h1 _ d _ a ha b => ?_⟩
    cases d
    cases a <;> cases b <;> simp [(permPay_Q _).1, (permPay_Q _).2, Proc.ofFun_w] at ha ⊢
    norm_num
  refine ⟨permPay_fairClass, permPay_iso01, permPay_members_ne, hD2,
    eventTrembleEdt_isOptimal_of_fairClass permPay_fairClass hD2, permPay_values.1, fun h => ?_⟩
  have := h (Proc.ofFun fun _ => Act2.a)
  rw [permPay_values.1, permPay_values.2] at this
  norm_num at this

end permPay

end Cleanroom.Decision.DpEdtUdtFair

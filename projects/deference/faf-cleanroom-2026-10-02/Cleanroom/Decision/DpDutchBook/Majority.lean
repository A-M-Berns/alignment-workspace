import Cleanroom.Decision.DpDutchBook.NewcombSeed

/-!
# T12: mako yass's majority game — three copies of one point under both semantics

Three `d`-nodes in sequence (`majority3`), payoff `1` iff the majority of the three draws is
`a`; the live draw is the last. Under **Definition 6** the draws are i.i.d. from the label, so
the live draw is independent of "both others drew `a`" (`maj_product_identity`:
`ν(live = a ∧ others = aa)·ν(⊤) = ν(live = a)·ν(others = aa)`, a product identity, not
`screening_recorded`), and the calibrated conditional value of `a` is `1 − (1−q)²`
(`majE_a`), of `b` is `q²` (`majE_b`): the value of "hold the others fixed and play `a`". Under
**6′** all copies draw alike (`maj_leafLaw'`): `ν'(live = a ∧ others = aa) = q ≠ q³`
(`maj_nu'_live_othersAA`, `maj_product_fails'`), and the calibrated conditional says "majority
= me": `E'[r ∣ live = a] = 1`, `E'[r ∣ live = b] = 0` (`majE'_values`). Never computed in the
source (dp-sl-2-028); these closed forms are the first.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpDutchBook

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-- Worlds: the three draws, the live one last. Source: dp-sl-2-028. Kind: D -/
abbrev MajW : Type := Act2 × Act2 × Act2

/-- "The majority of the three draws is `a`". Source: dp-sl-2-028 ("payoff `1` if the majority
of the three draws is `a`"). Kind: D -/
def majA (x₁ x₂ x₃ : Act2) : Prop :=
  (x₁ = .a ∧ x₂ = .a) ∨ (x₁ = .a ∧ x₃ = .a) ∨ (x₂ = .a ∧ x₃ = .a)

instance (x₁ x₂ x₃ : Act2) : Decidable (majA x₁ x₂ x₃) := by unfold majA; infer_instance

/-- **The majority game**: three copies of the one point `d` in sequence, payoff `1` iff the
majority of the draws is `a`. Source: dp-sl-2-028; P09-14 (P09.md line 84); mandate T12
Kind: D
Fidelity: exact (the live draw is the last copy) -/
def majority3 : Tree MajW Unit (fun _ => Act2) ℚ :=
  .decision () fun x₁ => .decision () fun x₂ => .decision () fun x₃ =>
    .leaf (x₁, x₂, x₃) (if majA x₁ x₂ x₃ then 1 else 0)

/-- `O_d = ⊤`. Source: dp-sl-2-028. Kind: D -/
def majObs : Unit → Finset MajW := fun _ => Finset.univ

/-- The live draw. Source: dp-sl-2-028. Kind: D -/
def majLive : Unit → Act2 → Finset MajW := fun _ a => Finset.univ.filter fun w => w.2.2 = a

/-- "Both others drew `a`". Source: dp-sl-2-028 ("`others = aa`"). Kind: D -/
def majOthersAA : Finset MajW := Finset.univ.filter fun w => w.1 = .a ∧ w.2.1 = .a

section tree

variable (C : Proc Unit (fun _ => Act2) ℚ)

/-- Sums over the eight leaves. Source: none: infrastructure. Kind: L -/
theorem majority3_sum {M : Type} [AddCommMonoid M] (f : majority3.Leaves → M) :
    ∑ ℓ, f ℓ = ∑ x₁ : Act2, ∑ x₂ : Act2, ∑ x₃ : Act2, f ⟨x₁, ⟨x₂, ⟨x₃, ()⟩⟩⟩ := by
  unfold majority3 at f ⊢
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun x₁ _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun x₂ _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun x₃ _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- `ν(live = a) = C(d)(a)`, `ν(others = aa) = q²`, `ν(live = a ∧ others = aa) = q³`,
`ν(⊤) = 1` under Definition 6. Source: dp-sl-2-028 ("the draws are i.i.d. `C(d)`"). Kind: L -/
theorem maj_nu (a : Act2) :
    nu C majority3 (majLive () a) = (C ()).w a ∧
      nu C majority3 majOthersAA = (C ()).w .a ^ 2 ∧
      nu C majority3 (majLive () .a ∩ majOthersAA) = (C ()).w .a ^ 3 ∧
      nu C majority3 (majObs ()) = 1 := by
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [nu_eq_sum, majority3_sum]
    try cases a
    all_goals
      simp [Act2.sum_univ, majority3, majLive, majOthersAA, majObs]
      (try rw [hb]); ring

/-- **The product identity under Definition 6**: the live draw is independent of "both others
drew `a`": `ν(live = a ∧ others = aa)·ν(⊤) = ν(live = a)·ν(others = aa)` — a product identity
of i.i.d. draws, not `screening_recorded` (whose one-node hypothesis fails here).
Source: dp-sl-2-028 ("the live draw is independent of the majority-of-others given the node");
mandate T12
Kind: P
Fidelity: exact -/
theorem maj_product_identity :
    nu C majority3 (majLive () .a ∩ majOthersAA) * nu C majority3 (majObs ()) =
      nu C majority3 (majLive () .a) * nu C majority3 majOthersAA := by
  obtain ⟨h1, h2, h3, h4⟩ := maj_nu C .a
  rw [h1, h2, h3, h4]; ring

/-- The strictly calibrated act value `E[r ∣ live = a]`. Source: dp-sl-2-028. Kind: D -/
noncomputable def majE (a : Act2) : ℚ := condExp C majority3 (majLive () a)

/-- `𝔼[r·1_{live = a}] = q(1 − (1−q)²)`, `𝔼[r·1_{live = b}] = (1−q)q²` under Definition 6.
Source: none: infrastructure. Kind: L -/
theorem maj_paySum :
    paySum C majority3 (majLive () .a) = (C ()).w .a * (1 - (1 - (C ()).w .a) ^ 2) ∧
      paySum C majority3 (majLive () .b) = (1 - (C ()).w .a) * (C ()).w .a ^ 2 := by
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  constructor <;>
  · rw [paySum_eq_sum_ite, majority3_sum]
    simp [Act2.sum_univ, majority3, majLive, majA]
    rw [hb]; ring

/-- **Definition 6: the calibrated conditional value of `a` is `1 − (1−q)²`** (the others are
i.i.d. from the label and the live draw is independent of them: "hold the others fixed and play
`a`" is the same number), and of `b` is `q²`.
Source: dp-sl-2-028 ("the classical 'hold the others fixed' value equals the calibrated
conditional"); mandate T12
Kind: P
Fidelity: exact
Hyps: (a) the act realized -/
theorem majE_a (hq : 0 < (C ()).w .a) : majE C .a = 1 - (1 - (C ()).w .a) ^ 2 := by
  unfold majE condExp
  rw [(maj_paySum C).1, (maj_nu C .a).1]
  field_simp

/-- `E[r ∣ live = b] = q²` under Definition 6. Source: dp-sl-2-028; mandate T12. Kind: P.
Fidelity: exact. Hyps: (a) the act realized -/
theorem majE_b (hq : 0 < (C ()).w .b) : majE C .b = (C ()).w .a ^ 2 := by
  unfold majE condExp
  rw [(maj_paySum C).2, (maj_nu C .b).1]
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  rw [hb] at hq ⊢
  field_simp

/-! ### The shared seed -/

/-- **The 6′ run law: all copies draw alike**, `μ'(x₁, x₂, x₃) = C(d)(x₁)·[x₁ = x₂]·[x₁ = x₃]`.
Source: `seeds.md` Definition 6′; dp-sl-2-028 ("6′: all copies draw alike"). Kind: P.
Fidelity: exact -/
theorem maj_leafLaw' (x₁ x₂ x₃ : Act2) :
    leafLaw' C majority3 ⟨x₁, ⟨x₂, ⟨x₃, ()⟩⟩⟩ =
      (C ()).w x₁ * (if x₁ = x₂ then 1 else 0) * (if x₁ = x₃ then 1 else 0) := by
  unfold leafLaw' majority3
  rw [leafLawSeed_decision_of_none C rfl, leafLawSeed_decision_of_some C (a' := x₁) (by simp),
    leafLawSeed_decision_of_some C (a' := x₁) (by simp)]
  simp only [leafLawSeed_leaf]
  split_ifs <;> ring

/-- **Under 6′ `ν'(live = a ∧ others = aa) = q = ν'(live = a) = ν'(others = aa)`**, so the
product identity fails for every properly mixed label (`q ≠ q·q`).
Source: dp-sl-2-028 ("`ν'(live = a ∧ others = aa) = q ≠ q³`"); mandate T12
Kind: P
Fidelity: exact -/
theorem maj_nu'_live_othersAA :
    nu' C majority3 (majLive () .a ∩ majOthersAA) = (C ()).w .a ∧
      nu' C majority3 (majLive () .a) = (C ()).w .a ∧
      nu' C majority3 majOthersAA = (C ()).w .a ∧
      nu' C majority3 (majObs ()) = 1 := by
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [nu'_eq_sum_ite, majority3_sum]
    simp only [maj_leafLaw']
    simp [Act2.sum_univ, majority3, majLive, majOthersAA, majObs]
    try linarith

/-- The product identity fails under 6′ at every properly mixed label.
Source: dp-sl-2-028; mandate T12. Kind: P. Fidelity: exact. Hyps: (a) `0 < q < 1` -/
theorem maj_product_fails' (h0 : 0 < (C ()).w .a) (h1 : (C ()).w .a < 1) :
    nu' C majority3 (majLive () .a ∩ majOthersAA) * nu' C majority3 (majObs ()) ≠
      nu' C majority3 (majLive () .a) * nu' C majority3 majOthersAA := by
  obtain ⟨e1, e2, e3, e4⟩ := maj_nu'_live_othersAA C
  rw [e1, e2, e3, e4]
  intro h
  nlinarith

/-- The 6′ strict act value. Source: dp-sl-2-028. Kind: D. Fidelity: variant: 6′ -/
noncomputable def majE' (a : Act2) : ℚ := condExpSeed C majority3 (majLive () a)

/-- **Under 6′ the calibrated conditional says "majority = me"**: `E'[r ∣ live = a] = 1`,
`E'[r ∣ live = b] = 0` at every label with `a` realized.
Source: dp-sl-2-028 ("the calibrated conditional says 'majority = me'"); mandate T12
Kind: P
Fidelity: variant: 6′
Hyps: (a) `0 < q` -/
theorem majE'_values (h0 : 0 < (C ()).w .a) :
    majE' C .a = 1 ∧ majE' C .b = 0 := by
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  have hpa : paySumSeed C majority3 (majLive () .a) = (C ()).w .a := by
    rw [paySumSeed_eq_sum_ite, majority3_sum]
    simp only [maj_leafLaw']
    simp [Act2.sum_univ, majority3, majLive, majA]
  have hpb : paySumSeed C majority3 (majLive () .b) = 0 := by
    rw [paySumSeed_eq_sum_ite, majority3_sum]
    simp only [maj_leafLaw']
    simp [Act2.sum_univ, majority3, majLive, majA]
  constructor
  · unfold majE' condExpSeed
    rw [hpa, (maj_nu'_live_othersAA C).2.1]
    field_simp
  · unfold majE' condExpSeed
    rw [hpb]; simp

end tree

end Cleanroom.Decision.DpDutchBook

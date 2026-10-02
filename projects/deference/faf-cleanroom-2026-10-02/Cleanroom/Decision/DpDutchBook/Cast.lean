import Cleanroom.Decision.DpDutchBook.MsrExists
import Cleanroom.Decision.DpCalibration.MiniDevices

/-!
# Base change `ℚ → ℝ`, and T7(e): the `ℝ`-cast miniature as the witness of MSR existence

Mandate §3.1: every `ℝ`-witness is the cast of a catalogue tree, never a tree re-defined over
`ℝ` by hand. `castDistr`/`castTree`/`castProc` are the mandate's `FinDistr.map Rat.cast` /
`Tree.castR` / `Proc.castR` (named without the `Tree.`/`Proc.` prefix so as not to add
declarations to `dp-core-tree`'s namespaces). The leaves of the cast tree are in bijection with
the base leaves (`castLeafEquiv`), and `leafLaw`, `world`, `payoff`, `chanceWeight`, `nu`,
`paySum`, `value`, `condExp` transport along the cast (`…_cast`, all `L`). `nuPoly`/`limitVal`
are **not** transported here: the `ℝ`-values below are computed through `r3Val_eq_qSum_div` on
the cast tree and then shown equal to the casts of `dp-calibration`'s `limitVal_mini`.

**T7(e), the N+ witness for `msrAtD4_exists`** (`miniR := castTree miniature`): the hypothesis
package is inhabited — `ActRecordingStruct` (the live nodes are node-action-veridical, the
predictor node is not), disjoint action events, the standing hypothesis `ν(O_d) = 1 > 0` —
and the tremble-pinned values are `r3Val m = (2·m(b), m(a))` at **every** `ℝ`-label
(`miniR_r3Val_a/_b`), so the best-response face flips at `m(a) = 2/3` (`miniR_br_flips`: the
correspondence is not constant — a recorded point's constant face would not be a witness) and
`MsrAtD4` holds at `C[d ↦ m]` iff `m(a) = 2/3` (`miniR_msrAtD4_iff`). Kakutani's fixed point is
therefore `2/3` (`miniR_msrAtD4_exists_witness`). The values are the casts of `limitVal_mini`
(`miniR_r3Val_cast_limitVal`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpDutchBook

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

variable {Ω ι : Type} {acts : ι → Type} [∀ d, Fintype (acts d)]

/-! ### The cast -/

/-- **Base change of a finite distribution** `ℚ → ℝ` (the mandate's `FinDistr.map Rat.cast`).
Source: mandate §3.1
Kind: D -/
def castDistr {α : Type} [Fintype α] (m : FinDistr ℚ α) : FinDistr ℝ α where
  w a := (m.w a : ℝ)
  nonneg a := by exact_mod_cast m.nonneg a
  sum_one := by rw [← Rat.cast_sum, m.sum_one, Rat.cast_one]

/-- Weights of the cast distribution. Source: none: infrastructure. Kind: L -/
@[simp] theorem castDistr_w {α : Type} [Fintype α] (m : FinDistr ℚ α) (a : α) :
    (castDistr m).w a = (m.w a : ℝ) := rfl

/-- **Base change of a tree** `ℚ → ℝ`, structural (the mandate's `Tree.castR`): payoffs and
chance weights cast, points, actions and worlds unchanged.
Source: mandate §3.1
Kind: D -/
def castTree : Tree Ω ι acts ℚ → Tree Ω ι acts ℝ
  | .leaf ω r => .leaf ω (r : ℝ)
  | .chance n β child => .chance n (castDistr β) fun i => castTree (child i)
  | .decision d child => .decision d fun a => castTree (child a)

/-- **Base change of a procedure** `ℚ → ℝ` (the mandate's `Proc.castR`).
Source: mandate §3.1
Kind: D -/
def castProc (C : Proc ι acts ℚ) : Proc ι acts ℝ := fun d => castDistr (C d)

/-- The leaf of the cast tree corresponding to a base leaf. Source: none: infrastructure. Kind: D -/
def castLeaf : (B : Tree Ω ι acts ℚ) → B.Leaves → (castTree B).Leaves
  | .leaf _ _, _ => ()
  | .chance _ _ child, ⟨i, ℓ⟩ => ⟨i, castLeaf (child i) ℓ⟩
  | .decision _ child, ⟨a, ℓ⟩ => ⟨a, castLeaf (child a) ℓ⟩

/-- The base leaf of a cast leaf. Source: none: infrastructure. Kind: D -/
def uncastLeaf : (B : Tree Ω ι acts ℚ) → (castTree B).Leaves → B.Leaves
  | .leaf _ _, _ => ()
  | .chance _ _ child, ⟨i, ℓ⟩ => ⟨i, uncastLeaf (child i) ℓ⟩
  | .decision _ child, ⟨a, ℓ⟩ => ⟨a, uncastLeaf (child a) ℓ⟩

/-- `uncastLeaf ∘ castLeaf = id`. Source: none: infrastructure. Kind: L -/
theorem uncastLeaf_castLeaf : ∀ (B : Tree Ω ι acts ℚ) (ℓ : B.Leaves),
    uncastLeaf B (castLeaf B ℓ) = ℓ
  | .leaf _ _, _ => rfl
  | .chance _ _ child, ⟨i, ℓ⟩ => by
      simp only [castLeaf, uncastLeaf, uncastLeaf_castLeaf (child i) ℓ]
  | .decision _ child, ⟨a, ℓ⟩ => by
      simp only [castLeaf, uncastLeaf, uncastLeaf_castLeaf (child a) ℓ]

/-- `castLeaf ∘ uncastLeaf = id`. Source: none: infrastructure. Kind: L -/
theorem castLeaf_uncastLeaf : ∀ (B : Tree Ω ι acts ℚ) (ℓ : (castTree B).Leaves),
    castLeaf B (uncastLeaf B ℓ) = ℓ
  | .leaf _ _, _ => rfl
  | .chance _ _ child, ⟨i, ℓ⟩ => by
      simp only [castLeaf, uncastLeaf, castLeaf_uncastLeaf (child i) ℓ]
  | .decision _ child, ⟨a, ℓ⟩ => by
      simp only [castLeaf, uncastLeaf, castLeaf_uncastLeaf (child a) ℓ]

/-- **The leaves of the cast tree are the base leaves.** Source: none: infrastructure. Kind: D -/
def castLeafEquiv (B : Tree Ω ι acts ℚ) : B.Leaves ≃ (castTree B).Leaves where
  toFun := castLeaf B
  invFun := uncastLeaf B
  left_inv := uncastLeaf_castLeaf B
  right_inv := castLeaf_uncastLeaf B

/-! ### Transport of the run-level quantities -/

/-- `leafLaw` transports along the cast. Source: mandate §3.1 (`leafLaw_castR`). Kind: L -/
theorem leafLaw_cast (C : Proc ι acts ℚ) : ∀ (B : Tree Ω ι acts ℚ) (ℓ : B.Leaves),
    leafLaw (castProc C) (castTree B) (castLeaf B ℓ) = ((leafLaw C B ℓ : ℚ) : ℝ)
  | .leaf _ _, _ => by simp [castTree, castLeaf, leafLaw]
  | .chance _ β child, ⟨i, ℓ⟩ => by
      simp only [castTree, castLeaf, leafLaw_chance, castDistr_w, leafLaw_cast C (child i) ℓ]
      push_cast; ring
  | .decision d child, ⟨a, ℓ⟩ => by
      simp only [castTree, castLeaf, leafLaw_decision, castProc, castDistr_w,
        leafLaw_cast C (child a) ℓ]
      push_cast; ring

/-- `world` is unchanged by the cast. Source: none: infrastructure. Kind: L -/
theorem world_cast : ∀ (B : Tree Ω ι acts ℚ) (ℓ : B.Leaves),
    world (castTree B) (castLeaf B ℓ) = world B ℓ
  | .leaf _ _, _ => rfl
  | .chance _ _ child, ⟨i, ℓ⟩ => by
      simp only [castTree, castLeaf, world_chance, world_cast (child i) ℓ]
  | .decision _ child, ⟨a, ℓ⟩ => by
      simp only [castTree, castLeaf, world_decision, world_cast (child a) ℓ]

/-- `payoff` transports along the cast. Source: none: infrastructure. Kind: L -/
theorem payoff_cast : ∀ (B : Tree Ω ι acts ℚ) (ℓ : B.Leaves),
    payoff (castTree B) (castLeaf B ℓ) = ((payoff B ℓ : ℚ) : ℝ)
  | .leaf _ _, _ => rfl
  | .chance _ _ child, ⟨i, ℓ⟩ => by
      simp only [castTree, castLeaf, payoff_chance, payoff_cast (child i) ℓ]
  | .decision _ child, ⟨a, ℓ⟩ => by
      simp only [castTree, castLeaf, payoff_decision, payoff_cast (child a) ℓ]

/-- `chanceWeight` transports along the cast. Source: none: infrastructure. Kind: L -/
theorem chanceWeight_cast : ∀ (B : Tree Ω ι acts ℚ) (ℓ : B.Leaves),
    chanceWeight (castTree B) (castLeaf B ℓ) = ((chanceWeight B ℓ : ℚ) : ℝ)
  | .leaf _ _, _ => by simp [castTree, castLeaf, chanceWeight]
  | .chance _ β child, ⟨i, ℓ⟩ => by
      simp only [castTree, castLeaf, chanceWeight_chance, castDistr_w,
        chanceWeight_cast (child i) ℓ]
      push_cast; ring
  | .decision _ child, ⟨a, ℓ⟩ => by
      simp only [castTree, castLeaf, chanceWeight_decision, chanceWeight_cast (child a) ℓ]

variable [Fintype Ω] [DecidableEq Ω]

/-- **`ν` transports along the cast**: `ν_{C^ℝ, B^ℝ}(X) = ↑ν_{C,B}(X)`.
Source: mandate §3.1 (`nu_castR`). Kind: L -/
theorem nu_cast (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (X : Finset Ω) :
    nu (castProc C) (castTree B) X = ((nu C B X : ℚ) : ℝ) := by
  rw [nu_eq_sum, nu_eq_sum, Rat.cast_sum, ← Equiv.sum_comp (castLeafEquiv B)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [castLeafEquiv, Equiv.coe_fn_mk, world_cast, leafLaw_cast]
  split_ifs <;> simp

/-- **`paySum` transports along the cast.** Source: mandate §3.1. Kind: L -/
theorem paySum_cast (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (X : Finset Ω) :
    paySum (castProc C) (castTree B) X = ((paySum C B X : ℚ) : ℝ) := by
  rw [paySum_eq_sum_ite, paySum_eq_sum_ite, Rat.cast_sum, ← Equiv.sum_comp (castLeafEquiv B)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [castLeafEquiv, Equiv.coe_fn_mk, world_cast, leafLaw_cast, payoff_cast]
  split_ifs <;> simp

/-- **`value` transports along the cast.** Source: mandate §3.1 (`value_castR`). Kind: L -/
theorem value_cast (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) :
    value (castProc C) (castTree B) = ((value C B : ℚ) : ℝ) := by
  unfold value
  rw [Rat.cast_sum, ← Equiv.sum_comp (castLeafEquiv B)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [castLeafEquiv, Equiv.coe_fn_mk, leafLaw_cast, payoff_cast]
  push_cast; ring

/-- **`condExp` transports along the cast.** Source: mandate §3.1 (`condExp_castR`). Kind: L -/
theorem condExp_cast (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (X : Finset Ω) :
    condExp (castProc C) (castTree B) X = ((condExp C B X : ℚ) : ℝ) := by
  unfold condExp
  rw [paySum_cast, nu_cast, Rat.cast_div]

/-! ### T7(e): the `ℝ`-cast miniature -/

/-- **The miniature over `ℝ`, as the cast of the catalogue tree** (never re-defined by hand).
Source: [[decision-problems-v2]] Remark 4.3; mandate §3.1, T7(e)
Kind: D -/
def miniR : Tree MiniW Unit (fun _ => Act2) ℝ := castTree miniature

/-- The cast miniature, written out: what `castTree miniature` computes to (the computations
below are done on this form, which is definitionally `miniR`; nothing is re-defined by hand —
`miniR_eq` is `rfl`). Source: none: infrastructure. Kind: D -/
def miniRx : Tree MiniW Unit (fun _ => Act2) ℝ :=
  .decision () fun s => .decision () fun l => .leaf (s, l) ((miniPay s l : ℚ) : ℝ)

/-- The cast miniature unfolded (definitional). Source: none: infrastructure. Kind: L -/
theorem miniR_eq : miniR = miniRx := rfl

/-- Sums over the leaves of the cast miniature as a double sum. Source: none: infrastructure.
Kind: L -/
theorem miniRx_sum {M : Type} [AddCommMonoid M] (f : miniRx.Leaves → M) :
    ∑ ℓ, f ℓ = ∑ s : Act2, ∑ l : Act2, f ⟨s, l, ()⟩ := by
  unfold miniRx at f ⊢
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun l _ => ?_
  show ∑ ℓ : Unit, f ⟨s, ⟨l, ℓ⟩⟩ = f ⟨s, ⟨l, ()⟩⟩
  simp

/-- The miniature's action events are disjoint. Source: none: infrastructure. Kind: L -/
theorem mini_disjointActEv : DisjointActEv miniActEv () := by
  intro a b hab
  rw [Finset.disjoint_left]
  intro w hw hw'
  simp only [miniActEv, Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
  exact hab (hw.symm.trans hw')

/-- **F3′ holds structurally on the cast miniature**: the live nodes `some ⟨s, none⟩` are
node-action-veridical, the predictor node `none` is not (it draws the sample while the world
records the live act), so every leaf passes exactly one node-action-veridical `d`-node;
`O_d = ⊤` makes subtree-veridicality trivial. The point is nested (`count = 2`), so the
correspondence of T7(d) is not a recorded point's constant face.
Source: [[decision-problems-v2]] Remark 4.3; `dp-calibration`'s `miniature_not_recordsFor`;
mandate T7(e)
Kind: P
Fidelity: exact -/
theorem miniRx_actRecordingStruct : ActRecordingStruct miniObs miniActEv miniRx () := by
  refine ⟨fun _ _ _ ℓ _ => Finset.mem_univ _, fun ℓ hcw _ => ?_⟩
  obtain ⟨s, l, ⟨⟩⟩ := ℓ
  refine ⟨some ⟨s, none⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_dNodesOn]
    exact ⟨rfl, by simp [miniRx, edgeOf]⟩
  · intro ℓ' a he
    obtain ⟨s', l', ⟨⟩⟩ := ℓ'
    by_cases hs : s' = s
    · subst hs
      simp [miniRx] at he
      subst he
      simp [miniRx, miniActEv]
    · simp [miniRx, hs] at he
  · rintro q ⟨hq, hnav⟩
    rw [mem_dNodesOn] at hq
    obtain ⟨-, hsome⟩ := hq
    rcases q with _ | ⟨s', q'⟩
    · exfalso
      have h1 := hnav ⟨s, ⟨Act2.a, ()⟩⟩ s (by simp [miniRx])
      have h2 := hnav ⟨s, ⟨Act2.b, ()⟩⟩ s (by simp [miniRx])
      simp [miniRx, miniActEv] at h1 h2
      cases s <;> simp_all
    · rcases q' with _ | ⟨a', q''⟩
      · by_cases hs : s = s'
        · subst hs; rfl
        · simp [miniRx, hs] at hsome
      · exact q''.elim

/-- `miniRx_actRecordingStruct` read on `miniR = castTree miniature` (definitional).
Source: mandate T7(e). Kind: L -/
theorem miniR_actRecordingStruct : ActRecordingStruct miniObs miniActEv miniR () :=
  miniRx_actRecordingStruct

/-- The standing hypothesis on the cast miniature: `ν(O_d) = 1 > 0` at every deviation.
Source: C2-7's standing hypothesis; mandate T7(e). Kind: L -/
theorem miniR_hStand (C' : Proc Unit (fun _ => Act2) ℝ) (m : FinDistr ℝ Act2) :
    0 < nu (C'.deviate () m) miniR (miniObs ()) := by
  rw [miniObs, nu_univ]; exact one_pos

/-- `Q_a(C') = 2·C'(d)(b)` on the cast miniature (the one-draw-erased weight of a live-`a` leaf is
the predictor's draw weight). Source: none: infrastructure. Kind: L -/
theorem miniR_qSum_a (C' : Proc Unit (fun _ => Act2) ℝ) :
    qSum C' () .a miniR (miniActEv () .a ∩ miniObs ()) = 2 * (C' ()).w .b := by
  rw [miniR_eq]
  unfold qSum reducedWeight worldEv
  rw [Finset.sum_filter, miniRx_sum]
  simp [Act2.sum_univ, miniRx, miniActEv, miniObs, miniPay, List.erase_cons]
  ring

/-- `Q_b(C') = C'(d)(a)` on the cast miniature. Source: none: infrastructure. Kind: L -/
theorem miniR_qSum_b (C' : Proc Unit (fun _ => Act2) ℝ) :
    qSum C' () .b miniR (miniActEv () .b ∩ miniObs ()) = (C' ()).w .a := by
  rw [miniR_eq]
  unfold qSum reducedWeight worldEv
  rw [Finset.sum_filter, miniRx_sum]
  simp [Act2.sum_univ, miniRx, miniActEv, miniObs, miniPay, List.erase_cons]

/-- **`r3Val m a = 2·m(b)` on the cast miniature at every `ℝ`-label** (boundary included).
Source: `calibration.md` CA-13′ (`2(1−q)`); mandate T7(e)
Kind: P
Fidelity: exact -/
theorem miniR_r3Val_a (C' : Proc Unit (fun _ => Act2) ℝ) (m : FinDistr ℝ Act2) :
    r3Val miniObs miniActEv C' miniR () m .a = 2 * m.w .b := by
  rw [r3Val_eq_qSum_div miniObs miniActEv miniR_actRecordingStruct mini_disjointActEv C' m .a
    (miniR_hStand C' m)]
  rw [miniObs, nu_univ, div_one, ← miniObs, miniR_qSum_a, Proc.deviate_same]

/-- **`r3Val m b = m(a)` on the cast miniature at every `ℝ`-label.**
Source: `calibration.md` CA-13′ (`q`); mandate T7(e)
Kind: P
Fidelity: exact -/
theorem miniR_r3Val_b (C' : Proc Unit (fun _ => Act2) ℝ) (m : FinDistr ℝ Act2) :
    r3Val miniObs miniActEv C' miniR () m .b = m.w .a := by
  rw [r3Val_eq_qSum_div miniObs miniActEv miniR_actRecordingStruct mini_disjointActEv C' m .b
    (miniR_hStand C' m)]
  rw [miniObs, nu_univ, div_one, ← miniObs, miniR_qSum_b, Proc.deviate_same]

/-- Both values in one case split. Source: none: infrastructure. Kind: L -/
theorem miniR_r3Val (C' : Proc Unit (fun _ => Act2) ℝ) (m : FinDistr ℝ Act2) (a : Act2) :
    r3Val miniObs miniActEv C' miniR () m a = if a = .a then 2 * m.w .b else m.w .a := by
  cases a <;> simp [miniR_r3Val_a, miniR_r3Val_b]

/-- **The `ℝ`-values are the casts of `dp-calibration`'s `limitVal_mini`**: at the cast of the
label `(q, 1 − q)`, `r3Val = (↑(2(1−q)), ↑q)`.
Source: mandate T7(e) ("values `2(1 − m.w a)`, `m.w a` (cast of `limitVal_mini`)")
Kind: L
Hyps: (a) `0 ≤ q ≤ 1` -/
theorem miniR_r3Val_cast_limitVal (C' : Proc Unit (fun _ => Act2) ℝ) (q : ℚ) (h0 : 0 ≤ q)
    (h1 : q ≤ 1) :
    r3Val miniObs miniActEv C' miniR () (castDistr (FinDistr.act2 q h0 h1)) .a =
        ((limitVal (procQ q h0 h1) miniature (miniActEv () .a ∩ miniObs ()) : ℚ) : ℝ) ∧
      r3Val miniObs miniActEv C' miniR () (castDistr (FinDistr.act2 q h0 h1)) .b =
        ((limitVal (procQ q h0 h1) miniature (miniActEv () .b ∩ miniObs ()) : ℚ) : ℝ) := by
  obtain ⟨ha, hb⟩ := limitVal_mini q h0 h1
  rw [ha, hb, miniR_r3Val_a, miniR_r3Val_b]
  simp only [castDistr_w, FinDistr.act2_a, FinDistr.act2_b]
  refine ⟨?_, ?_⟩
  · push_cast; ring
  · push_cast

/-- **The best-response correspondence moves**: `a` is strictly preferred iff `m(a) < 2/3`
(so the face is `{δ_a}` below `2/3`, `{δ_b}` above, everything at `2/3`) — the witness
exercises T7(b)'s continuity, not a constant face.
Source: mandate T7(e) ("the correspondence flips at `2/3`")
Kind: P
Fidelity: exact -/
theorem miniR_br_flips (C' : Proc Unit (fun _ => Act2) ℝ) (m : FinDistr ℝ Act2) :
    r3Val miniObs miniActEv C' miniR () m .b < r3Val miniObs miniActEv C' miniR () m .a ↔
      m.w .a < 2 / 3 := by
  have hsum := m.sum_one
  rw [Act2.sum_univ] at hsum
  rw [miniR_r3Val_a, miniR_r3Val_b]
  constructor <;> intro h <;> linarith

/-- **`MsrAtD4` on the cast miniature holds at `C[d ↦ m]` iff `m(a) = 2/3`** — the `ℝ`-form of
`miniature_msrAtD4_iff`, at every `ℝ`-label.
Source: `calibration.md` CA-13′/CA-14′ ("D4 = {2/3}"); mandate T7(e), T9(a)
Kind: P
Fidelity: exact -/
theorem miniR_msrAtD4_iff (C' : Proc Unit (fun _ => Act2) ℝ) (m : FinDistr ℝ Act2) :
    MsrAtD4 miniObs miniActEv (C'.deviate () m) miniR () ↔ m.w .a = 2 / 3 := by
  rw [msrAtD4_deviate_iff]
  have hsum := m.sum_one
  rw [Act2.sum_univ] at hsum
  have ha := m.nonneg .a
  have hb := m.nonneg .b
  simp only [brSet, Set.mem_setOf_eq, miniR_r3Val]
  constructor
  · intro h
    by_cases hqa : 0 < m.w .a
    · have h1 := h .a hqa .b
      simp only [if_true, reduceCtorEq, if_false] at h1
      by_cases hqb : 0 < m.w .b
      · have h2 := h .b hqb .a
        simp only [if_true, reduceCtorEq, if_false] at h2
        linarith
      · have : m.w .b = 0 := le_antisymm (not_lt.mp hqb) hb
        exfalso; linarith
    · have : m.w .a = 0 := le_antisymm (not_lt.mp hqa) ha
      have h2 := h .b (by linarith) .a
      simp only [if_true, reduceCtorEq, if_false] at h2
      exfalso; linarith
  · intro hq a _ b
    cases a <;> cases b <;> simp <;> linarith

/-- **T7(e): the witness for `msrAtD4_exists`** — on the `ℝ`-cast miniature the hypothesis
package of T7(d) is inhabited (`miniR_actRecordingStruct`, `mini_disjointActEv`, `miniR_hStand`),
Kakutani delivers a label `m` with `MsrAtD4 (C[d ↦ m])`, and that label is forced to be
`m(a) = 2/3` by `miniR_msrAtD4_iff`. Grade N+: nested tree, the correspondence flips at `2/3`.
Source: `repair/C2.md` C2-7; `calibration.md` CA-14′; mandate T7(e)
Kind: N+
Fidelity: exact
Hyps: (a) none beyond the tree -/
theorem miniR_msrAtD4_exists_witness (C' : Proc Unit (fun _ => Act2) ℝ) :
    ∃ m : FinDistr ℝ Act2, MsrAtD4 miniObs miniActEv (C'.deviate () m) miniR () ∧ m.w .a = 2 / 3 := by
  obtain ⟨m, hm⟩ := msrAtD4_exists miniObs miniActEv C' () miniR miniR_actRecordingStruct
    mini_disjointActEv (miniR_hStand C')
  exact ⟨m, hm, (miniR_msrAtD4_iff C' m).mp hm⟩

end Cleanroom.Decision.DpDutchBook

import Cleanroom.Decision.DpFairnessReloc

/-!
# Audit round 3 (fidelity) probe: `Fair_{≈val}` admits *non-degenerate* nesting

Not imported by the library. Checks the claim in the ledger row of `degen_fairValEq` and in
findings F13 that the payoff-degenerate tree `degen` (every value `0`) is "the best available"
witness for EQ-4's `≈_val` clause because "a non-degenerate nested tree is rejected by it
whenever the nested point changes the value".

`vnTop` refutes that: one point `d` at three nodes, top `a → vnA`, `b → vnBot`; `vnA` is
`a → ½(0, 2)-coin`, `b → 0`; `vnBot` is `a → 1`, `b → 0`. Every fiber member is worth
`C(d)(a)` under every `C` — the value *varies* with the procedure and the payoffs are `0, 1, 2` —
so `vnTop` is nested and `Fair_{≈val}`, while it is **not** law-fair (under `d ↦ a` the laws
`½δ₀ + ½δ₂` and `δ₁` differ). This is the witness EQ-4's clause needs to be distinct from the
`≈_law` clause: `degen` is also law-fair (all leaves `(( ), 0)`), so it only witnesses
law-spurious nesting.

`sp2` (top `a, b → vnBot`) is the same for the `≈_law` clause: a law-spurious nested tree whose
value `C(d)(a)` varies, replacing the constant-payoff `spur`.
-/

namespace Cleanroom.Decision.DpFairnessReloc.AuditR3

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpFairnessReloc
open Finset

/-- Bottom: `a → 1`, `b → 0`. -/
def vnBot : Tree Unit Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => .leaf () 1
    | .b => .leaf () 0

/-- A fair coin over payoffs `0` and `2` (worth `1`, law `½δ₀ + ½δ₂`). -/
def vnCoin : Tree Unit Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair ![.leaf () 0, .leaf () 2]

/-- The top's `a`-child: `a → vnCoin`, `b → 0` (same value function as `vnBot`, different law). -/
def vnA : Tree Unit Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => vnCoin
    | .b => .leaf () 0

/-- The nested tree: `a → vnA`, `b → vnBot`. -/
def vnTop : Tree Unit Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => vnA
    | .b => vnBot

theorem vnBot_value (C : Proc Unit (fun _ => Act2) ℚ) : value C vnBot = (C ()).w .a := by
  unfold vnBot
  rw [value_decision, Act2.sum_univ]
  simp only [value_leaf, mul_one, mul_zero, add_zero]

theorem vnA_value (C : Proc Unit (fun _ => Act2) ℚ) : value C vnA = (C ()).w .a := by
  unfold vnA vnCoin
  rw [value_decision, Act2.sum_univ]
  simp only [value_chance, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, value_leaf]
  simp [FinDistr.fair, FinDistr.coin]
  ring

theorem vnTop_value (C : Proc Unit (fun _ => Act2) ℚ) : value C vnTop = (C ()).w .a := by
  unfold vnTop
  rw [value_decision, Act2.sum_univ]
  simp only [vnA_value, vnBot_value]
  have h : (C ()).w .a + (C ()).w .b = 1 := by rw [← Act2.sum_univ]; exact (C ()).sum_one
  rw [show (C ()).w .b = 1 - (C ()).w .a by linarith]
  ring

/-- The value is not constant: `q` under `procQ q`. -/
theorem vnTop_value_procQ (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (procQ q h0 h1) vnTop = q := by
  rw [vnTop_value]; rfl

theorem vnTop_subtree (q : vnTop.DecNode) :
    subtreeAt vnTop q = vnTop ∨ subtreeAt vnTop q = vnA ∨ subtreeAt vnTop q = vnBot := by
  rcases q with _ | ⟨x, q⟩
  · exact Or.inl rfl
  · cases x
    · rcases q with _ | ⟨y, e⟩
      · exact Or.inr (Or.inl rfl)
      · cases y
        · obtain ⟨i, e⟩ := e
          fin_cases i <;> (change Empty at e; exact e.elim)
        · change Empty at e
          exact e.elim
    · rcases q with _ | ⟨y, e⟩
      · exact Or.inr (Or.inr rfl)
      · cases y <;> (change Empty at e; exact e.elim)

/-- **`vnTop` is `Fair_{≈val}`** in the source's own grade (`ValEq`: equal `V_T(C)` for every `C`). -/
theorem vnTop_fairValEq : FairWrt (fun _ => ValEq) vnTop := by
  intro d q _ q' _ C
  rcases vnTop_subtree q with h | h | h <;> rcases vnTop_subtree q' with h' | h' | h' <;>
    rw [h, h'] <;> simp only [vnTop_value, vnA_value, vnBot_value]

/-- `vnTop` is nested (positively: no chance node on the `b, a` path). -/
theorem vnTop_nested : Nested vnTop () := by
  refine ⟨by decide, ⟨.b, ⟨.a, ()⟩⟩, ?_, ?_⟩
  · unfold Positive vnTop vnBot; simp
  · unfold vnTop vnBot; simp

/-- `vnBot`'s law: `C(a) δ_{(( ),1)} + C(b) δ_{(( ),0)}`. -/
theorem contLaw_vnBot (C : Proc Unit (fun _ => Act2) ℚ) :
    contLaw C vnBot =
      (C ()).w .a • Finsupp.single ((), (1 : ℚ)) 1 + (C ()).w .b • Finsupp.single ((), (0 : ℚ)) 1 := by
  unfold vnBot
  rw [contLaw_decision, Act2.sum_univ]
  simp only [contLaw_leaf]

/-- `vnCoin`'s law: `½ δ_{(( ),0)} + ½ δ_{(( ),2)}`. -/
theorem contLaw_vnCoin (C : Proc Unit (fun _ => Act2) ℚ) :
    contLaw C vnCoin =
      (1 / 2 : ℚ) • Finsupp.single ((), (0 : ℚ)) 1 + (1 / 2 : ℚ) • Finsupp.single ((), (2 : ℚ)) 1 := by
  unfold vnCoin
  rw [contLaw_chance, Fin.sum_univ_two]
  norm_num [FinDistr.fair, FinDistr.coin]

/-- `vnA`'s law: `C(a) (½ δ_{(( ),0)} + ½ δ_{(( ),2)}) + C(b) δ_{(( ),0)}`. -/
theorem contLaw_vnA (C : Proc Unit (fun _ => Act2) ℚ) :
    contLaw C vnA =
      (C ()).w .a • ((1 / 2 : ℚ) • Finsupp.single ((), (0 : ℚ)) 1 +
        (1 / 2 : ℚ) • Finsupp.single ((), (2 : ℚ)) 1) +
      (C ()).w .b • Finsupp.single ((), (0 : ℚ)) 1 := by
  unfold vnA
  rw [contLaw_decision, Act2.sum_univ]
  simp only [contLaw_vnCoin, contLaw_leaf]

/-- **`vnTop` is not law-fair**: under `d ↦ a` the fiber members `vnA` and `vnBot` put mass `0`
and `1` on `(( ), 1)`. -/
theorem vnTop_not_lawFair : ¬ LawFair vnTop := by
  intro h
  have key := h () (some ⟨.a, none⟩) (by decide) (some ⟨.b, none⟩) (by decide)
    (procQ 1 (by norm_num) (by norm_num))
  change contLaw _ vnA = contLaw _ vnBot at key
  have := DFunLike.congr_fun key ((), (1 : ℚ))
  rw [contLaw_vnA, contLaw_vnBot] at this
  simp [procQ, Finsupp.single_apply] at this

/-- **The `≈_val` clause with a non-degenerate witness**: `vnTop` is nested, `Fair_{≈val}`, not
law-fair, and its value `C(d)(a)` varies with the procedure. So EQ-4's "not by `≈_val`" is
witnessed by a tree the `≈_law` clause does not already cover, and the ledger's "a non-degenerate
nested tree is rejected by `≈_val` whenever the nested point changes the value" is false. -/
theorem valFair_nested_nondegenerate :
    Nested vnTop () ∧ FairWrt (fun _ => ValEq) vnTop ∧ ¬ LawFair vnTop ∧
      ∀ q h0 h1, value (procQ q h0 h1) vnTop = q :=
  ⟨vnTop_nested, vnTop_fairValEq, vnTop_not_lawFair, vnTop_value_procQ⟩

/-! ### The `≈_law` clause with a non-constant witness -/

/-- A spurious `d`-query over two copies of `vnBot`: law-spurious nesting with varying value. -/
def sp2 : Tree Unit Unit (fun _ => Act2) ℚ := .decision () fun _ => vnBot

theorem contLaw_sp2 (C : Proc Unit (fun _ => Act2) ℚ) : contLaw C sp2 = contLaw C vnBot := by
  unfold sp2
  rw [contLaw_decision]
  show ∑ a : Act2, (C ()).w a • contLaw C vnBot = contLaw C vnBot
  rw [← Finset.sum_smul, (C ()).sum_one, one_smul]

theorem sp2_subtree (q : sp2.DecNode) : subtreeAt sp2 q = sp2 ∨ subtreeAt sp2 q = vnBot := by
  rcases q with _ | ⟨x, q⟩
  · exact Or.inl rfl
  · rcases q with _ | ⟨y, e⟩
    · exact Or.inr rfl
    · cases y <;> (change Empty at e; exact e.elim)

theorem sp2_lawFair : LawFair sp2 := by
  intro d q _ q' _ C
  rcases sp2_subtree q with h | h <;> rcases sp2_subtree q' with h' | h' <;>
    rw [h, h'] <;> simp only [contLaw_sp2]

theorem sp2_nested : Nested sp2 () := by
  refine ⟨by decide, ⟨.a, ⟨.a, ()⟩⟩, ?_, ?_⟩
  · unfold Positive sp2 vnBot; simp
  · unfold sp2 vnBot; simp

theorem sp2_value (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : value (procQ q h0 h1) sp2 = q := by
  unfold sp2
  rw [value_decision]
  show ∑ a : Act2, (procQ q h0 h1 ()).w a * value (procQ q h0 h1) vnBot = q
  rw [vnBot_value, ← Finset.sum_mul, (procQ q h0 h1 ()).sum_one, one_mul]
  rfl

/-- **The `≈_law` clause with a non-constant witness**: `sp2` is nested, law-fair, and worth `q`. -/
theorem lawFair_nested_nonconstant :
    Nested sp2 () ∧ LawFair sp2 ∧ ∀ q h0 h1, value (procQ q h0 h1) sp2 = q :=
  ⟨sp2_nested, sp2_lawFair, sp2_value⟩

end Cleanroom.Decision.DpFairnessReloc.AuditR3

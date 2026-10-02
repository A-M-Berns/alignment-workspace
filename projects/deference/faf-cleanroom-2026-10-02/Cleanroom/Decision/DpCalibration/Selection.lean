import Cleanroom.Decision.DpCalibration.Witnesses

/-!
# The selection-forcing tree: Remark 5.2(i)'s missing witness (T15(c))

`S_sel(−20, −20; 10, 5)`: a chance root with three equiprobable branches — a real `d`-node
(`a → realA`, payoff `−20`; `b → realB`, `−20`), a fake-`a` leaf (`10`), a fake-`b` leaf (`5`);
`O_d = ⊤`, action events `{act = a}`, `{act = b}` across real and fake worlds. Under strict
calibration for `procQ q`, both acts are always subjectively possible (the fake worlds carry
mass `⅓`), `V(a) = 10(1−2q)/(1+q)`, `V(b) = (20q−15)/(2−q)`, they tie at `q = 7/11`, and the
`EDT` procedure has **no** strictly-calibrated fixed point (`sel_edt_no_fixed`): at `q ∈ {0,1}`
the argmax is the *other* act, at interior `q ≠ 7/11` it is a pure act `≠ q`, and at the tie
the uniform break returns `½ ≠ 7/11`. The witness v2's Remark 5.2 lacks.
-/

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace Cleanroom.Decision.DpCalibration

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Finset

/-- `S_sel(−20, −20; 10, 5)`, the default parameters.
Source: `calibration.md` line 23 ("default payoffs `(−20,−20;10,5)`"); CA-12′ ("Almost-fairness
is not sufficient")
Kind: D -/
def selTree : Tree SelW Unit (fun _ => Act2) ℚ := selectionForcing (-20) (-20) 10 5

/-- A sum over the leaves of `selTree` as four terms. Source: none: infrastructure. Kind: L -/
theorem sel_sum (f : selTree.Leaves → ℚ) :
    ∑ ℓ, f ℓ = f ⟨0, .a, ()⟩ + f ⟨0, .b, ()⟩ + f ⟨1, ()⟩ + f ⟨2, ()⟩ := by
  unfold selTree selectionForcing at f ⊢
  rw [sum_leaves_chance, Fin.sum_univ_three]
  show (∑ ℓ : (Tree.decision () (fun | .a => .leaf SelW.realA (-20) | .b => .leaf SelW.realB (-20)) :
      Tree SelW Unit (fun _ => Act2) ℚ).Leaves, f ⟨0, ℓ⟩) +
    (∑ ℓ : (Tree.leaf SelW.fakeA 10 : Tree SelW Unit (fun _ => Act2) ℚ).Leaves, f ⟨1, ℓ⟩) +
    (∑ ℓ : (Tree.leaf SelW.fakeB 5 : Tree SelW Unit (fun _ => Act2) ℚ).Leaves, f ⟨2, ℓ⟩) = _
  rw [sum_leaves_decision, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf]

/-- `ν` on `selTree` as an explicit expression. Source: none: infrastructure. Kind: L -/
theorem sel_nu (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset SelW) :
    nu C selTree X =
      (if SelW.realA ∈ X then (1/3 : ℚ) * (C ()).w .a else 0) +
      (if SelW.realB ∈ X then (1/3 : ℚ) * (C ()).w .b else 0) +
      (if SelW.fakeA ∈ X then (1/3 : ℚ) else 0) +
      (if SelW.fakeB ∈ X then (1/3 : ℚ) else 0) := by
  rw [nu_eq_sum, sel_sum]
  unfold selTree selectionForcing
  simp [leafLaw_chance, leafLaw_decision, leafLaw_leaf, world_chance, world_decision, world_leaf,
    FinDistr.third]

/-- `𝔼[r · 1_X]` on `selTree` as an explicit expression. Source: none: infrastructure. Kind: L -/
theorem sel_paySum (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset SelW) :
    paySum C selTree X =
      (if SelW.realA ∈ X then (1/3 : ℚ) * (C ()).w .a * (-20) else 0) +
      (if SelW.realB ∈ X then (1/3 : ℚ) * (C ()).w .b * (-20) else 0) +
      (if SelW.fakeA ∈ X then (1/3 : ℚ) * 10 else 0) +
      (if SelW.fakeB ∈ X then (1/3 : ℚ) * 5 else 0) := by
  rw [paySum_eq_sum_ite, sel_sum]
  unfold selTree selectionForcing
  simp [leafLaw_chance, leafLaw_decision, leafLaw_leaf, world_chance, world_decision, world_leaf,
    payoff_chance, payoff_decision, payoff_leaf, FinDistr.third]

/-- The strict state of `procQ q` on `selTree` (`O = ⊤`).
Source: `calibration.md` CA-12′ ("the strictly calibrated act values")
Kind: D -/
noncomputable def selState (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : State SelW ℚ :=
  calibratedState (procQ q h0 h1) selTree Finset.univ (nu_univ_pos _ _)

/-- `P_s(a) = (1+q)/3`, `P_s(b) = (2−q)/3`: both acts are always subjectively possible.
Source: `calibration.md` CA-12′ ("the fake worlds carry mass, so both actions are in `A_d^+` at
every `q`")
Kind: L -/
theorem selState_pr (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (selState q h0 h1).pr (selActEv () .a) = (1 + q) / 3 ∧
    (selState q h0 h1).pr (selActEv () .b) = (2 - q) / 3 := by
  simp only [selState, calibratedState_pr, Finset.inter_univ, nu_univ, div_one, sel_nu, selActEv,
    procQ, FinDistr.act2_a, FinDistr.act2_b]
  constructor <;> simp <;> ring

/-- **`V_s(a) = (10 − 20q)/(1+q)`, `V_s(b) = (20q − 15)/(2−q)`**, derived from the tree.
Source: `calibration.md` CA-12′ (`V_{s_d}(a) = 10(1−2q)/(1+q)`, `V_{s_d}(b) = (20q−15)/(2−q)`)
Kind: P
Fidelity: exact
Hyps: none (`0 ≤ q ≤ 1` keeps both denominators positive) -/
theorem selState_V (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (selState q h0 h1).V (selActEv () .a) = (10 - 20 * q) / (1 + q) ∧
    (selState q h0 h1).V (selActEv () .b) = (20 * q - 15) / (2 - q) := by
  have hnA : nu (procQ q h0 h1) selTree (selActEv () .a) = (1 + q) / 3 := by
    rw [sel_nu]; simp [selActEv, procQ]; ring
  have hpA : paySum (procQ q h0 h1) selTree (selActEv () .a) = (10 - 20 * q) / 3 := by
    rw [sel_paySum]; simp [selActEv, procQ]; ring
  have hnB : nu (procQ q h0 h1) selTree (selActEv () .b) = (2 - q) / 3 := by
    rw [sel_nu]; simp [selActEv, procQ]; ring
  have hpB : paySum (procQ q h0 h1) selTree (selActEv () .b) = (20 * q - 15) / 3 := by
    rw [sel_paySum]; simp [selActEv, procQ]; ring
  simp only [selState, calibratedState_V, Finset.inter_univ, hnA, hpA, hnB, hpB]
  have h2 : (0 : ℚ) < 2 - q := by linarith
  have h3 : (0 : ℚ) < 1 + q := by linarith
  constructor
  · rw [div_eq_div_iff (by linarith) h3.ne']; ring
  · rw [div_eq_div_iff (by linarith) h2.ne']; ring

/-- `A_d^+ = A_d` on `selTree` at every `q`. Source: `calibration.md` CA-12′. Kind: L -/
theorem sel_aPlus (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    APlus (fun _ => selState q h0 h1) selActEv () = Finset.univ := by
  obtain ⟨ha, hb⟩ := selState_pr q h0 h1
  ext a
  cases a <;> simp [APlus, ha, hb] <;> linarith

/-- The `EDT` comparison on `selTree`: `V(b) ≤ V(a) ↔ q ≤ 7/11` and `V(a) ≤ V(b) ↔ 7/11 ≤ q`.
Source: `calibration.md` CA-12′ ("the tie at `7/11`")
Kind: L -/
theorem sel_compare (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    ((selState q h0 h1).V (selActEv () .b) ≤ (selState q h0 h1).V (selActEv () .a) ↔ q ≤ 7 / 11) ∧
    ((selState q h0 h1).V (selActEv () .a) ≤ (selState q h0 h1).V (selActEv () .b) ↔ 7 / 11 ≤ q) := by
  obtain ⟨hVa, hVb⟩ := selState_V q h0 h1
  rw [hVa, hVb]
  have h2 : (0 : ℚ) < 2 - q := by linarith
  have h3 : (0 : ℚ) < 1 + q := by linarith
  constructor
  · rw [div_le_div_iff₀ h2 h3]; constructor <;> intro h <;> nlinarith
  · rw [div_le_div_iff₀ h3 h2]; constructor <;> intro h <;> nlinarith

/-- **The `EDT` procedure has no strictly-calibrated fixed point on `selTree`** (Remark 5.2(i)'s
missing witness): for every `q ∈ [0, 1]`, `EDT(selState q) ≠ procQ q`.
Source: [[decision-problems-v2]] Remark 5.2(i) ("the fixed-point existence failures"); mandate
T15(c) ("the witness v2 lacks"); `calibration.md` CA-12′
Kind: P
Fidelity: exact
Hyps: (a) `0 ≤ q ≤ 1` -/
theorem sel_edt_no_fixed (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    edtProc (fun _ => selState q h0 h1) selActEv () ≠ procQ q h0 h1 () := by
  intro h
  have hw := congrArg (fun p => p.w Act2.a) h
  simp only [procQ, FinDistr.act2_a] at hw
  obtain ⟨hcmp1, hcmp2⟩ := sel_compare q h0 h1
  have hA := sel_aPlus q h0 h1
  rcases lt_trichotomy q (7/11) with hlt | heq | hgt
  · -- argmax = {a}: EDT plays `a` with weight 1, but `q < 7/11 < 1`
    have hM : argmaxPlus (fun _ => selState q h0 h1) selActEv () = {.a} := by
      ext a
      rw [mem_argmaxPlus, hA, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h⟩
        cases a
        · rfl
        · have := h .a (Finset.mem_univ _)
          exact absurd (hcmp2.mp this) (by linarith)
      · rintro rfl
        refine ⟨Finset.mem_univ _, fun b _ => ?_⟩
        cases b
        · exact le_rfl
        · exact hcmp1.mpr hlt.le
    rw [edtProc, dif_pos ⟨.a, by rw [hM]; simp⟩] at hw
    simp [uniformOn_w, hM] at hw
    linarith
  · -- the tie: EDT returns ½ ≠ 7/11
    subst heq
    have hM : argmaxPlus (fun _ => selState (7/11) h0 h1) selActEv () = Finset.univ := by
      ext a
      rw [mem_argmaxPlus, hA]
      simp only [Finset.mem_univ, true_and, iff_true]
      intro b _
      cases a <;> cases b
      · exact le_rfl
      · exact hcmp1.mpr le_rfl
      · exact hcmp2.mpr le_rfl
      · exact le_rfl
    rw [edtProc, dif_pos ⟨.a, by rw [hM]; simp⟩] at hw
    simp [uniformOn_w, hM, Act2.univ_eq] at hw
    norm_num at hw
  · -- argmax = {b}: EDT plays `a` with weight 0, but `q > 7/11 > 0`
    have hM : argmaxPlus (fun _ => selState q h0 h1) selActEv () = {.b} := by
      ext a
      rw [mem_argmaxPlus, hA, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h⟩
        cases a
        · have := h .b (Finset.mem_univ _)
          exact absurd (hcmp1.mp this) (by linarith)
        · rfl
      · rintro rfl
        refine ⟨Finset.mem_univ _, fun b _ => ?_⟩
        cases b
        · exact hcmp2.mpr hgt.le
        · exact le_rfl
    rw [edtProc, dif_pos ⟨.b, by rw [hM]; simp⟩] at hw
    simp [uniformOn_w, hM] at hw
    linarith

end Cleanroom.Decision.DpCalibration

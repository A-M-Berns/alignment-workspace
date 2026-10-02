import Cleanroom.Uea.UeaSelfGame.Tables

/-!
# Mixed-policy objects on `Fin 2`- and `Fin 3`-indexed games as explicit sums

`Ucoord`, `Umix` and `pa`/`pva` on `S = Fin 2` and `S = Fin 3` as nested sums over the entries, for the
mixed instance files (`Floored.lean`, `Witness8801.lean`, `NoPureFP.lean`).

Package: `Cleanroom.Uea.UeaSelfGame` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSelfGame

open Finset
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem prod_erase_fin2_0 (f : Fin 2 → ℝ) : ∏ t ∈ (Finset.univ : Finset (Fin 2)).erase 0, f t = f 1 := by
  have : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  rw [this, Finset.prod_singleton]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem prod_erase_fin2_1 (f : Fin 2 → ℝ) : ∏ t ∈ (Finset.univ : Finset (Fin 2)).erase 1, f t = f 0 := by
  have : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  rw [this, Finset.prod_singleton]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem prod_erase_fin3_0 (f : Fin 3 → ℝ) :
    ∏ t ∈ (Finset.univ : Finset (Fin 3)).erase 0, f t = f 1 * f 2 := by
  have : (Finset.univ : Finset (Fin 3)).erase 0 = {1, 2} := by decide
  rw [this, Finset.prod_pair (by decide)]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem prod_erase_fin3_1 (f : Fin 3 → ℝ) :
    ∏ t ∈ (Finset.univ : Finset (Fin 3)).erase 1, f t = f 0 * f 2 := by
  have : (Finset.univ : Finset (Fin 3)).erase 1 = {0, 2} := by decide
  rw [this, Finset.prod_pair (by decide)]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem prod_erase_fin3_2 (f : Fin 3 → ℝ) :
    ∏ t ∈ (Finset.univ : Finset (Fin 3)).erase 2, f t = f 0 * f 1 := by
  have : (Finset.univ : Finset (Fin 3)).erase 2 = {0, 1} := by decide
  rw [this, Finset.prod_pair (by decide)]

namespace Game

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- `U_a(σ)` at `s₀` on `Fin 2`: `∑_y σ₁(y) U(a, y)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Ucoord_fin2_0 (G : Game (Fin 2) A) (σ : Fin 2 → A → ℝ) (a : A) :
    G.Ucoord σ 0 a = ∑ y, σ 1 y * G.U ![a, y] := by
  unfold Ucoord
  rw [sum_fin2_arrow]
  simp only [prod_erase_fin2_0, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ a, if_pos (Finset.mem_univ _)]

/-- `U_a(σ)` at `s₁` on `Fin 2`: `∑_x σ₀(x) U(x, a)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Ucoord_fin2_1 (G : Game (Fin 2) A) (σ : Fin 2 → A → ℝ) (a : A) :
    G.Ucoord σ 1 a = ∑ x, σ 0 x * G.U ![x, a] := by
  unfold Ucoord
  rw [sum_fin2_arrow]
  simp only [prod_erase_fin2_1, Matrix.cons_val_zero, Matrix.cons_val_one]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ a, if_pos (Finset.mem_univ _)]

omit [DecidableEq A] in
/-- `U(σ)` on `Fin 2`: `∑_{x,y} σ₀(x) σ₁(y) U(x, y)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Umix_fin2 (G : Game (Fin 2) A) (σ : Fin 2 → A → ℝ) :
    G.Umix σ = ∑ x, ∑ y, σ 0 x * σ 1 y * G.U ![x, y] := by
  unfold Umix prodW
  rw [sum_fin2_arrow]
  simp [Fin.prod_univ_two]

/-- `U_a(σ)` at `s₀` on `Fin 3`: `∑_{y,z} σ₁(y) σ₂(z) U(a, y, z)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Ucoord_fin3_0 (G : Game (Fin 3) A) (σ : Fin 3 → A → ℝ) (a : A) :
    G.Ucoord σ 0 a = ∑ y, ∑ z, σ 1 y * σ 2 z * G.U ![a, y, z] := by
  unfold Ucoord
  rw [sum_fin3_arrow]
  simp only [prod_erase_fin3_0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ a, if_pos (Finset.mem_univ _)]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Ucoord_fin3_1 (G : Game (Fin 3) A) (σ : Fin 3 → A → ℝ) (a : A) :
    G.Ucoord σ 1 a = ∑ x, ∑ z, σ 0 x * σ 2 z * G.U ![x, a, z] := by
  unfold Ucoord
  rw [sum_fin3_arrow]
  simp only [prod_erase_fin3_1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ a, if_pos (Finset.mem_univ _)]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Ucoord_fin3_2 (G : Game (Fin 3) A) (σ : Fin 3 → A → ℝ) (a : A) :
    G.Ucoord σ 2 a = ∑ x, ∑ y, σ 0 x * σ 1 y * G.U ![x, y, a] := by
  unfold Ucoord
  rw [sum_fin3_arrow]
  simp only [prod_erase_fin3_2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ a, if_pos (Finset.mem_univ _)]

omit [DecidableEq A] in
/-- `U(σ)` on `Fin 3`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Umix_fin3 (G : Game (Fin 3) A) (σ : Fin 3 → A → ℝ) :
    G.Umix σ = ∑ x, ∑ y, ∑ z, σ 0 x * σ 1 y * σ 2 z * G.U ![x, y, z] := by
  unfold Umix prodW
  rw [sum_fin3_arrow]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  ring

end Game

end Cleanroom.Uea.UeaSelfGame

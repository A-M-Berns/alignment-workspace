import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Prod

/-!
# Sums over `Fin 2 → A` and `Fin 3 → A`

Infrastructure for the instance files: a sum over the policies `Fin n → A` (`n = 2, 3`) is the nested sum
over the entries, so that `Fin.sum_univ_two`/`Fin.sum_univ_three` reduce it to finitely many terms and
`simp` with `Matrix.cons_val_*` evaluates each. No `decide` on policies is needed.

Package: `Cleanroom.Uea.UeaSelfGame` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSelfGame

open Finset

variable {M : Type*} [AddCommMonoid M] {A : Type*} [Fintype A]

/-- A sum over `Fin 2 → A` is the nested sum over the two entries.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem sum_fin2_arrow (f : (Fin 2 → A) → M) : ∑ π, f π = ∑ a, ∑ b, f ![a, b] := by
  rw [← (finTwoArrowEquiv A).symm.sum_comp, Fintype.sum_prod_type]
  rfl

/-- A sum over `Fin 3 → A` is the nested sum over the three entries.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem sum_fin3_arrow (f : (Fin 3 → A) → M) : ∑ π, f π = ∑ a, ∑ b, ∑ c, f ![a, b, c] := by
  rw [← (Fin.consEquiv (fun _ : Fin 3 => A)).sum_comp, Fintype.sum_prod_type]
  simp_rw [sum_fin2_arrow]
  rfl

end Cleanroom.Uea.UeaSelfGame

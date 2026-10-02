import Cleanroom.Corrigibility.CorrPowerChannel.Mdp

/-!
Audit r3 (adversarial) probe for `visit` (`Mdp.lean`, T7(b)).

The ledger discloses the visit distributions as `(c)`: "hand-evaluated closed forms of the
unmodelled five-state MDP — no transition kernel in Lean". This file writes the transition kernel
down (at `p = 1`, as a `0/1` matrix `T π` read off `check_turner.py`: `s →keep→ k`, `s →erode→ c1`,
`k → z`, `c1`/`c2` stay or swap, `z → z`) and checks that the four closed forms of `visit` satisfy the
defining recursion of a visit distribution,

  `f(x) = 𝟙[x = s] + γ · ∑_y f(y) · T(y → x)`   for `γ ∈ [0, 1)`,

for **all eight** policies and all five states (`visit_recursion`), and that every row of `T π` is a
probability vector (`T_row_sum`). For `γ < 1` the recursion `f = e_s + γ Tᵀ f` has a unique solution
(`γ Tᵀ` is a contraction in the `ℓ¹` sense), so this pins the closed forms down as *the* visit
distributions of that kernel; the uniqueness step is standard and not formalized here. The `(c)` is
thereby reduced from "hand-evaluated, unchecked" to "checked against the stated kernel".

Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrPowerChannel.AuditR3

open Finset

noncomputable section

/-- The five-state transition matrix at `p = 1`: row `y` is the one-hot vector of the successor of `y`
under `π = (keep?, c1 stays?, c2 stays?)`. States `s = 0`, `k = 1`, `c1 = 2`, `c2 = 3`, `z = 4`. -/
def T (π : Pol) : Fin 5 → Fin 5 → ℝ :=
  ![if π.1 then ![0, 1, 0, 0, 0] else ![0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1],
    if π.2.1 then ![0, 0, 1, 0, 0] else ![0, 0, 0, 1, 0],
    if π.2.2 then ![0, 0, 0, 1, 0] else ![0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1]]

/-- Every row of the kernel is a probability vector. -/
theorem T_row_sum (π : Pol) : ∀ y, ∑ x, T π y x = 1 := by
  rcases π with ⟨k, a, b⟩
  cases k <;> cases a <;> cases b <;>
    simp [Fin.forall_fin_succ, Fin.sum_univ_succ, T]

/-- **The closed forms of `visit` satisfy the visit recursion of the stated kernel**, for every policy
and every state, on `γ ∈ [0, 1)`. -/
theorem visit_recursion (π : Pol) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∀ x, visit π γ x = (![1, 0, 0, 0, 0] : Fin 5 → ℝ) x + γ * ∑ y, visit π γ y * T π y x := by
  have h1 : (1 - γ) ≠ 0 := by linarith
  have h2 : (1 - γ ^ 2) ≠ 0 := by nlinarith
  rcases π with ⟨k, a, b⟩
  cases k <;> cases a <;> cases b <;>
    simp [Fin.forall_fin_succ, Fin.sum_univ_succ, visit, T] <;>
    (repeat' apply And.intro) <;> (try field_simp) <;> ring

end

end Cleanroom.Corrigibility.CorrPowerChannel.AuditR3

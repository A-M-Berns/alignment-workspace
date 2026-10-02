import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic.Linarith

/-!
# Turner's letter-gridworld facts (Target 15)

Turner 2021, "A certain formalization of corrigibility is VNM-incoherent" (ll. 54–125): a
terminal-state reward `R : Letter → ℝ` on the letter states, in the case "reward independent of
corrigibility" (`R blue = R red` built into the carrier: one reward per letter). Allowing
correction to `x` is *an* optimal policy iff `R x ≥ max R` (weak corrigibility); strict
corrigibility (`R x > max R`) is impossible; and an `R`-maximiser is weakly corrigible to every
letter iff `R` is constant (the **Fact**, l. 92).

The findings file records that the title claim ("corrigibility is VNM-incoherent") is this Fact
about state-based terminal rewards on one MDP, and that a utility over `Ω × Θ` (the thesis's) is
outside its scope (corr-core-030). The `1/(n+1)` permutation bound is Target 20 (not done).
-/

namespace Cleanroom.Lit.LitShutdownPrefs

namespace Turner

variable {n : ℕ}

/-- **Weakly corrigible to `x`**: allowing correction to letter `x` is an optimal policy, i.e.
`R x ≥ max_y R y`; with `R blue = R red` built in, the max over the red (incorrigible) letters is
the max over all letters.
Source: Turner 2021 l. 86 ("weakly corrigible … iff `R(C) ≥ max(R(A), R(B), R(C))`"), l. 54
Kind: D
Fidelity: variant: `R blue = R red` is the carrier (case 1 of the post) -/
def WeakCorrigibleTo (R : Fin n → ℝ) (x : Fin n) : Prop := ∀ y, R y ≤ R x

/-- **Strictly corrigible to `x`**: `R x > max_y R y` (the `y = x` term is the red copy of `x`).
Source: Turner 2021 l. 86 ("strictly corrigible … iff this inequality is strict"), l. 90
Kind: D
Fidelity: variant: as above -/
def StrictCorrigibleTo (R : Fin n → ℝ) (x : Fin n) : Prop := ∀ y, R y < R x

/-- **Strict corrigibility is impossible** when the reward cannot see corrigibility: it would need
`R x > … ≥ R x`.
Source: Turner 2021 l. 90 ("strict corrigibility is impossible for any policy")
Kind: L
Fidelity: exact (under the identification) -/
theorem not_strictCorrigibleTo (R : Fin n → ℝ) (x : Fin n) : ¬ StrictCorrigibleTo R x :=
  fun h => lt_irrefl _ (h x)

/-- **The Fact**: an `R`-maximiser is weakly corrigible to every letter iff `R` is constant — and
therefore makes every policy optimal.
Source: Turner 2021 l. 92 ("**Fact:** An `R`-maximizer is weakly corrigible to all of these policies
simultaneously iff `R` is constant"); corr-refs-056, corr-core-030
Kind: L
Fidelity: exact (under the identification)
Hyps: (a) all -/
theorem weakCorrigibleTo_all_iff (R : Fin n → ℝ) :
    (∀ x, WeakCorrigibleTo R x) ↔ ∀ x y, R x = R y := by
  constructor
  · intro h x y
    exact le_antisymm (h y x) (h x y)
  · intro h x y
    exact (h y x).le

/-- Weak corrigibility to some letter is always available (any maximiser of `R`), for `n ≥ 1`.
Source: Turner 2021 l. 86 ("either avoiding or allowing correction can be optimal if `R(A)` is maximal")
Kind: L -/
theorem exists_weakCorrigibleTo (R : Fin (n + 1) → ℝ) : ∃ x, WeakCorrigibleTo R x := by
  obtain ⟨x, -, hx⟩ := Finset.exists_max_image Finset.univ R Finset.univ_nonempty
  exact ⟨x, fun y => hx y (Finset.mem_univ y)⟩

end Turner

end Cleanroom.Lit.LitShutdownPrefs

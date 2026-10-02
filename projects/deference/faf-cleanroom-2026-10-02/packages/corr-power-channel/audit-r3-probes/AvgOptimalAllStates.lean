import Cleanroom.Corrigibility.CorrPowerChannel.Mdp

/-!
Audit r3 (adversarial) probe for `AvgOptimal` (`Mdp.lean`, T7(b)).

`AvgOptimal R π` is Def. 6.11 **at the start state only**: the RSD from `s` maximizes `dᵀR` over
the four RSDs from `s`. Turner's Def. 6.11 asks for optimality at *every* state. Round 1 (fidelity
N3), round 2 (adversarial N7) and round 3 (fidelity N8) each re-derived by hand the docstring's
argument that the existential forms `∃ π, π.1 = keep ∧ AvgOptimal (R) π` coincide with the all-states
ones in this MDP, and left it unformalized. This file formalizes it.

`rsdFrom π x` is the RSD of policy `π` started at state `x` (at `p = 1`, `γ = 1`): from `s` it is
`rsd π`; from `k` and `z` it is `e_z` whatever `π`; from `c1` it is `e_{c1}` if `c1` stays, else
`e_{c2}` if `c2` stays, else the cycle; from `c2` symmetrically. `AvgOptimalAll R π` is Def. 6.11 in
full: `∀ x, ∀ π', rsdFrom π' x ⬝ R ≤ rsdFrom π x ⬝ R`.

* `avgOptimalAll_imp`: all-states optimality implies the library's start-state optimality
  (`rsdFrom π 0 = rsd π` by `rfl`).
* `keep_all_iff`: `(∃ π, π.1 = true ∧ AvgOptimalAll R π) ↔ max (R c1) (R c2) ≤ R z` — the same
  right-hand side as the library's `keep_avgOptimal_iff`; hence `keep_all_iff_start`.
* `erode_all_iff`: `(∃ π, π.1 = false ∧ AvgOptimalAll R π) ↔ R z ≤ max (R c1) (R c2)` — the same
  right-hand side as `erode_avgOptimal_iff`; hence `erode_all_iff_start`.

So `keepOptPerms`/`erodeOptPerms` (and the tie-robust sets) are unchanged if `AvgOptimal` is replaced
by the all-states form, and every orbit count of `Mdp.lean` is Cor. 6.14's count for Def. 6.11 as
stated. The `rsdFrom` vectors from `c1`/`c2`/`k`/`z` are, like `rsd`, written down by hand (they are
the obvious limits: a 1-cycle, or the two-cycle's `(e_{c1} + e_{c2})/2`).

Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrPowerChannel.AuditR3

open Finset

noncomputable section

/-- `e_z`. -/
def ez : Fin 5 → ℝ := ![0, 0, 0, 0, 1]

/-- The RSD from `c1`: stay gives `e_{c1}`; move to a staying `c2` gives `e_{c2}`; otherwise the
two-cycle. -/
def fromC1 (π : Pol) : Fin 5 → ℝ :=
  match π with
  | (_, true, _) => ![0, 0, 1, 0, 0]
  | (_, false, true) => ![0, 0, 0, 1, 0]
  | (_, false, false) => ![0, 0, 1 / 2, 1 / 2, 0]

/-- The RSD from `c2`: stay gives `e_{c2}`; move to a staying `c1` gives `e_{c1}`; otherwise the
two-cycle. -/
def fromC2 (π : Pol) : Fin 5 → ℝ :=
  match π with
  | (_, _, true) => ![0, 0, 0, 1, 0]
  | (_, true, false) => ![0, 0, 1, 0, 0]
  | (_, false, false) => ![0, 0, 1 / 2, 1 / 2, 0]

/-- The RSD of `π` started at each of the five states (`s = 0`, `k = 1`, `c1 = 2`, `c2 = 3`,
`z = 4`). -/
def rsdFrom (π : Pol) : Fin 5 → Fin 5 → ℝ := ![rsd π, ez, fromC1 π, fromC2 π, ez]

/-- From the start state, `rsdFrom` is the library's `rsd`. -/
theorem rsdFrom_zero (π : Pol) : rsdFrom π 0 = rsd π := rfl

/-- **Def. 6.11 in full**: `π` is average-optimal at every state. -/
def AvgOptimalAll (R : Fin 5 → ℝ) (π : Pol) : Prop :=
  ∀ x : Fin 5, ∀ π' : Pol, dot (rsdFrom π' x) R ≤ dot (rsdFrom π x) R

/-- All-states optimality implies the library's start-state optimality. -/
theorem avgOptimalAll_imp (R : Fin 5 → ℝ) (π : Pol) (h : AvgOptimalAll R π) : AvgOptimal R π :=
  fun π' => h 0 π'

/-- **Keep is all-states average-optimal for some policy iff `max (R c1) (R c2) ≤ R z`** — the
library's `keep_avgOptimal_iff` right-hand side. -/
theorem keep_all_iff (R : Fin 5 → ℝ) :
    (∃ π : Pol, π.1 = true ∧ AvgOptimalAll R π) ↔ max (R 2) (R 3) ≤ R 4 := by
  constructor
  · rintro ⟨π, hk, h⟩
    exact (keep_avgOptimal_iff R).1 ⟨π, hk, avgOptimalAll_imp R π h⟩
  · intro hmax
    have h2 : R 2 ≤ R 4 := le_trans (le_max_left _ _) hmax
    have h3 : R 3 ≤ R 4 := le_trans (le_max_right _ _) hmax
    rcases le_total (R 3) (R 2) with h32 | h23
    · refine ⟨(true, true, false), rfl, ?_⟩
      intro x π'
      rcases π' with ⟨k, a, b⟩
      fin_cases x <;> cases k <;> cases a <;> cases b <;>
        (try simp [dot, rsdFrom, ez, fromC1, fromC2, rsd, Fin.sum_univ_succ]) <;> linarith
    · refine ⟨(true, false, true), rfl, ?_⟩
      intro x π'
      rcases π' with ⟨k, a, b⟩
      fin_cases x <;> cases k <;> cases a <;> cases b <;>
        (try simp [dot, rsdFrom, ez, fromC1, fromC2, rsd, Fin.sum_univ_succ]) <;> linarith

/-- **Erode is all-states average-optimal for some policy iff `R z ≤ max (R c1) (R c2)`** — the
library's `erode_avgOptimal_iff` right-hand side. -/
theorem erode_all_iff (R : Fin 5 → ℝ) :
    (∃ π : Pol, π.1 = false ∧ AvgOptimalAll R π) ↔ R 4 ≤ max (R 2) (R 3) := by
  constructor
  · rintro ⟨π, hk, h⟩
    exact (erode_avgOptimal_iff R).1 ⟨π, hk, avgOptimalAll_imp R π h⟩
  · intro hmax
    rcases le_total (R 3) (R 2) with h32 | h23
    · have h4 : R 4 ≤ R 2 := by rw [max_eq_left h32] at hmax; exact hmax
      refine ⟨(false, true, false), rfl, ?_⟩
      intro x π'
      rcases π' with ⟨k, a, b⟩
      fin_cases x <;> cases k <;> cases a <;> cases b <;>
        (try simp [dot, rsdFrom, ez, fromC1, fromC2, rsd, Fin.sum_univ_succ]) <;> linarith
    · have h4 : R 4 ≤ R 3 := by rw [max_eq_right h23] at hmax; exact hmax
      refine ⟨(false, false, true), rfl, ?_⟩
      intro x π'
      rcases π' with ⟨k, a, b⟩
      fin_cases x <;> cases k <;> cases a <;> cases b <;>
        (try simp [dot, rsdFrom, ez, fromC1, fromC2, rsd, Fin.sum_univ_succ]) <;> linarith

/-- **The existential keep forms coincide**: Def. 6.11 in full and at the start state. -/
theorem keep_all_iff_start (R : Fin 5 → ℝ) :
    (∃ π : Pol, π.1 = true ∧ AvgOptimalAll R π) ↔ (∃ π : Pol, π.1 = true ∧ AvgOptimal R π) := by
  rw [keep_all_iff, keep_avgOptimal_iff]

/-- **The existential erode forms coincide**: Def. 6.11 in full and at the start state. -/
theorem erode_all_iff_start (R : Fin 5 → ℝ) :
    (∃ π : Pol, π.1 = false ∧ AvgOptimalAll R π) ↔ (∃ π : Pol, π.1 = false ∧ AvgOptimal R π) := by
  rw [erode_all_iff, erode_avgOptimal_iff]

end

end Cleanroom.Corrigibility.CorrPowerChannel.AuditR3

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# corr-value-change — belief updates with a random outcome: (R), (M), (Z), (R∣L)

Source: [[value-change-as-epistemic-update]] §2.3 and §6.2–6.3. A **joint** `P` over worlds `W`
and update outcomes `I` (`P(w, i)`), with `π_i = P(E_i) = ∑_w P(w, i)` and the marginal
`P⁺(w) = ∑_i P(w, i)`; an **installed family** `Q_i`, one probability on `W` per outcome. The
three rules, in product form (no division; the guard `0 < π_i` is the note's "for every `i` with
`π_i > 0`"):
- **(R)** Reflection: `P(· ∣ E_i) = Q_i`, i.e. `P(w, i) = π_i · Q_i(w)` for every `w`, whenever `π_i > 0`;
- **(M)** no expected net update: `P⁺(w) = ∑_i π_i Q_i(w)`;
- **(Z)** no update away from zero: `P⁺(w) = 0 ⇒ Q_i(w) = 0` for every `i` with `π_i > 0`;
- **(R∣L)** reflection conditional on an event `L ⊆ W × I`: `P(· ∣ E_i ∧ L) = Q_i` whenever
  `P(E_i ∧ L) > 0`.
`T6` instantiates `W := Ω × Θ` (the note's (R⁺), (M⁺), (Z)); `T12` uses a general `W`.

Why not `LitDdbFrames.Reflects`: that predicate compares `π` on `W` with the rows of a frame
`F : Frame W` on the *same* `W`, cell by cell of the map `w ↦ F.P w`. The note's (R⁺) compares
the conditional of a joint on `W × I` given the outcome `i` with a state `Q_i` on `W`; the
outcome is a separate coordinate, and distinct outcomes may install the same state (the pill),
which a frame's cells would merge. `Reflection` below is the note's object; a bridge to a frame
on `W × I` (rows `(w, i) ↦ [i' = i] · Q_i(w)`) was not written and is not needed for any headline.
-/

namespace Cleanroom.Corrigibility.CorrValueChange

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {W I : Type} [Fintype W] [Fintype I] [DecidableEq W] [DecidableEq I]

/-- **A joint** over worlds and update outcomes: `P(w, i) ≥ 0`, total mass one.
Source: [[value-change-as-epistemic-update]] §2.3 ("the agent's joint `P` on `Ω × Θ × I`"), §6.3
Kind: D
Fidelity: exact -/
structure Joint (W I : Type) [Fintype W] [Fintype I] where
  /-- the joint weight of world `w` and outcome `i` -/
  P : W → I → ℝ
  /-- nonnegative -/
  nonneg : ∀ w i, 0 ≤ P w i
  /-- total mass one -/
  sum_one : ∑ w, ∑ i, P w i = 1

/-- **An installed family**: for each outcome `i` the state `Q_i` the modification installs, a
probability on `W`.
Source: [[value-change-as-epistemic-update]] §2.3 ("installs the state `Q_i` on `Ω⁺`")
Kind: D
Fidelity: exact -/
structure Installed (W I : Type) [Fintype W] [Fintype I] where
  /-- `Q_i(w)` -/
  Q : I → W → ℝ
  /-- nonnegative -/
  nonneg : ∀ i w, 0 ≤ Q i w
  /-- each `Q_i` sums to one -/
  sum_one : ∀ i, ∑ w, Q i w = 1

namespace Joint

variable (J : Joint W I)

/-- `π_i = P(E_i) = ∑_w P(w, i)`.
Source: [[value-change-as-epistemic-update]] §2.3
Kind: D
Fidelity: exact -/
def π (i : I) : ℝ := ∑ w, J.P w i

/-- The marginal on worlds, `P⁺(w) = ∑_i P(w, i)`.
Source: [[value-change-as-epistemic-update]] §2.3 (`P⁺`), §6.2 (`P_0`)
Kind: D
Fidelity: exact -/
def marg (w : W) : ℝ := ∑ i, J.P w i

/-- `π_i ≥ 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π_nonneg (i : I) : 0 ≤ J.π i := sum_nonneg fun w _ => J.nonneg w i

/-- `∑_i π_i = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π_sum : ∑ i, J.π i = 1 := by
  unfold π; rw [sum_comm]; exact J.sum_one

/-- `P⁺(w) ≥ 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem marg_nonneg (w : W) : 0 ≤ J.marg w := sum_nonneg fun i _ => J.nonneg w i

/-- `∑_w P⁺(w) = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem marg_sum : ∑ w, J.marg w = 1 := J.sum_one

/-- `P(w, i) ≤ π_i`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem P_le_π (w : W) (i : I) : J.P w i ≤ J.π i :=
  single_le_sum (f := fun w => J.P w i) (fun w _ => J.nonneg w i) (mem_univ w)

/-- `P(w, i) ≤ P⁺(w)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem P_le_marg (w : W) (i : I) : J.P w i ≤ J.marg w :=
  single_le_sum (f := fun i => J.P w i) (fun i _ => J.nonneg w i) (mem_univ i)

/-- `P(w, i) = 0` when `π_i = 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem P_eq_zero_of_π_eq_zero {i : I} (h : J.π i = 0) (w : W) : J.P w i = 0 :=
  le_antisymm (h ▸ J.P_le_π w i) (J.nonneg w i)

/-- The weight of `(w, i)` restricted to an event `L ⊆ W × I`: `P(w, i)·𝟙_L(w, i)`.
Source: [[value-change-as-epistemic-update]] §2.3 (Conditional reflection)
Kind: D
Fidelity: exact -/
def PL (L : Finset (W × I)) (w : W) (i : I) : ℝ := if (w, i) ∈ L then J.P w i else 0

/-- `P(E_i ∧ L)`.
Source: [[value-change-as-epistemic-update]] §2.3
Kind: D
Fidelity: exact -/
def πL (L : Finset (W × I)) (i : I) : ℝ := ∑ w, J.PL L w i

/-- `P(L)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def massL (L : Finset (W × I)) : ℝ := ∑ i, J.πL L i

/-- On the sure event `L = ⊤` the restricted weight is the weight.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem PL_univ (w : W) (i : I) : J.PL univ w i = J.P w i := by simp [PL]

/-- On the sure event, `P(E_i ∧ ⊤) = π_i`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem πL_univ (i : I) : J.πL univ i = J.π i := by simp [πL, π]

/-- `0 ≤ P(w,i)·𝟙_L`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem PL_nonneg (L : Finset (W × I)) (w : W) (i : I) : 0 ≤ J.PL L w i := by
  unfold PL; split_ifs
  · exact J.nonneg w i
  · exact le_refl 0

/-- `0 ≤ P(E_i ∧ L)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem πL_nonneg (L : Finset (W × I)) (i : I) : 0 ≤ J.πL L i :=
  sum_nonneg fun w _ => J.PL_nonneg L w i

/-- `P(E_i ∧ L) ≤ π_i`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem πL_le_π (L : Finset (W × I)) (i : I) : J.πL L i ≤ J.π i := by
  unfold πL π
  apply sum_le_sum; intro w _
  unfold PL; split_ifs
  · exact le_refl _
  · exact J.nonneg w i

end Joint

/-! ## The rules -/

/-- **(R) Reflection**: `P(· ∣ E_i) = Q_i` for every `i` with `π_i > 0`, in product form
`P(w, i) = π_i · Q_i(w)`. This is the note's (R⁺) (for `W = Ω × Θ`) and (R) (§6.3), van
Fraassen's Reflection applied to the modification: an equality of the *conditional distribution*
with the installed state, not merely of expectations.
Source: [[value-change-as-epistemic-update]] §2.3 (R⁺), §6.3 (R)
Kind: D
Fidelity: exact -/
def Reflection (J : Joint W I) (Q : Installed W I) : Prop :=
  ∀ i, 0 < J.π i → ∀ w, J.P w i = J.π i * Q.Q i w

/-- **(M) no expected net update**: `P⁺ = ∑_i π_i Q_i` — the present state is the average of
the installed states.
Source: [[value-change-as-epistemic-update]] §2.3 (M⁺), §6.2 (M)
Kind: D
Fidelity: exact -/
def Martingale (J : Joint W I) (Q : Installed W I) : Prop :=
  ∀ w, J.marg w = ∑ i, J.π i * Q.Q i w

/-- **(Z) no update away from zero**: a world of prior probability zero gets probability zero
from every outcome of positive probability.
Source: [[value-change-as-epistemic-update]] §2.3 (Z), §6.2 (Z)
Kind: D
Fidelity: exact -/
def NoZero (J : Joint W I) (Q : Installed W I) : Prop :=
  ∀ w, J.marg w = 0 → ∀ i, 0 < J.π i → Q.Q i w = 0

/-- **(R∣L) reflection conditional on legitimacy**: `P(· ∣ E_i ∧ L) = Q_i` for every `i` with
`P(E_i ∧ L) > 0`, in product form `P(w, i)·𝟙_L(w, i) = P(E_i ∧ L) · Q_i(w)`; nothing is required
on `¬L`. `L` is any event of the joint (world and outcome), as the note allows ("which event is
a modelling choice").
Source: [[value-change-as-epistemic-update]] §2.3 (Conditional reflection, (R⁺∣L))
Kind: D
Fidelity: exact -/
def CondReflection (J : Joint W I) (Q : Installed W I) (L : Finset (W × I)) : Prop :=
  ∀ i, 0 < J.πL L i → ∀ w, J.PL L w i = J.πL L i * Q.Q i w

/-- **(R∣L) is vacuous on a null `L`**: when `P(L) = 0` every installed family satisfies it (no `i`
has `P(E_i ∧ L) > 0`). So a conditional-reflection headline carries content only when some
`P(E_i ∧ L) > 0`; the package's witnesses have it (`lam_condReflection` for `λ > 0`).
Source: none: infrastructure (audit r1, adversarial N1)
Kind: L
Fidelity: n/a -/
theorem condReflection_of_massL_eq_zero (J : Joint W I) (Q : Installed W I) (L : Finset (W × I))
    (hL : J.massL L = 0) : CondReflection J Q L := by
  intro i hi
  exfalso
  have hle : J.πL L i ≤ ∑ i', J.πL L i' :=
    single_le_sum (f := fun i => J.πL L i) (fun i _ => J.πL_nonneg L i) (mem_univ i)
  unfold Joint.massL at hL
  linarith

/-- **T6(a): (R) ⇒ (M)**. Summing Reflection over `i` (outcomes with `π_i = 0` contribute
nothing on either side).
Source: [[value-change-as-epistemic-update]] §2.3 ("Summing (R⁺) over `i` gives … (M⁺)"), §6.3
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem reflection_imp_martingale {J : Joint W I} {Q : Installed W I} (h : Reflection J Q) :
    Martingale J Q := by
  intro w
  unfold Joint.marg
  refine sum_congr rfl fun i _ => ?_
  rcases (J.π_nonneg i).lt_or_eq with hpos | hzero
  · exact h i hpos w
  · rw [J.P_eq_zero_of_π_eq_zero hzero.symm w, ← hzero, zero_mul]

/-- **T6(a): (M) ⇒ (Z)**. A sum of nonnegative terms is zero only if each is.
Source: [[value-change-as-epistemic-update]] §2.3 ("(M⁺) implies … (Z)"), §6.2 ("(Z) follows
from (M)")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem martingale_imp_noZero {J : Joint W I} {Q : Installed W I} (h : Martingale J Q) :
    NoZero J Q := by
  intro w hw i hi
  have hsum : ∑ i, J.π i * Q.Q i w = 0 := by rw [← h w]; exact hw
  have hnn : ∀ i ∈ (univ : Finset I), 0 ≤ J.π i * Q.Q i w :=
    fun i _ => mul_nonneg (J.π_nonneg i) (Q.nonneg i w)
  have := (sum_eq_zero_iff_of_nonneg hnn).1 hsum i (mem_univ i)
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 hi.ne'
  · exact h0

/-- (R) ⇒ (Z), composed.
Source: [[value-change-as-epistemic-update]] §2.3
Kind: C
Fidelity: exact -/
theorem reflection_imp_noZero {J : Joint W I} {Q : Installed W I} (h : Reflection J Q) :
    NoZero J Q := martingale_imp_noZero (reflection_imp_martingale h)

/-- **T8(a): (R⁺) is (R⁺∣L) at `L = ⊤`.**
Source: [[value-change-as-epistemic-update]] §2.3 ("(R⁺) is the case `L = ⊤`")
Kind: L
Fidelity: exact -/
theorem condReflection_univ_iff (J : Joint W I) (Q : Installed W I) :
    CondReflection J Q univ ↔ Reflection J Q := by
  unfold CondReflection Reflection
  simp only [Joint.PL_univ, Joint.πL_univ]

/-- Under (R), the installed state at a positive-probability outcome is the conditional:
`Q_i(w) = P(w, i) / π_i`.
Source: [[value-change-as-epistemic-update]] §2.3
Kind: L
Fidelity: exact -/
theorem Reflection.Q_eq {J : Joint W I} {Q : Installed W I} (h : Reflection J Q) {i : I}
    (hi : 0 < J.π i) (w : W) : Q.Q i w = J.P w i / J.π i := by
  rw [h i hi w]; field_simp

/-- Under (R), two outcomes installing the same state have the same conditional; in particular
a **constant installed state forces `P⁺ = Q`** (Claim 1's second half, as a statement about the
marginal on `W`): if `Q_i = Q₀` for every `i` then `P⁺ = Q₀` pointwise.
Source: [[value-change-as-epistemic-update]] §2.4 Claim 1 ("(R⁺) with a constant target gives
`P = Q`"); mandate Known issues 2 (it is literally `P⁺ = Q` on `Ω⁺`)
Kind: P
Fidelity: exact
Hyps: (a) `h : Reflection`, `hc : ∀ i, Q_i = Q₀` -/
theorem Reflection.marg_eq_of_const {J : Joint W I} {Q : Installed W I} (h : Reflection J Q)
    (Q₀ : W → ℝ) (hc : ∀ i w, Q.Q i w = Q₀ w) (w : W) : J.marg w = Q₀ w := by
  have hM := reflection_imp_martingale h w
  rw [hM]
  simp_rw [hc]
  rw [← sum_mul, J.π_sum, one_mul]

end

end Cleanroom.Corrigibility.CorrValueChange

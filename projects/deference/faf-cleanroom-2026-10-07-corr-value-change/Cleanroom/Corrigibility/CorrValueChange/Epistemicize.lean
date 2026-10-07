import Cleanroom.Corrigibility.CorrValueChange.Examples14
import Cleanroom.Corrigibility.CorrValueChange.Good

/-!
# corr-value-change — (A) = 0 iff an epistemicization with (R⁺) reproduces the installed choices (T10(d))

Source: [[value-change-as-epistemic-update]] §3.4 ("(A) = 0 iff the installed values select, in
each outcome, what the old values would select given that outcome"), mandate T10(d). This module
glues the two-step model of §1 (`ProductModel`, `TwoStep`, the value table) to the epistemic
model of §2 (`Joint`, `Installed`, `Reflection`, the branch values `S`): the change event of a
product model, with its outcome coordinate, *is* a joint on `(F × Option J) × Θ` with outcomes `J`,
and an **epistemicization** of the two-step decision is any such joint, over any finite candidate
type `Θ`, whose `Θ`-marginal is that joint and whose effective utility is the present `U`
(`IsEpistemicization`). For every epistemicization the branch value is `p_j · v_j(a)`
(`S_of_isEpistemicization`), so term (A) of §1.4 is `termAep` of §2.4 (`termA_eq_termAep`), and
`A_zero_iff_epistemicizable` is T10(d): (A) = 0 iff some epistemicization, reflected, has the
installed choices as installed maximizers. The `termA = 0 → ∃` direction is witnessed by the
trivial epistemicization `Θ = Unit` with `Q_j := P(· ∣ C_j)` (`epiJoint`, `condInstalled`,
reflected by construction, `epiJoint_reflection`); the `∃ → termA = 0` direction is
`branch_opt_of_reflection` on any epistemicization. (The mandate's T10(d) calls these "⇐" and
"⇒", reading the iff as "∃ … iff (A) = 0"; the directions here are named by content, after audit
r4 adversarial N4, because the Lean statement is written the other way round.)
Under any reflected epistemicization the installed value is the informed value,
`E_{Q_j}[U_a] = v_j(a)` (`EQ_eq_v_of_epistemicization`), so the iff is `termA_eq_zero_iff`
relativized through that identity; where it bites is the `∃ → termA = 0` direction, over every
finite `Θ`:
the coin admits no reflected epistemicization with the signal choices as installed maximizers
(`coin_not_epistemicizable`). `IsEpistemicization.eff` conditions the effective utility on
`(w, j)` rather than on `w` alone as §2.1's `Ū` does; since `w = (f, c)` carries the configuration
and `P'(w, j) = 0` unless `c = C_j`, the two coincide for every joint with this `Θ`-marginal.
Caution (audit r1): this reproduces `v_j` and the installed choices, not `Val(decline)`: the
epistemic model has no keep event, so with payment `E_{P'}[U_a] = ∑_j p_j v_j(a) ≠ v_K(a)`; T10(d)
is a statement about choices, and that is all this module claims.
-/

namespace Cleanroom.Corrigibility.CorrValueChange

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {F J A : Type} [Fintype F] [Fintype J] [Fintype A] [DecidableEq F] [DecidableEq J]
  [DecidableEq A] [Nonempty J]

namespace ProductModel

variable (M : ProductModel F J A)

/-- The worlds of the epistemic model: fact and configuration (the act coordinate dropped, as in
§2.4 after `act_independent_condExp`).
Source: [[value-change-as-epistemic-update]] §3.4
Kind: D
Fidelity: exact -/
abbrev Wc (F J : Type) := F × Option J

/-- Summing an outcome-`j` slice over the worlds `(f, c, ())`: only `c = C_j` contributes.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_slice (g : F → Option J → ℝ) (j : J) :
    (∑ w : Wc F J × Unit, if w.1.2 = some j then g w.1.1 w.1.2 else 0) = ∑ f, g f (some j) := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun f _ => ?_
  rw [Fintype.sum_option]
  simp

/-- **The change event as a joint with the outcome coordinate**: `P'((f, c), j) = [c = C_j] q(f, c) / P(C)`
on worlds `(f, c)` with the trivial candidate coordinate `Θ = Unit` and outcomes `J`. This is the
two-step decision conditioned on `C`, which is what the value table `p_j, v_j` describes.
Source: [[value-change-as-epistemic-update]] §3.4 ("construct `Q_j := P(· ∣ C_j)`"), mandate T10(d)
Kind: D
Fidelity: exact -/
def epiJoint : Joint (Wc F J × Unit) J where
  P := fun w j => if w.1.2 = some j then M.q w.1.1 w.1.2 / M.qCtot else 0
  nonneg := fun w j => by
    split_ifs
    · exact div_nonneg (M.q_nonneg _ _) M.qCtot_pos.le
    · exact le_rfl
  sum_one := by
    rw [sum_comm]
    have h : ∀ j, (∑ w : Wc F J × Unit, if w.1.2 = some j then M.q w.1.1 w.1.2 / M.qCtot else 0) =
        M.qC j / M.qCtot := by
      intro j; rw [sum_slice (fun f c => M.q f c / M.qCtot) j]; unfold qC; rw [sum_div]
    simp_rw [h]
    rw [← sum_div]; exact div_self M.qCtot_pos.ne'

/-- `π_j = P(C_j) / P(C) = p_j`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem epiJoint_π (j : J) : M.epiJoint.π j = M.toTwoStep.p j := by
  unfold Joint.π epiJoint
  simp only
  rw [sum_slice (fun f c => M.q f c / M.qCtot) j, M.toTwoStep_p]
  unfold qC; rw [sum_div]

/-- **The conditional installation** `Q_j := P(· ∣ C_j)`: `Q_j(f, c) = [c = C_j] q(f, c) / P(C_j)`.
Source: [[value-change-as-epistemic-update]] §3.4, mandate T10(d) ("construct `Q_j := P(· ∣ C_j)`")
Kind: D
Fidelity: exact -/
def condInstalled : Installed (Wc F J × Unit) J where
  Q := fun j w => if w.1.2 = some j then M.q w.1.1 w.1.2 / M.qC j else 0
  nonneg := fun j w => by
    split_ifs
    · exact div_nonneg (M.q_nonneg _ _) (M.qC_pos j).le
    · exact le_rfl
  sum_one := fun j => by
    rw [sum_slice (fun f c => M.q f c / M.qC j) j]
    unfold qC; rw [← sum_div]; exact div_self (M.qC_pos j).ne'

/-- **The trivial epistemicization is reflected**: `P'(w, j) = π_j Q_j(w)` by construction.
Source: [[value-change-as-epistemic-update]] §3.4; mandate T10(d) (the `termA = 0 → ∃`
direction, the mandate's "⇐")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem epiJoint_reflection : Reflection M.epiJoint M.condInstalled := by
  intro j _ w
  rw [epiJoint_π, toTwoStep_p]
  unfold epiJoint condInstalled
  simp only
  split_ifs
  · have h1 : M.qC j ≠ 0 := (M.qC_pos j).ne'
    have h2 : M.qCtot ≠ 0 := M.qCtot_pos.ne'
    field_simp
  · simp

/-- The present utility as a (constant-in-`θ`) candidate family on the epistemic worlds:
`u_{(), a}(f, c) = U(f, c, a)`.
Source: [[value-change-as-epistemic-update]] §3.4
Kind: D
Fidelity: exact -/
def uOf : Unit → A → Wc F J → ℝ := fun _ a w => M.Uf w.1 w.2 a

/-- **An epistemicization of the two-step decision**: a finite candidate type `Θ`, a joint on
`(F × Option J) × Θ` with outcomes `J`, and candidates `u_{θ,a}`, such that (i) the `Θ`-marginal is the
change event's joint `P'`, and (ii) the effective utility is the present `U`:
`∑_θ P⁺((w, θ), j) u_{θ,a}(w) = P'(w, j) U(w, a)` (the product form of `Ū_a(w) = U_a(w)` at every
world of positive probability; vacuous at null worlds).
Source: [[value-change-as-epistemic-update]] §2.1 (epistemicization: `P⁺` with marginal `P̄` and
effective utility `Ū`), §3.4
Kind: D
Fidelity: exact -/
structure IsEpistemicization {Θ : Type} [Fintype Θ] (Pp : Joint (Wc F J × Θ) J)
    (u : Θ → A → Wc F J → ℝ) : Prop where
  /-- the `Θ`-marginal is `P'` -/
  marg : ∀ w j, ∑ θ, Pp.P (w, θ) j = M.epiJoint.P (w, ()) j
  /-- the effective utility is `U` -/
  eff : ∀ w j a, ∑ θ, Pp.P (w, θ) j * u θ a w = (∑ θ, Pp.P (w, θ) j) * M.Uf w.1 w.2 a

/-- The trivial epistemicization is one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem epiJoint_isEpistemicization : M.IsEpistemicization M.epiJoint M.uOf where
  marg := fun w j => by rw [Fintype.sum_unique]
  eff := fun w j a => by rw [Fintype.sum_unique, Fintype.sum_unique]; rfl

/-- **The branch value of the trivial epistemicization is `p_j · v_j(a)`.**
Source: [[value-change-as-epistemic-update]] §3.4
Kind: L
Fidelity: exact -/
theorem S_epiJoint (a : A) (j : J) :
    S M.epiJoint M.uOf a j = M.toTwoStep.p j * M.toTwoStep.v M.U j a := by
  rw [toTwoStep_p, toTwoStep_v]
  unfold S epiJoint uOf Uplus
  simp only
  have h : ∀ w : Wc F J × Unit,
      (if w.1.2 = some j then M.q w.1.1 w.1.2 / M.qCtot else 0) * M.Uf w.1.1 w.1.2 a =
        if w.1.2 = some j then M.q w.1.1 w.1.2 * M.Uf w.1.1 w.1.2 a / M.qCtot else 0 := by
    intro w; split_ifs
    · ring
    · ring
  simp_rw [h]
  rw [sum_slice (fun f c => M.q f c * M.Uf f c a / M.qCtot) j]
  unfold vf
  have h1 : M.qC j ≠ 0 := (M.qC_pos j).ne'
  have h2 : M.qCtot ≠ 0 := M.qCtot_pos.ne'
  rw [← sum_div]
  field_simp

/-- **The installed value under the conditional installation is `v_j`**: `E_{Q_j}[U_a] = v_j(a)`, so
the installed maximizers are exactly the `v_j`-maximizers.
Source: [[value-change-as-epistemic-update]] §3.4
Kind: L
Fidelity: exact -/
theorem EQ_condInstalled (j : J) (a : A) :
    EQ M.condInstalled M.uOf j a = M.toTwoStep.v M.U j a := by
  rw [toTwoStep_v]
  unfold EQ condInstalled uOf Uplus
  simp only
  have h : ∀ w : Wc F J × Unit,
      (if w.1.2 = some j then M.q w.1.1 w.1.2 / M.qC j else 0) * M.Uf w.1.1 w.1.2 a =
        if w.1.2 = some j then M.q w.1.1 w.1.2 * M.Uf w.1.1 w.1.2 a / M.qC j else 0 := by
    intro w; split_ifs
    · ring
    · ring
  simp_rw [h]
  rw [sum_slice (fun f c => M.q f c * M.Uf f c a / M.qC j) j]
  unfold vf
  rw [← sum_div]

/-- **Every epistemicization has the same branch values**, `S(a, j) = p_j · v_j(a)`: the candidate
coordinate integrates out by (ii).
Source: [[value-change-as-epistemic-update]] §2.1 (`marginalization`), §3.4
Kind: P
Fidelity: exact
Hyps: (a) `h : IsEpistemicization` -/
theorem S_of_isEpistemicization {Θ : Type} [Fintype Θ] [DecidableEq Θ]
    {Pp : Joint (Wc F J × Θ) J} {u : Θ → A → Wc F J → ℝ} (h : M.IsEpistemicization Pp u)
    (a : A) (j : J) : S Pp u a j = M.toTwoStep.p j * M.toTwoStep.v M.U j a := by
  rw [← M.S_epiJoint a j]
  unfold S
  have hL : ∑ x : Wc F J × Θ, Pp.P x j * Uplus u a x =
      ∑ w : Wc F J, ∑ θ, Pp.P (w, θ) j * Uplus u a (w, θ) :=
    Fintype.sum_prod_type _
  have hR : ∑ x : Wc F J × Unit, M.epiJoint.P x j * Uplus M.uOf a x =
      ∑ w : Wc F J, M.epiJoint.P (w, ()) j * Uplus M.uOf a (w, ()) := by
    rw [Fintype.sum_prod_type (f := fun x : Wc F J × Unit => M.epiJoint.P x j * Uplus M.uOf a x)]
    simp only [Fintype.sum_unique]
  rw [hL, hR]
  refine sum_congr rfl fun w _ => ?_
  simp only [Uplus]
  rw [h.eff w j a, h.marg w j]
  rfl

/-- **Term (A) of §1.4 is term (A) of §2.4** on every epistemicization.
Source: [[value-change-as-epistemic-update]] §2.4 ("In the terms of §1.4"), §3.4
Kind: P
Fidelity: exact
Hyps: (a) `h : IsEpistemicization` -/
theorem termA_eq_termAep {Θ : Type} [Fintype Θ] [DecidableEq Θ] {Pp : Joint (Wc F J × Θ) J}
    {u : Θ → A → Wc F J → ℝ} (h : M.IsEpistemicization Pp u) (aj ahat : J → A) :
    (M.toTwoStep.table M.U).termA aj ahat = termAep Pp u aj ahat := by
  unfold ValueTable.termA termAep TwoStep.table
  simp only
  refine sum_congr rfl fun j _ => ?_
  rw [M.S_of_isEpistemicization h, M.S_of_isEpistemicization h]
  ring

/-- **T10(d), the `∃ → termA = 0` direction (reflection forces the informed choice)**: if some epistemicization is reflected and
the installed choices `a^j` are its installed maximizers, then (A) = 0 — the installed choices
maximize `v_j`.
Source: [[value-change-as-epistemic-update]] §3.4; mandate T10(d) ("for ⇒ show (R⁺) forces the
installed choice to maximize `v_j`"; the mandate's "⇒" is this direction)
Kind: P
Fidelity: exact
Hyps: (a) `h : IsEpistemicization`, `hR : Reflection`, `hhat : â^j` maximizes `v_j`, `hstar : a^j`
maximizes `E_{Q_j}` -/
theorem termA_zero_of_reflection {Θ : Type} [Fintype Θ] [DecidableEq Θ]
    {Pp : Joint (Wc F J × Θ) J} {u : Θ → A → Wc F J → ℝ} (h : M.IsEpistemicization Pp u)
    (Q : Installed (Wc F J × Θ) J) (hR : Reflection Pp Q) (aj ahat : J → A)
    (hhat : ∀ j a, M.toTwoStep.v M.U j a ≤ M.toTwoStep.v M.U j (ahat j))
    (hstar : ∀ j a, EQ Q u j a ≤ EQ Q u j (aj j)) :
    (M.toTwoStep.table M.U).termA aj ahat = 0 := by
  rw [M.termA_eq_termAep h]
  apply reflection_imp_termAep_zero hR u aj ahat hstar
  intro j a
  rw [M.S_of_isEpistemicization h, M.S_of_isEpistemicization h]
  exact mul_le_mul_of_nonneg_left (hhat j a) (M.toTwoStep.p_pos j).le

/-- **T10(d): (A) = 0 iff an epistemicization with (R⁺) reproduces the installed choices.** For
the two-step decision of a product model, with `â^j` maximizing `v_j`: term (A) vanishes iff there
is an epistemicization (some finite `Θ`, joint `P⁺`, candidates `u`) and an installed family `Q`
with (R⁺) such that every installed choice `a^j` maximizes `E_{Q_j}[U_a]`. The `termA = 0 → ∃`
direction is witnessed by the trivial epistemicization with `Q_j = P(· ∣ C_j)`; the
`∃ → termA = 0` direction holds for every epistemicization.
What the right-hand side says, for every admissible `(Θ, P⁺, u, Q)`, is exactly "the `a^j`
maximize `v_j`" (`EQ_eq_v_of_epistemicization`): the iff is `termA_eq_zero_iff` relativized
through that identity, with `IsEpistemicization ∧ Reflection` as the hypotheses that make the
identity hold (not a squeeze: `S_of_isEpistemicization` is the derivation). The negative instance
is `coin_not_epistemicizable`.
Source: [[value-change-as-epistemic-update]] §3.4 ("(A) = 0 iff the installed values select, in
each outcome, what the old values would select given that outcome"); mandate T10(d)
Kind: P
Fidelity: exact (the epistemicization quantified over all finite candidate types)
Hyps: (a) `hhat : â^j` maximizes `v_j` -/
theorem A_zero_iff_epistemicizable (aj ahat : J → A)
    (hhat : ∀ j a, M.toTwoStep.v M.U j a ≤ M.toTwoStep.v M.U j (ahat j)) :
    (M.toTwoStep.table M.U).termA aj ahat = 0 ↔
      ∃ (Θ : Type) (_ : Fintype Θ) (_ : DecidableEq Θ) (Pp : Joint (Wc F J × Θ) J)
        (u : Θ → A → Wc F J → ℝ) (Q : Installed (Wc F J × Θ) J),
        M.IsEpistemicization Pp u ∧ Reflection Pp Q ∧ ∀ j a, EQ Q u j a ≤ EQ Q u j (aj j) := by
  constructor
  · intro hA
    refine ⟨Unit, inferInstance, inferInstance, M.epiJoint, M.uOf, M.condInstalled,
      M.epiJoint_isEpistemicization, M.epiJoint_reflection, ?_⟩
    intro j a
    rw [EQ_condInstalled, EQ_condInstalled]
    exact ((M.toTwoStep.table M.U).termA_eq_zero_iff aj ahat hhat).1 hA j a
  · rintro ⟨Θ, _, _, Pp, u, Q, h, hR, hstar⟩
    exact M.termA_zero_of_reflection h Q hR aj ahat hhat hstar

end ProductModel

/-- `π_j` of any epistemicization is `p_j` (the `Θ`-marginal is `epiJoint`, whose `π` is `p`).
Source: none: infrastructure; audit r2 (adversarial N1)
Kind: L
Fidelity: n/a -/
theorem π_of_epistemicization (M : ProductModel F J A)
    {Θ : Type} [Fintype Θ] [DecidableEq Θ] {Pp : Joint (ProductModel.Wc F J × Θ) J}
    {u : Θ → A → ProductModel.Wc F J → ℝ} (h : M.IsEpistemicization Pp u) (j : J) :
    Pp.π j = M.toTwoStep.p j := by
  rw [← M.epiJoint_π j]
  unfold Joint.π
  rw [Fintype.sum_prod_type (f := fun x : ProductModel.Wc F J × Θ => Pp.P x j),
    Fintype.sum_prod_type (f := fun x : ProductModel.Wc F J × Unit => M.epiJoint.P x j)]
  refine sum_congr rfl fun w _ => ?_
  rw [h.marg w j]
  simp

/-- **Under any reflected epistemicization the installed value is the informed value**:
`E_{Q_j}[U_a] = v_j(a)`. So "the installed choices are installed maximizers" on the right-hand
side of `A_zero_iff_epistemicizable` says, for every admissible `(Θ, P⁺, u, Q)`, exactly "the
installed choices maximize `v_j`".
Source: [[value-change-as-epistemic-update]] §3.4; audit r2 (adversarial N1)
Kind: P
Fidelity: exact
Hyps: (a) `h : IsEpistemicization`, `hR : Reflection` -/
theorem EQ_eq_v_of_epistemicization (M : ProductModel F J A)
    {Θ : Type} [Fintype Θ] [DecidableEq Θ] {Pp : Joint (ProductModel.Wc F J × Θ) J}
    {u : Θ → A → ProductModel.Wc F J → ℝ} (h : M.IsEpistemicization Pp u)
    (Q : Installed (ProductModel.Wc F J × Θ) J) (hR : Reflection Pp Q) (j : J) (a : A) :
    EQ Q u j a = M.toTwoStep.v M.U j a := by
  have hS := S_eq_of_reflection hR u a j
  rw [M.S_of_isEpistemicization h, π_of_epistemicization M h] at hS
  have hp := M.toTwoStep.p_pos j
  exact (mul_left_cancel₀ hp.ne' hS).symm

/-- **The coin is not reflectively epistemicizable with the signal choices** (T10(d), the
`∃ → termA = 0` direction over all finite `Θ`, applied to `coin_decomposition`'s (A) = −1/10): no finite candidate
type, joint, candidate utilities and installed family make the coin's change event an
epistemicization that is reflected and has the signal-following choices as installed maximizers.
This is where T10(d) has teeth; the teacher (`teacher_epistemicizable`) only inhabits the `termA = 0 → ∃` side.
Source: [[value-change-as-epistemic-update]] §1.4 (the coin), §3.4; mandate T10(d); audit r2
(adversarial N1)
Kind: N+ (refutation)
Fidelity: exact -/
theorem coin_not_epistemicizable :
    ¬ ∃ (Θ : Type) (_ : Fintype Θ) (_ : DecidableEq Θ)
        (Pp : Joint (ProductModel.Wc Bool Bool × Θ) Bool)
        (u : Θ → Fin 3 → ProductModel.Wc Bool Bool → ℝ)
        (Q : Installed (ProductModel.Wc Bool Bool × Θ) Bool),
        coinPM.IsEpistemicization Pp u ∧ Reflection Pp Q ∧
          ∀ j a, EQ Q u j a ≤ EQ Q u j (chooseSignal j) := by
  obtain ⟨_, hhat, hA, _, _⟩ := coin_decomposition
  intro h
  have := (coinPM.A_zero_iff_epistemicizable chooseSignal (fun _ => 2) hhat).2 h
  rw [hA] at this
  norm_num at this

/-- **The teacher is epistemicizable**: the trivial epistemicization of `teacherPM` is reflected
and its installed maximizers are the signal-following choices `a_j`, so (A) = 0 there by T10(d)
(the same `0` as `teacher_decomposition`). Non-degenerate: two outcomes, three acts, the installed
states `P(· ∣ C_A) ≠ P(· ∣ C_B)`. What it exercises (audit r2): the `termA = 0 → ∃` direction only, and the
third clause, `termA a_j a_j = 0`, is an identity in every model (the installed choice *is* the
informed one), here derived through the iff. The `∃ → termA = 0` direction is exercised by
`coin_not_epistemicizable`.
Source: [[value-change-as-epistemic-update]] §1.4, §3.4; mandate T10(d)
Kind: N+ (`termA = 0 → ∃` side; the (A) = 0 clause is an identity)
Fidelity: exact -/
theorem teacher_epistemicizable :
    Reflection teacherPM.epiJoint teacherPM.condInstalled ∧
    (∀ j a, EQ teacherPM.condInstalled teacherPM.uOf j a ≤
      EQ teacherPM.condInstalled teacherPM.uOf j (chooseSignal j)) ∧
    (teacherPM.toTwoStep.table teacherPM.U).termA chooseSignal chooseSignal = 0 := by
  obtain ⟨_, hv, _, _, _, _, _⟩ := teacher_decomposition
  refine ⟨teacherPM.epiJoint_reflection, ?_, ?_⟩
  · intro j a; rw [ProductModel.EQ_condInstalled, ProductModel.EQ_condInstalled]; exact hv j a
  · exact (teacherPM.A_zero_iff_epistemicizable chooseSignal chooseSignal hv).2
      ⟨Unit, inferInstance, inferInstance, teacherPM.epiJoint, teacherPM.uOf,
        teacherPM.condInstalled, teacherPM.epiJoint_isEpistemicization,
        teacherPM.epiJoint_reflection, fun j a => by
          rw [ProductModel.EQ_condInstalled, ProductModel.EQ_condInstalled]; exact hv j a⟩

end

end Cleanroom.Corrigibility.CorrValueChange

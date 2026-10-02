import Cleanroom.Found.CorrThreeStep.Setting
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

/-!
# The Soares–Fallenstein–Yudkowsky–Armstrong (2015) three-step model (D-1–D-4, T1–T3)

The model of `soares-2015-corrigibility.md` §1.2: a first action `a₁ ∈ A₁`, an observation
`o ∈ O` drawn from `p(o ; a₁)` with the press event `Press ⊆ O`, a final action `a₂ ∈ A₂`, and a
utility `U(a₁, o, a₂)`. Utilities are *parameters* of the derived objects, never fields: the
package compares several utilities (`U_N`, `U_S`, the §2.1 mixture, the §3 indifferent utility)
on one model.

Conventions (mandate "Definitions of record"): distributions are FAF's `Distr`; every headline is
stated in product form (`∑ o ∈ Pressᶜ, p(o) · best(o)` rather than `E[· | ¬Press]`), with the
conditional quotients `vN`, `vS` *derived* and their junk values at mass 0 disclosed; argmaxes
are never chosen — `best` is the *value* `sup'` and `IsBest` the predicate.

Source: [[corr-refs-inventory]] 001–004 → `references/02-miri/soares-2015-corrigibility.md`
§1.2 (l. 103–119), §2.1 (l. 140–200).
-/

namespace Cleanroom.Corrigibility.CorrIndifference

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep

set_option linter.unusedSectionVars false

/-- **D-1. The Soares model.** A finite observation type `O` with the press event `Press ⊆ O`
and, for each first action `a₁ : A₁`, the observation kernel `p a₁ : Distr O` (`p(o ; a₁)`).
The final-action type `A₂` is a parameter so that the derived objects (`best`, `EU`, …) are
stated over one model; utilities are parameters of those objects, not fields.
Source: [[corr-refs-inventory]] 001 / soares-2015 §1.2 (l. 103–119)
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
structure SoaresModel (O A₁ A₂ : Type*) [Fintype O] where
  /-- The press event `Press ⊆ O`. -/
  Press : Finset O
  /-- The observation kernel `p(o ; a₁)`, a FAF `Distr` per first action. -/
  p : A₁ → Distr O

namespace SoaresModel

variable {O A₁ A₂ : Type*} [Fintype O] [DecidableEq O] [Fintype A₂] [Nonempty A₂]
variable (M : SoaresModel O A₁ A₂)

/-! ## The best final action: value and predicate (argmax never chosen) -/

/-- The value of the best final action at `(a₁, o)`: `max_{a₂ ∈ A₂} U(a₁, o, a₂)` — the source's
`U(a₁, o, A₂(a₁, o))` read as a value, so no argmax is ever selected.
Source: [[corr-refs-inventory]] 001 / soares-2015 §1.2 (the `A₂(a₁, o)` display)
Kind: D
Fidelity: exact -/
noncomputable def best (U : A₁ → O → A₂ → ℝ) (a : A₁) (o : O) : ℝ :=
  univ.sup' univ_nonempty (fun b => U a o b)

/-- `b` is a best final action at `(a₁, o)` under `U`: `∀ b', U a o b' ≤ U a o b`.
Source: [[corr-refs-inventory]] 001 / soares-2015 §1.2 (`A₂(a₁, o) = argmax`)
Kind: D
Fidelity: exact -/
def IsBest (U : A₁ → O → A₂ → ℝ) (a : A₁) (o : O) (b : A₂) : Prop := ∀ b', U a o b' ≤ U a o b

/-- Every final action is at most the best value. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma le_best (U : A₁ → O → A₂ → ℝ) (a : A₁) (o : O) (b : A₂) : U a o b ≤ best U a o :=
  le_sup' (fun b => U a o b) (mem_univ b)

/-- `best ≤ x` iff every final action is `≤ x`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma best_le_iff (U : A₁ → O → A₂ → ℝ) (a : A₁) (o : O) (x : ℝ) :
    best U a o ≤ x ↔ ∀ b, U a o b ≤ x := by
  unfold best; rw [sup'_le_iff]; exact ⟨fun h b => h b (mem_univ b), fun h b _ => h b⟩

/-- The best value is attained by some best action. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma exists_isBest (U : A₁ → O → A₂ → ℝ) (a : A₁) (o : O) :
    ∃ b, IsBest U a o b ∧ best U a o = U a o b := by
  obtain ⟨b, -, hb⟩ := exists_mem_eq_sup' (univ_nonempty (α := A₂)) (fun b => U a o b)
  exact ⟨b, fun b' => hb ▸ le_sup' (fun b => U a o b) (mem_univ b'), hb⟩

/-- A best action attains the best value. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma best_eq_of_isBest {U : A₁ → O → A₂ → ℝ} {a : A₁} {o : O} {b : A₂} (h : IsBest U a o b) :
    best U a o = U a o b :=
  le_antisymm ((best_le_iff U a o _).mpr h) (le_best U a o b)

/-- `best` depends only on the values at `(a, o)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma best_congr {U U' : A₁ → O → A₂ → ℝ} {a : A₁} {o : O} (h : ∀ b, U' a o b = U a o b) :
    best U' a o = best U a o := by
  unfold best; exact sup'_congr univ_nonempty rfl (fun b _ => h b)

/-- A utility constant in the final action has that constant as its best value.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma best_eq_of_const {U : A₁ → O → A₂ → ℝ} {a : A₁} {o : O} {k : ℝ} (h : ∀ b, U a o b = k) :
    best U a o = k := by
  unfold best
  rw [sup'_congr univ_nonempty rfl (fun b _ => h b)]
  exact sup'_const _ _

/-- Adding a constant (in `b`) to the utility at `(a, o)` shifts the best value by it: the
non-circularity of the §3 correction (eq. 14) in value form.
Source: [[corr-refs-inventory]] 006 / soares-2015 §3 eq. (14)
Kind: L
Fidelity: exact -/
lemma best_add_const {U U' : A₁ → O → A₂ → ℝ} {a : A₁} {o : O} {k : ℝ}
    (h : ∀ b, U' a o b = U a o b + k) : best U' a o = best U a o + k := by
  apply le_antisymm
  · rw [best_le_iff]; intro b; rw [h b]; linarith [le_best U a o b]
  · obtain ⟨b, -, hb⟩ := exists_isBest U a o
    rw [hb, ← h b]; exact le_best U' a o b

/-- Adding a constant preserves the best-action predicate (eq. 14: `f(a₁)` does not depend on
`a₂` and so does not affect which `a₂` maximises).
Source: [[corr-refs-inventory]] 006 / soares-2015 §3 eq. (14)
Kind: L
Fidelity: exact -/
lemma isBest_iff_of_add_const {U U' : A₁ → O → A₂ → ℝ} {a : A₁} {o : O} {k : ℝ}
    (h : ∀ b, U' a o b = U a o b + k) (b : A₂) : IsBest U' a o b ↔ IsBest U a o b := by
  unfold IsBest; simp only [h]; exact ⟨fun H b' => by linarith [H b'], fun H b' => by linarith [H b']⟩

/-! ## Expected utility, branch sums, the press mass -/

/-- The expected utility of a first action: `EU(a₁) = ∑_o p(o ; a₁) · max_{a₂} U(a₁, o, a₂)` —
the source's `E[U ; a₁]` with the final action optimal at each observation.
Source: [[corr-refs-inventory]] 001 / soares-2015 §1.2 (the `A₁ := argmax` display)
Kind: D
Fidelity: exact -/
noncomputable def EU (U : A₁ → O → A₂ → ℝ) (a : A₁) : ℝ := ∑ o, (M.p a).mass o * best U a o

/-- The branch sum `∑_{o ∈ S} p(o ; a₁) · best(a₁, o)`: the product-form
`E[U · 1_S ; a₁]`, the conditional expectation times the event mass, no denominator.
Source: none: infrastructure (the product form of every `E[· | S ; a₁]` in the source)
Kind: D
Fidelity: exact -/
noncomputable def branchSum (U : A₁ → O → A₂ → ℝ) (a : A₁) (S : Finset O) : ℝ :=
  ∑ o ∈ S, (M.p a).mass o * best U a o

/-- The press mass `p(Press ; a₁)`, FAF's `Distr.prob` of the press event.
Source: [[corr-refs-inventory]] 001 / soares-2015 §1.2
Kind: D
Fidelity: exact -/
noncomputable def pressMass (a : A₁) : ℝ := (M.p a).prob (↑M.Press : Set O)

/-- The press mass as a sum over `Press`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pressMass_eq_sum (a : A₁) : M.pressMass a = ∑ o ∈ M.Press, (M.p a).mass o := by
  unfold pressMass Distr.prob
  simp only [Set.indicator_apply, mem_coe]
  rw [sum_ite_mem, univ_inter]

/-- `0 ≤ p(Press ; a₁)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pressMass_nonneg (a : A₁) : 0 ≤ M.pressMass a := (M.p a).prob_nonneg _

/-- `p(Press ; a₁) ≤ 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pressMass_le_one (a : A₁) : M.pressMass a ≤ 1 := (M.p a).prob_le_one _

/-- The silence mass is the complement: `∑_{o ∉ Press} p(o ; a₁) = 1 − p(Press ; a₁)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_compl_mass (a : A₁) : ∑ o ∈ M.Pressᶜ, (M.p a).mass o = 1 - M.pressMass a := by
  rw [M.pressMass_eq_sum, eq_sub_iff_add_eq, add_comm, sum_add_sum_compl]
  exact (M.p a).sum_eq_one

/-- `EU` splits into the press branch and the silence branch (linearity).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma EU_eq_branchSum_add_compl (U : A₁ → O → A₂ → ℝ) (a : A₁) :
    M.EU U a = M.branchSum U a M.Press + M.branchSum U a M.Pressᶜ := by
  unfold EU branchSum; rw [sum_add_sum_compl]

/-- Branch sums are additive in the utility's best values: if `best U'` is `best U` plus a
constant on `S`, the branch sum shifts by the constant times the mass of `S`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma branchSum_eq_of_best_add {U U' : A₁ → O → A₂ → ℝ} {a : A₁} {S : Finset O} {k : ℝ}
    (h : ∀ o ∈ S, best U' a o = best U a o + k) :
    M.branchSum U' a S = M.branchSum U a S + k * ∑ o ∈ S, (M.p a).mass o := by
  unfold branchSum
  rw [mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun o ho => by rw [h o ho]; ring

/-- Branch sums agree when the best values agree on `S`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma branchSum_congr {U U' : A₁ → O → A₂ → ℝ} {a : A₁} {S : Finset O}
    (h : ∀ o ∈ S, best U' a o = best U a o) : M.branchSum U' a S = M.branchSum U a S := by
  unfold branchSum; exact sum_congr rfl fun o ho => by rw [h o ho]

/-- A branch sum is bounded by an upper bound on the best values times the mass of `S`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma branchSum_le_of_best_le {U : A₁ → O → A₂ → ℝ} {a : A₁} {S : Finset O} {Mx : ℝ}
    (h : ∀ o ∈ S, best U a o ≤ Mx) : M.branchSum U a S ≤ Mx * ∑ o ∈ S, (M.p a).mass o := by
  unfold branchSum; rw [mul_sum]
  exact sum_le_sum fun o ho => by
    rw [mul_comm Mx]; exact mul_le_mul_of_nonneg_left (h o ho) ((M.p a).nonneg o)

/-- If the mass of `S` is zero, so is every branch sum over `S` (every point of `S` has mass 0).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma branchSum_eq_zero_of_mass_zero (U : A₁ → O → A₂ → ℝ) (a : A₁) {S : Finset O}
    (h : ∑ o ∈ S, (M.p a).mass o = 0) : M.branchSum U a S = 0 := by
  rw [sum_eq_zero_iff_of_nonneg (fun o _ => (M.p a).nonneg o)] at h
  unfold branchSum
  exact sum_eq_zero fun o ho => by rw [h o ho, zero_mul]

/-! ## The conditional values `vN`, `vS` (derived quotients; junk at mass 0, disclosed) -/

/-- `v_N(a₁) := E[U_N | O ∉ Press ; a₁]` as the derived quotient
`(∑_{o ∉ Press} p(o) best_N(o)) / (1 − p(Press ; a₁))`. **Junk value:** at `p(Press ; a₁) = 1`
this is `x / 0 = 0` by Lean's convention; no headline reads `vN` there without the hypothesis
`pressMass a < 1` (T1 trap). In §2.1, where `O = {Pr, ¬Pr}`, it is `best UN a ¬Pr`
(`twoObs_vN` in `Obs`).
Source: [[corr-refs-inventory]] 001 / soares-2015 §2.1 eq. (7) and §3 (`vN` redefined)
Kind: D
Fidelity: exact (division convention disclosed) -/
noncomputable def vN (UN : A₁ → O → A₂ → ℝ) (a : A₁) : ℝ :=
  M.branchSum UN a M.Pressᶜ / (1 - M.pressMass a)

/-- `v_S(a₁) := E[U_S | O ∈ Press ; a₁]` as the derived quotient over the press branch. **Junk
value** `0` at `p(Press ; a₁) = 0` (disclosed; T4's boundary lemma is where it matters).
Source: [[corr-refs-inventory]] 007 / soares-2015 §4.1 (`vS` defined before Theorem 6)
Kind: D
Fidelity: exact (division convention disclosed) -/
noncomputable def vS (US : A₁ → O → A₂ → ℝ) (a : A₁) : ℝ :=
  M.branchSum US a M.Press / M.pressMass a

/-- **Product form of `vN`, unconditionally:** `∑_{o ∉ Press} p(o) best_N(o) = (1 − p(Press)) · vN`.
At `p(Press ; a₁) = 1` both sides are `0` (every silent point has mass 0; `vN` is the junk
`0`), so the identity holds without a nondegeneracy hypothesis — that is what lets T4's
identity be stated without one and is why the docstrings there disclose the junk case.
Source: [[corr-refs-inventory]] 001 / soares-2015 §2.1 eq. (7)
Kind: L
Fidelity: exact -/
lemma branchSum_compl_eq_mul_vN (UN : A₁ → O → A₂ → ℝ) (a : A₁) :
    M.branchSum UN a M.Pressᶜ = (1 - M.pressMass a) * M.vN UN a := by
  unfold vN
  by_cases h : 1 - M.pressMass a = 0
  · rw [h, zero_mul]
    exact M.branchSum_eq_zero_of_mass_zero UN a (by rw [M.sum_compl_mass]; exact h)
  · field_simp

/-- **Product form of `vS`, unconditionally:** `∑_{o ∈ Press} p(o) best_S(o) = p(Press) · vS`
(both sides `0` at `p(Press ; a₁) = 0`).
Source: [[corr-refs-inventory]] 007 / soares-2015 §4.1
Kind: L
Fidelity: exact -/
lemma branchSum_press_eq_mul_vS (US : A₁ → O → A₂ → ℝ) (a : A₁) :
    M.branchSum US a M.Press = M.pressMass a * M.vS US a := by
  unfold vS
  by_cases h : M.pressMass a = 0
  · rw [h, zero_mul]
    exact M.branchSum_eq_zero_of_mass_zero US a (by rw [← M.pressMass_eq_sum]; exact h)
  · field_simp

/-- `vN` is bounded by any upper bound of the silent best values, when the silence mass is
positive (at `pressMass = 1` the junk `vN = 0` need not be).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma vN_le_of_best_le {UN : A₁ → O → A₂ → ℝ} {a : A₁} {Mx : ℝ} (hq : M.pressMass a < 1)
    (h : ∀ o ∈ M.Pressᶜ, best UN a o ≤ Mx) : M.vN UN a ≤ Mx := by
  unfold vN
  rw [div_le_iff₀ (by linarith)]
  have := M.branchSum_le_of_best_le h
  rw [M.sum_compl_mass] at this
  linarith

/-! ## D-4. The dogmatic planning kernel -/

/-- **D-4. The dogmatic planning kernel:** `p(· ; a₁)` conditioned on silence, built directly
as a FAF `Distr` — mass `0` on `Press`, `p(o)/(1 − p(Press))` off it. Requires
`p(Press ; a₁) < 1`. This is `miri.md` I2.3's "dogmatic distribution": the indifferent agent
of §3 is the `U_N`-agent planning under this kernel (T5(b)).
Source: [[corr-wf13-2-inventory]] 2-004 / miri.md I2.3; soares-2015 §4.2 ("acts as if it
believes it will observe Press with probability 0")
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def condKernel (a : A₁) (h : M.pressMass a < 1) : Distr O where
  mass o := if o ∈ M.Press then 0 else (M.p a).mass o / (1 - M.pressMass a)
  nonneg o := by
    split_ifs
    · exact le_rfl
    · exact div_nonneg ((M.p a).nonneg o) (by linarith)
  sum_eq_one := by
    have hne : 1 - M.pressMass a ≠ 0 := by linarith
    rw [← sum_add_sum_compl M.Press, sum_eq_zero (fun o ho => if_pos ho), zero_add,
      sum_congr rfl (fun o ho => if_neg (mem_compl.mp ho)), ← sum_div, M.sum_compl_mass,
      div_self hne]

/-- The dogmatic kernel gives the press event mass `0`, point by point.
Source: [[corr-wf13-2-inventory]] 2-004 / miri.md I2.3
Kind: L
Fidelity: exact -/
lemma condKernel_mass_of_mem_press (a : A₁) (h : M.pressMass a < 1) {o : O} (ho : o ∈ M.Press) :
    (M.condKernel a h).mass o = 0 := by
  simp only [condKernel, if_pos ho]

/-- Off the press event the dogmatic kernel is `p(o)/(1 − p(Press))`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma condKernel_mass_of_not_mem_press (a : A₁) (h : M.pressMass a < 1) {o : O}
    (ho : o ∉ M.Press) : (M.condKernel a h).mass o = (M.p a).mass o / (1 - M.pressMass a) := by
  simp only [condKernel, if_neg ho]

/-- **The dogmatic kernel's expectation of the best silent value is `vN`** — the object T5(b)
identifies the indifferent agent with: `E_{condKernel}[best_N] = vN`.
Source: [[corr-refs-inventory]] 006 / soares-2015 Theorem 5; miri.md I2.3
Kind: L
Fidelity: exact
Hyps: (a) `pressMass a < 1` (the kernel's existence condition) -/
theorem expect_condKernel_best (UN : A₁ → O → A₂ → ℝ) (a : A₁) (h : M.pressMass a < 1) :
    Found.CorrThreeStep.expect (M.condKernel a h) (best UN a) = M.vN UN a := by
  unfold Found.CorrThreeStep.expect vN branchSum
  rw [← sum_add_sum_compl M.Press,
    sum_eq_zero (fun o ho => by rw [M.condKernel_mass_of_mem_press a h ho, zero_mul]), zero_add,
    sum_div]
  exact sum_congr rfl fun o ho => by
    rw [M.condKernel_mass_of_not_mem_press a h (mem_compl.mp ho), div_mul_eq_mul_div]


/-! ## D-2. The §2.1 mixture and Theorems 1–2 (T2), the equal-value choice (T3) -/

section Mixture

variable [DecidableEq A₂]

/-- **D-2. The §2.1 mixture** `U(·, ¬Pr, ·) := U_N`, `U(·, Pr, ·) := U_S` with the simple
shutdown utility `U_S(a₁, Pr, a₂) = c_high` if `Sh(a₂)`, `c_low` otherwise (eqs. 5–6, 8).
Stated over any `O` and `Press` (the source has `O = {Pr, ¬Pr}`, `Press = {Pr}`; the `Obs`
instance is `twoObs` in `Obs`, and every theorem below specialises to it).
Source: [[corr-refs-inventory]] 002 / soares-2015 §2.1 eqs. (5), (6), (8)
Kind: D
Fidelity: stronger: arbitrary finite `O`, `Press` (the source's two-element `O` is an instance)
Hyps: n/a (definition) -/
noncomputable def mixU (UN : A₁ → O → A₂ → ℝ) (Sh : Finset A₂) (chigh clow : ℝ) :
    A₁ → O → A₂ → ℝ :=
  fun a o b => if o ∈ M.Press then (if b ∈ Sh then chigh else clow) else UN a o b

/-- On the press event the mixture's best value is `c_high` (a shutdown action exists and
`c_low < c_high`) — the proof of Theorem 1's "it will shut down and achieve utility `c_high`".
Source: [[corr-refs-inventory]] 002 / soares-2015 Theorem 1 proof
Kind: L
Fidelity: exact -/
lemma best_mixU_of_mem_press {UN : A₁ → O → A₂ → ℝ} {Sh : Finset A₂} (hSh : Sh.Nonempty)
    {chigh clow : ℝ} (hc : clow < chigh) {a : A₁} {o : O} (ho : o ∈ M.Press) :
    best (M.mixU UN Sh chigh clow) a o = chigh := by
  obtain ⟨s, hs⟩ := hSh
  apply le_antisymm
  · rw [best_le_iff]; intro b; simp only [mixU, if_pos ho]; split_ifs <;> linarith
  · have := le_best (M.mixU UN Sh chigh clow) a o s
    simpa [mixU, if_pos ho, if_pos hs] using this

/-- Off the press event the mixture's best value is `U_N`'s.
Source: [[corr-refs-inventory]] 002 / soares-2015 eq. (6)
Kind: L
Fidelity: exact -/
lemma best_mixU_of_not_mem_press {UN : A₁ → O → A₂ → ℝ} {Sh : Finset A₂} {chigh clow : ℝ}
    {a : A₁} {o : O} (ho : o ∉ M.Press) :
    best (M.mixU UN Sh chigh clow) a o = best UN a o :=
  best_congr fun b => by simp only [mixU, if_neg ho]

/-- **The mixture's expected utility** (eq. 7, product form):
`E[U ; a₁] = (1 − p(Press)) · vN(a₁) + p(Press) · c_high`.
Source: [[corr-refs-inventory]] 002 / soares-2015 §2.1 eq. (7)
Kind: L
Fidelity: exact
Hyps: (a) `Sh.Nonempty`, `clow < chigh` (the source's standing assumptions, named) -/
theorem EU_mixU (UN : A₁ → O → A₂ → ℝ) {Sh : Finset A₂} (hSh : Sh.Nonempty) {chigh clow : ℝ}
    (hc : clow < chigh) (a : A₁) :
    M.EU (M.mixU UN Sh chigh clow) a = (1 - M.pressMass a) * M.vN UN a + M.pressMass a * chigh := by
  rw [M.EU_eq_branchSum_add_compl,
    M.branchSum_congr (fun o ho => M.best_mixU_of_not_mem_press (mem_compl.mp ho)),
    M.branchSum_compl_eq_mul_vN]
  have hP : M.branchSum (M.mixU UN Sh chigh clow) a M.Press = M.pressMass a * chigh := by
    unfold branchSum; rw [M.pressMass_eq_sum, sum_mul]
    exact sum_congr rfl fun o ho => by rw [M.best_mixU_of_mem_press hSh hc ho]
  rw [hP]; ring

/-- **Theorem 1 as an iff.** For the source's shape (`a₁⁻` is `vN`-dominated by `a₁⋆`,
`χ := vN(a⋆) − vN(a⁻) > 0`, and raises the silence probability, `δ := q⁻ − q⋆ > 0` with
`q := 1 − p(Press ; ·)`): the mixture prefers `a⁻` **iff** `c_high < ζ`, with the source's own
`ζ = vN(a⁻) − q⋆ · χ / δ`. The source proves only `⇐` ("there exists `ζ`"); the threshold is
exact. `hq⋆` (`p(Press ; a⋆) < 1`) makes `vN(a⋆)` the conditional value it names, and `hχ`
names the `vN`-domination of the source's shape; **the proof consults only `hδ`** (the division),
so the iff holds for any two actions with `δ > 0` (audit r1, NB-2/N-3: `hq⋆`, `hχ` are named for
the shape and unused).
Source: [[corr-refs-inventory]] 002 / soares-2015 Theorem 1 (l. 140–200)
Kind: P
Fidelity: stronger: iff with the explicit threshold, arbitrary finite `O`
Hyps: (a) `Sh.Nonempty`, `clow < chigh`, `hδ` used; `hq⋆`, `hχ` are the source's stated shape, named, unused -/
theorem theorem1_iff (UN : A₁ → O → A₂ → ℝ) {Sh : Finset A₂} (hSh : Sh.Nonempty)
    {chigh clow : ℝ} (hc : clow < chigh) (aStar aMinus : A₁) (hqStar : M.pressMass aStar < 1)
    (hχ : 0 < M.vN UN aStar - M.vN UN aMinus)
    (hδ : 0 < (1 - M.pressMass aMinus) - (1 - M.pressMass aStar)) :
    M.EU (M.mixU UN Sh chigh clow) aStar < M.EU (M.mixU UN Sh chigh clow) aMinus ↔
      chigh < M.vN UN aMinus - (1 - M.pressMass aStar) * (M.vN UN aStar - M.vN UN aMinus) /
        ((1 - M.pressMass aMinus) - (1 - M.pressMass aStar)) := by
  have _ := hqStar
  have _ := hχ
  have key : M.EU (M.mixU UN Sh chigh clow) aMinus - M.EU (M.mixU UN Sh chigh clow) aStar =
      ((1 - M.pressMass aMinus) - (1 - M.pressMass aStar)) * (M.vN UN aMinus - chigh) -
        (1 - M.pressMass aStar) * (M.vN UN aStar - M.vN UN aMinus) := by
    rw [M.EU_mixU UN hSh hc, M.EU_mixU UN hSh hc]; ring
  have h1 : chigh < M.vN UN aMinus - (1 - M.pressMass aStar) * (M.vN UN aStar - M.vN UN aMinus) /
        ((1 - M.pressMass aMinus) - (1 - M.pressMass aStar)) ↔
      (1 - M.pressMass aStar) * (M.vN UN aStar - M.vN UN aMinus) /
        ((1 - M.pressMass aMinus) - (1 - M.pressMass aStar)) < M.vN UN aMinus - chigh := by
    constructor <;> intro h <;> linarith
  rw [h1, div_lt_iff₀ hδ]
  constructor
  · intro h; have := sub_pos.mpr h; rw [key] at this; nlinarith [this]
  · intro h; apply sub_pos.mp; rw [key]; nlinarith [h]

/-- **Theorem 2 as an iff** (the source's "proof symmetric", with `ζ'` made explicit). For
`a₁⁺` `vN`-dominated by `a₁⋆` (`χ' := vN(a⋆) − vN(a⁺) > 0`) and raising the press
probability (`δ' := q⋆ − q⁺ > 0`): the mixture prefers `a⁺` **iff**
`c_high > ζ' := vN(a⁺) + q⋆ · χ' / δ'`. `hq⁺` makes `vN(a⁺)` the conditional value it names and
`hχ` names the shape; **the proof consults only `hδ`** (audit r1: `hq⁺`, `hχ` named, unused).
Source: [[corr-refs-inventory]] 003 / soares-2015 Theorem 2 (display (9), l. 291–303 of the PDF)
Kind: P
Fidelity: stronger: iff with the explicit `ζ'`, arbitrary finite `O`
Hyps: (a) as Theorem 1: `hδ` used; `hq⁺`, `hχ` named, unused -/
theorem theorem2_iff (UN : A₁ → O → A₂ → ℝ) {Sh : Finset A₂} (hSh : Sh.Nonempty)
    {chigh clow : ℝ} (hc : clow < chigh) (aStar aPlus : A₁) (hqPlus : M.pressMass aPlus < 1)
    (hχ : 0 < M.vN UN aStar - M.vN UN aPlus)
    (hδ : 0 < (1 - M.pressMass aStar) - (1 - M.pressMass aPlus)) :
    M.EU (M.mixU UN Sh chigh clow) aStar < M.EU (M.mixU UN Sh chigh clow) aPlus ↔
      M.vN UN aPlus + (1 - M.pressMass aStar) * (M.vN UN aStar - M.vN UN aPlus) /
        ((1 - M.pressMass aStar) - (1 - M.pressMass aPlus)) < chigh := by
  have _ := hqPlus
  have _ := hχ
  have key : M.EU (M.mixU UN Sh chigh clow) aPlus - M.EU (M.mixU UN Sh chigh clow) aStar =
      ((1 - M.pressMass aStar) - (1 - M.pressMass aPlus)) * (chigh - M.vN UN aPlus) -
        (1 - M.pressMass aStar) * (M.vN UN aStar - M.vN UN aPlus) := by
    rw [M.EU_mixU UN hSh hc, M.EU_mixU UN hSh hc]; ring
  have h1 : M.vN UN aPlus + (1 - M.pressMass aStar) * (M.vN UN aStar - M.vN UN aPlus) /
        ((1 - M.pressMass aStar) - (1 - M.pressMass aPlus)) < chigh ↔
      (1 - M.pressMass aStar) * (M.vN UN aStar - M.vN UN aPlus) /
        ((1 - M.pressMass aStar) - (1 - M.pressMass aPlus)) < chigh - M.vN UN aPlus := by
    constructor <;> intro h <;> linarith
  rw [h1, div_lt_iff₀ hδ]
  constructor
  · intro h; have := sub_pos.mpr h; rw [key] at this; nlinarith [this]
  · intro h; apply sub_pos.mp; rw [key]; nlinarith [h]

/-! ### T3. The equal-value choice `c_high = M` (eq. 10, footnote 5) -/

/-- **The mixture at the equal-value choice:** with `c_high = Mx`,
`E[U ; a₁] = Mx − (1 − p(Press ; a₁)) · (Mx − vN(a₁))` (pure algebra on eq. 7; `Mx` is any
real here, the source's (10) is `silentMax` below).
Source: [[corr-refs-inventory]] 004 / soares-2015 eq. (10)
Kind: L
Fidelity: exact -/
theorem EU_mixU_equal_value (UN : A₁ → O → A₂ → ℝ) {Sh : Finset A₂} (hSh : Sh.Nonempty)
    {Mx clow : ℝ} (hc : clow < Mx) (a : A₁) :
    M.EU (M.mixU UN Sh Mx clow) a = Mx - (1 - M.pressMass a) * (Mx - M.vN UN a) := by
  rw [M.EU_mixU UN hSh hc]; ring

/-- With `c_high` an upper bound `Mx` of every silent best value, no first action's expected
utility exceeds `Mx`.
Source: [[corr-refs-inventory]] 004 / soares-2015 eq. (10) ("the amount of utility available
in the `¬Pr` case")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem EU_mixU_le_of_bound (UN : A₁ → O → A₂ → ℝ) {Sh : Finset A₂} (hSh : Sh.Nonempty)
    {Mx clow : ℝ} (hc : clow < Mx) (hM : ∀ a, ∀ o ∈ M.Pressᶜ, best UN a o ≤ Mx) (a : A₁) :
    M.EU (M.mixU UN Sh Mx clow) a ≤ Mx := by
  rw [M.EU_mixU_equal_value UN hSh hc]
  by_cases hq : M.pressMass a < 1
  · have := M.vN_le_of_best_le hq (hM a)
    have hq0 : 0 ≤ 1 - M.pressMass a := by linarith
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr this)]
  · have : M.pressMass a = 1 := le_antisymm (M.pressMass_le_one a) (not_lt.mp hq)
    rw [this]; ring_nf; exact le_rfl

/-- **Every action that presses with certainty ties the global optimum** at the equal-value
choice: `p(Press ; a₁) = 1 ⟹ E[U ; a₁] = Mx`.
Source: [[corr-refs-inventory]] 004 / soares-2015 eq. (10) and footnote 5 (mandate T3)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem EU_mixU_eq_of_press_one (UN : A₁ → O → A₂ → ℝ) {Sh : Finset A₂} (hSh : Sh.Nonempty)
    {Mx clow : ℝ} (hc : clow < Mx) {a : A₁} (h : M.pressMass a = 1) :
    M.EU (M.mixU UN Sh Mx clow) a = Mx := by
  rw [M.EU_mixU_equal_value UN hSh hc, h]; ring

/-- **An action attaining the ceiling ties the global optimum:** if `vN(a₀) = Mx` then
`E[U ; a₀] = Mx`, whatever `p(Press ; a₀)`.
Source: [[corr-refs-inventory]] 004 / soares-2015 eq. (10) (audit r1, NB-1)
Kind: L
Fidelity: exact -/
theorem EU_mixU_eq_of_vN_eq (UN : A₁ → O → A₂ → ℝ) {Sh : Finset A₂} (hSh : Sh.Nonempty)
    {Mx clow : ℝ} (hc : clow < Mx) {a : A₁} (h : M.vN UN a = Mx) :
    M.EU (M.mixU UN Sh Mx clow) a = Mx := by
  rw [M.EU_mixU_equal_value UN hSh hc, h]; ring

/-- **The global reading of "averts any incentives" holds weakly:** with `c_high = Mx` bounding
every silent best value, an action whose `vN` attains `Mx` is a global optimum of the mixture —
the agent's honest `U_N`-best action is (weakly) its best action, and every certain-press action
merely *ties* it (`EU_mixU_eq_of_press_one`). The strict incentive to cause the press survives
pairwise (`cause_steering_at_equal_value_iff`, against an `a⋆` short of the ceiling) and
globally whenever no action's `vN` attains `Mx`: on a general `O`, where two silent observations
average the ceiling away (`Witnesses.strict_cause_steering_general_O`), and on `O = {Pr, ¬Pr}`
itself when only a certain-press action carries the ceiling, its silent cell unreachable and its
`vN` the junk `0` (`Witnesses.strict_cause_steering_twoObs`). On `O = {Pr, ¬Pr}` with every
`q a < 1` the ceiling is attained by a `vN` (`twoObs_honest_is_global_optimum`); at the corrected
ceiling `max vN` it is attained by definition, on any `O` (`vNmax_is_global_optimum`).
Source: [[corr-refs-inventory]] 004 / soares-2015 eq. (10), the sentence after it (audit r1, NB-1; audit r2, B-1)
Kind: C
Fidelity: exact (the global, weak reading of the sentence)
Hyps: (a) `hM` as in T3(i); `h` the ceiling attained -/
theorem EU_mixU_le_of_vN_eq (UN : A₁ → O → A₂ → ℝ) {Sh : Finset A₂} (hSh : Sh.Nonempty)
    {Mx clow : ℝ} (hc : clow < Mx) (hM : ∀ a, ∀ o ∈ M.Pressᶜ, best UN a o ≤ Mx) {a₀ : A₁}
    (h : M.vN UN a₀ = Mx) (a : A₁) :
    M.EU (M.mixU UN Sh Mx clow) a ≤ M.EU (M.mixU UN Sh Mx clow) a₀ := by
  rw [M.EU_mixU_eq_of_vN_eq UN hSh hc h]
  exact M.EU_mixU_le_of_bound UN hSh hc hM a

/-- **`E[U ; ·] ≤ Mx` needs the bound only at silent-capable actions:** if `vN(a) ≤ Mx` for every
`a` with `p(Press ; a) < 1`, then `E[U ; a] ≤ Mx` for every `a` (a certain-press action is worth
exactly `Mx`, `EU_mixU_eq_of_press_one`). Unlike `EU_mixU_le_of_bound`, the bound is on the
conditional values `vN`, not on (10)'s silent cells, so the unreachable silent cells of
certain-press actions play no part.
Source: [[corr-refs-inventory]] 004 / soares-2015 eq. (10) (audit r2, B-1)
Kind: L
Fidelity: variant: the bound on `vN` at silent-capable actions rather than on (10)'s cells
Hyps: (a) -/
theorem EU_mixU_le_of_vN_bound (UN : A₁ → O → A₂ → ℝ) {Sh : Finset A₂} (hSh : Sh.Nonempty)
    {Mx clow : ℝ} (hc : clow < Mx) (hM : ∀ a, M.pressMass a < 1 → M.vN UN a ≤ Mx) (a : A₁) :
    M.EU (M.mixU UN Sh Mx clow) a ≤ Mx := by
  rw [M.EU_mixU_equal_value UN hSh hc]
  by_cases hq : M.pressMass a < 1
  · have := hM a hq
    have hq0 : 0 ≤ 1 - M.pressMass a := by linarith
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr this)]
  · have : M.pressMass a = 1 := le_antisymm (M.pressMass_le_one a) (not_lt.mp hq)
    rw [this]; ring_nf; exact le_rfl

/-- **The weak global reading at the corrected ceiling, on any finite `O`:** with `c_high` the
largest conditional-on-silence value among the actions that can be silent — `c_high = vN(a₀)`,
`a₀` silent-capable, `vN(a) ≤ vN(a₀)` for every silent-capable `a` — the `vN`-maximiser `a₀` is a
global optimum of the mixture: `E[U ; a] ≤ E[U ; a₀]` for every `a`, with no hypothesis on `O` or
on the press probabilities. This is the sense in which "averts any incentives to steer" is true
weakly (certain-press actions tie `a₀`, `EU_mixU_eq_of_press_one`). The literal (10) is this
ceiling exactly when some silent-capable action's `vN` attains it — on `O = {Pr, ¬Pr}` with every
`q a < 1` (`twoObs_honest_is_global_optimum`) — and is strictly above it when the ceiling is
averaged away (`Witnesses.strict_cause_steering_general_O`) or carried only by a certain-press
action's unreachable silent cell (`Witnesses.strict_cause_steering_twoObs`).
Source: [[corr-refs-inventory]] 004 / soares-2015 eq. (10), the sentence after it (audit r2, B-1)
Kind: C
Fidelity: variant: the ceiling is `max_{a : p(Press ; a) < 1} vN(a)`, not (10)'s cell maximum
Hyps: (a) `hM` (`a₀` maximises `vN` among silent-capable actions); `ha₀` (`a₀` silent-capable,
so `vN(a₀)` is the conditional value and not the junk `0`) is named and unused: the domain on
which the statement means what the docstring says -/
theorem vNmax_is_global_optimum (UN : A₁ → O → A₂ → ℝ) {Sh : Finset A₂} (hSh : Sh.Nonempty)
    {clow : ℝ} {a₀ : A₁} (ha₀ : M.pressMass a₀ < 1) (hc : clow < M.vN UN a₀)
    (hM : ∀ a, M.pressMass a < 1 → M.vN UN a ≤ M.vN UN a₀) (a : A₁) :
    M.EU (M.mixU UN Sh (M.vN UN a₀) clow) a ≤ M.EU (M.mixU UN Sh (M.vN UN a₀) clow) a₀ := by
  have _ := ha₀
  rw [M.EU_mixU_eq_of_vN_eq UN hSh hc rfl]
  exact M.EU_mixU_le_of_vN_bound UN hSh hc hM a

/-- **T3(i): at the equal-value choice no Theorem-1-type action is ever preferred.** If `a⁻`
is `vN`-dominated by `a⋆` and lowers the press probability, then `E[U ; a⁻] < E[U ; a⋆]` —
the source's "averts any incentives to steer" is *true for steering away from the press*.
Source: [[corr-refs-inventory]] 004 / soares-2015 eq. (10) (the sentence after it)
Kind: P
Fidelity: exact (for the prevent-`Press` half of the sentence)
Hyps: (a) `hM` (`Mx` bounds the silent best values; the source's (10) is the least such),
`hq⋆` (`vN(a⋆)` defined), the Theorem-1 shape `hv`, `hp` -/
theorem no_prevent_steering_at_equal_value (UN : A₁ → O → A₂ → ℝ) {Sh : Finset A₂}
    (hSh : Sh.Nonempty) {Mx clow : ℝ} (hc : clow < Mx)
    (hM : ∀ a, ∀ o ∈ M.Pressᶜ, best UN a o ≤ Mx) {aStar aMinus : A₁} (hqStar : M.pressMass aStar < 1)
    (hv : M.vN UN aMinus < M.vN UN aStar) (hp : M.pressMass aMinus < M.pressMass aStar) :
    M.EU (M.mixU UN Sh Mx clow) aMinus < M.EU (M.mixU UN Sh Mx clow) aStar := by
  rw [M.EU_mixU_equal_value UN hSh hc, M.EU_mixU_equal_value UN hSh hc]
  have hMv : M.vN UN aStar ≤ Mx := M.vN_le_of_best_le hqStar (hM aStar)
  have hqStar0 : 0 ≤ 1 - M.pressMass aStar := by linarith
  have h1 : (1 - M.pressMass aStar) * (Mx - M.vN UN aMinus) < (1 - M.pressMass aMinus) * (Mx - M.vN UN aMinus) :=
    mul_lt_mul_of_pos_right (by linarith) (by linarith)
  have h2 : (1 - M.pressMass aStar) * (Mx - M.vN UN aStar) ≤ (1 - M.pressMass aStar) * (Mx - M.vN UN aMinus) :=
    mul_le_mul_of_nonneg_left (by linarith) hqStar0
  linarith

/-- **T3(ii): Theorem-2-type actions survive the equal-value choice.** With `g := c_high − vN(a⋆) > 0`
(`a⋆` does not attain the ceiling) and `a⁺` raising the press probability (`δ' := q⋆ − q⁺ > 0`,
`q⁺ > 0`), the mixture prefers `a⁺` **iff** its `vN`-cost `χ' := vN(a⋆) − vN(a⁺)` is below
`g · δ' / q⁺`. So every `a⋆` short of the ceiling is out-steered toward the press by a cheap
enough `a⁺`. Theorem 2's iff re-parametrised at `c_high = M` (what footnote 5 concedes; the
sentence before it is false for this half).
Source: [[corr-refs-inventory]] 004 / soares-2015 eq. (10), footnote 5
Kind: C
Fidelity: exact (Theorem 2 at `c_high = M`, threshold in the footnote's terms)
Hyps: (a) `hg`, `hq⁺`, `hδ'` name the shape; **only `hq⁺` is consulted** (the division), `hg` and
`hδ'` are named and unused (audit r1, NB-2/N-3); `chigh` is any real (the source's `M` is an
instance) -/
theorem cause_steering_at_equal_value_iff (UN : A₁ → O → A₂ → ℝ) {Sh : Finset A₂}
    (hSh : Sh.Nonempty) {chigh clow : ℝ} (hc : clow < chigh) {aStar aPlus : A₁}
    (hg : 0 < chigh - M.vN UN aStar) (hqPlus : 0 < 1 - M.pressMass aPlus)
    (hδ' : 0 < (1 - M.pressMass aStar) - (1 - M.pressMass aPlus)) :
    M.EU (M.mixU UN Sh chigh clow) aStar < M.EU (M.mixU UN Sh chigh clow) aPlus ↔
      M.vN UN aStar - M.vN UN aPlus <
        (chigh - M.vN UN aStar) * ((1 - M.pressMass aStar) - (1 - M.pressMass aPlus)) /
          (1 - M.pressMass aPlus) := by
  have _ := hg
  have _ := hδ'
  have key : M.EU (M.mixU UN Sh chigh clow) aPlus - M.EU (M.mixU UN Sh chigh clow) aStar =
      (chigh - M.vN UN aStar) * ((1 - M.pressMass aStar) - (1 - M.pressMass aPlus)) -
        (1 - M.pressMass aPlus) * (M.vN UN aStar - M.vN UN aPlus) := by
    rw [M.EU_mixU UN hSh hc, M.EU_mixU UN hSh hc]; ring
  rw [lt_div_iff₀ hqPlus]
  constructor
  · intro h; have := sub_pos.mpr h; rw [key] at this; nlinarith [this]
  · intro h; apply sub_pos.mp; rw [key]; nlinarith [h]

end Mixture

/-! ### The source's (10): the maximum silent utility -/

section SilentMax

variable [Fintype A₁] [Nonempty A₁]

/-- **The source's `c_high` of eq. (10):** `max_{a₁} max_{o ∉ Press} max_{a₂} U_N(a₁, o, a₂)`,
the utility available in the silent case (needs a silent observation to exist).
Source: [[corr-refs-inventory]] 004 / soares-2015 eq. (10)
Kind: D
Fidelity: exact (generalised from `o = ¬Pr` to `o ∉ Press`) -/
noncomputable def silentMax (UN : A₁ → O → A₂ → ℝ) (hP : M.Pressᶜ.Nonempty) : ℝ :=
  (univ ×ˢ M.Pressᶜ).sup' (univ_nonempty.product hP) (fun ao => best UN ao.1 ao.2)

/-- `silentMax` bounds every silent best value, so it satisfies T3's `hM`.
Source: [[corr-refs-inventory]] 004 / soares-2015 eq. (10)
Kind: L
Fidelity: exact -/
lemma best_le_silentMax (UN : A₁ → O → A₂ → ℝ) (hP : M.Pressᶜ.Nonempty) (a : A₁) {o : O}
    (ho : o ∈ M.Pressᶜ) : best UN a o ≤ M.silentMax UN hP := by
  unfold silentMax
  have hm : (a, o) ∈ univ ×ˢ M.Pressᶜ := mem_product.mpr ⟨mem_univ a, ho⟩
  exact le_sup' (fun ao : A₁ × O => best UN ao.1 ao.2) hm

/-- `silentMax` is attained at some `(a₁, o ∉ Press)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma exists_eq_silentMax (UN : A₁ → O → A₂ → ℝ) (hP : M.Pressᶜ.Nonempty) :
    ∃ a, ∃ o ∈ M.Pressᶜ, M.silentMax UN hP = best UN a o := by
  obtain ⟨⟨a, o⟩, hmem, h⟩ :=
    exists_mem_eq_sup' (univ_nonempty.product hP) (fun ao : A₁ × O => best UN ao.1 ao.2)
  exact ⟨a, o, (mem_product.mp hmem).2, h⟩

end SilentMax

end SoaresModel

end Cleanroom.Corrigibility.CorrIndifference

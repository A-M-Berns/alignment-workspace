import Cleanroom.Corrigibility.CorrValueChange.Good

/-!
# corr-value-change — the fine Kolmogorov picture and Claim 4 (T6(f), T10(a)–(c))

Source: [[value-change-as-epistemic-update]] §2.4 Claim 4, §3.1–3.3. With the joint
`P` on `Ω × Θ × I`: the current effective utility `Ū_a(ω) = E_P[u_{θ,a} ∣ ω]`, the **fine** current
utility `Ū^{cur}_a(ω, i) = E_P[u_{θ,a} ∣ ω, E_i]` on `Ω × I`, and the installed `Ū^{(i)}_a(ω) =
E_{Q_i}[U_a ∣ ω]`. The Pythagorean identity for conditional expectations gives Claim 4; under (R⁺)
the installed utility is the fine current utility on the realized slice (T10(a)), and the tower
identity (M^U) is T10(c).
-/

namespace Cleanroom.Corrigibility.CorrValueChange

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω Θ I A : Type} [Fintype Ω] [Fintype Θ] [Fintype I] [Fintype A] [DecidableEq Ω]
  [DecidableEq Θ] [DecidableEq I] [DecidableEq A]

/-- `P(ω, i) = ∑_θ P(ω, θ, i)`.
Source: [[value-change-as-epistemic-update]] §3.1
Kind: D
Fidelity: exact -/
def Pωi (J : Joint (Ω × Θ) I) (ω : Ω) (i : I) : ℝ := ∑ θ, J.P (ω, θ) i

/-- `P(ω) = ∑_i P(ω, i)`.
Source: [[value-change-as-epistemic-update]] §3.1
Kind: D
Fidelity: exact -/
def Pω (J : Joint (Ω × Θ) I) (ω : Ω) : ℝ := ∑ i, Pωi J ω i

/-- The **fine current utility** `Ū^{cur}_a(ω, i) = E_P[u_{θ,a} ∣ ω, E_i]` (junk at `P(ω, i) = 0`).
Source: [[value-change-as-epistemic-update]] §3.1 (third row of the table), §3.2
Kind: D
Fidelity: exact on `P(ω, i) > 0` -/
def Ucur (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (a : A) (ω : Ω) (i : I) : ℝ :=
  (∑ θ, J.P (ω, θ) i * u θ a ω) / Pωi J ω i

/-- The **current effective utility** `Ū_a(ω) = E_P[u_{θ,a} ∣ ω]` (junk at `P(ω) = 0`).
Source: [[value-change-as-epistemic-update]] §2.4 Claim 4 (`Ū_a(ω) = E_P[u_{θ,a} ∣ ω]`)
Kind: D
Fidelity: exact on `P(ω) > 0` -/
def Ubar (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (a : A) (ω : Ω) : ℝ :=
  (∑ i, ∑ θ, J.P (ω, θ) i * u θ a ω) / Pω J ω

/-- The mean-square distance of a representation `R(ω, i)` from the value variable `u_{θ,a}(ω)`,
under the joint: `∑_{ω,θ,i} P(ω,θ,i) (R(ω, i) − u_{θ,a}(ω))²`.
Source: [[value-change-as-epistemic-update]] §2.4 Claim 4 (the expectation "runs over `ω`, `θ`
and `i`")
Kind: D
Fidelity: exact -/
def msErr (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (a : A) (R : Ω → I → ℝ) : ℝ :=
  ∑ ω, ∑ i, ∑ θ, J.P (ω, θ) i * (R ω i - u θ a ω) ^ 2

/-- `P(ω, i) ≥ 0`, and `P(ω, θ, i) = 0` when `P(ω, i) = 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Pωi_nonneg (J : Joint (Ω × Θ) I) (ω : Ω) (i : I) : 0 ≤ Pωi J ω i :=
  sum_nonneg fun θ _ => J.nonneg _ _

/-- `P(ω,θ,i) = 0` where `P(ω, i) = 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem P_eq_zero_of_Pωi_eq_zero (J : Joint (Ω × Θ) I) {ω : Ω} {i : I} (h : Pωi J ω i = 0)
    (θ : Θ) : J.P (ω, θ) i = 0 :=
  (sum_eq_zero_iff_of_nonneg fun θ _ => J.nonneg (ω, θ) i).1 h θ (mem_univ θ)

/-- `P(ω) ≥ 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Pω_nonneg (J : Joint (Ω × Θ) I) (ω : Ω) : 0 ≤ Pω J ω :=
  sum_nonneg fun i _ => Pωi_nonneg J ω i

/-- `P(ω, i) = 0` where `P(ω) = 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Pωi_eq_zero_of_Pω_eq_zero (J : Joint (Ω × Θ) I) {ω : Ω} (h : Pω J ω = 0) (i : I) :
    Pωi J ω i = 0 :=
  (sum_eq_zero_iff_of_nonneg fun i _ => Pωi_nonneg J ω i).1 h i (mem_univ i)

/-- The defining identity of the fine utility in product form:
`∑_θ P(ω,θ,i) (Ū^{cur}_a(ω,i) − u_{θ,a}(ω)) = 0` (the conditional mean of the residual is zero;
trivially also when `P(ω, i) = 0`).
Source: [[value-change-as-epistemic-update]] §2.4 Claim 4 proof ("has conditional mean zero
given `(ω, E_i)`")
Kind: L
Fidelity: exact -/
theorem Ucur_residual (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (a : A) (ω : Ω) (i : I) :
    ∑ θ, J.P (ω, θ) i * (Ucur J u a ω i - u θ a ω) = 0 := by
  rcases (Pωi_nonneg J ω i).lt_or_eq with hpos | hzero
  · have : ∑ θ, J.P (ω, θ) i * (Ucur J u a ω i - u θ a ω) =
        Pωi J ω i * Ucur J u a ω i - ∑ θ, J.P (ω, θ) i * u θ a ω := by
      unfold Pωi; rw [sum_mul, ← sum_sub_distrib]
      refine sum_congr rfl fun θ _ => ?_; ring
    rw [this]; unfold Ucur; field_simp; ring
  · exact sum_eq_zero fun θ _ => by rw [P_eq_zero_of_Pωi_eq_zero J hzero.symm θ, zero_mul]

/-- **T10(c), (M^U) no expected net utility change / the tower property**: at `P(ω) > 0`,
`∑_i P(E_i ∣ ω) Ū^{cur}_a(ω, i) = Ū_a(ω)`, in product form `∑_i P(ω,i) Ū^{cur}_a(ω,i) = P(ω) Ū_a(ω)`.
Source: [[value-change-as-epistemic-update]] §3.3 ((M^U)), §2.4 Claim 4 proof ("`Ū_a =
E_P[Ū^{(i)}_a ∣ ω]` by the tower property")
Kind: P
Fidelity: exact
Hyps: (a) none for the product form; `0 < P(ω)` for the division form -/
theorem tower_Ucur (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (a : A) (ω : Ω) :
    ∑ i, Pωi J ω i * Ucur J u a ω i = Pω J ω * Ubar J u a ω := by
  have h1 : ∀ i, Pωi J ω i * Ucur J u a ω i = ∑ θ, J.P (ω, θ) i * u θ a ω := by
    intro i
    rcases (Pωi_nonneg J ω i).lt_or_eq with hpos | hzero
    · unfold Ucur; field_simp
    · rw [← hzero, zero_mul]
      exact (sum_eq_zero fun θ _ => by rw [P_eq_zero_of_Pωi_eq_zero J hzero.symm θ, zero_mul]).symm
  simp_rw [h1]
  rcases (Pω_nonneg J ω).lt_or_eq with hpos | hzero
  · unfold Ubar; field_simp
  · rw [← hzero, zero_mul]
    exact sum_eq_zero fun i _ => sum_eq_zero fun θ _ => by
      rw [P_eq_zero_of_Pωi_eq_zero J (Pωi_eq_zero_of_Pω_eq_zero J hzero.symm i) θ, zero_mul]

/-- (M^U) in the division form.
Source: [[value-change-as-epistemic-update]] §3.3
Kind: L
Fidelity: exact
Hyps: (a) `0 < P(ω)` -/
theorem M_U (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (a : A) (ω : Ω) (h : 0 < Pω J ω) :
    ∑ i, (Pωi J ω i / Pω J ω) * Ucur J u a ω i = Ubar J u a ω := by
  have e : ∀ i, Pωi J ω i / Pω J ω * Ucur J u a ω i = (Pωi J ω i * Ucur J u a ω i) / Pω J ω :=
    fun i => by ring
  simp_rw [e]
  rw [← sum_div, tower_Ucur]; field_simp

/-- **The Pythagorean identity**: `E[(Ū_a − u)²] = E[(Ū_a − Ū^{cur}_a)²] + E[(Ū^{cur}_a − u)²]`, the
cross term vanishing because `Ū_a − Ū^{cur}_a` is a function of `(ω, i)` and the residual has
conditional mean zero. Holds for every joint (no reflection needed): it is a fact about the
conditional expectations `Ū`, `Ū^{cur}` of the joint.
Source: [[value-change-as-epistemic-update]] §2.4 Claim 4 proof
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem pythagoras (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (a : A) :
    msErr J u a (fun ω _ => Ubar J u a ω) =
      (∑ ω, ∑ i, ∑ θ, J.P (ω, θ) i * (Ubar J u a ω - Ucur J u a ω i) ^ 2) +
        msErr J u a (Ucur J u a) := by
  unfold msErr
  rw [← sum_add_distrib]
  refine sum_congr rfl fun ω _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  have hcross : ∑ θ, J.P (ω, θ) i * ((Ubar J u a ω - Ucur J u a ω i) * (Ucur J u a ω i - u θ a ω))
      = 0 := by
    have : ∀ θ, J.P (ω, θ) i * ((Ubar J u a ω - Ucur J u a ω i) * (Ucur J u a ω i - u θ a ω)) =
        (Ubar J u a ω - Ucur J u a ω i) * (J.P (ω, θ) i * (Ucur J u a ω i - u θ a ω)) := by
      intro θ; ring
    simp_rw [this]
    rw [← mul_sum, Ucur_residual, mul_zero]
  have : ∀ θ, J.P (ω, θ) i * (Ubar J u a ω - u θ a ω) ^ 2 =
      J.P (ω, θ) i * (Ubar J u a ω - Ucur J u a ω i) ^ 2 + J.P (ω, θ) i * (Ucur J u a ω i - u θ a ω) ^ 2
        + 2 * (J.P (ω, θ) i * ((Ubar J u a ω - Ucur J u a ω i) * (Ucur J u a ω i - u θ a ω))) := by
    intro θ; ring
  simp_rw [this]
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, hcross, mul_zero, add_zero]

/-- The fine current utility is a better representation than the current one: Claim 4 for the
joint's own conditional expectations, `E[(Ū^{cur}_a − u)²] ≤ E[(Ū_a − u)²]`.
Source: [[value-change-as-epistemic-update]] §2.4 Claim 4
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem msErr_Ucur_le (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (a : A) :
    msErr J u a (Ucur J u a) ≤ msErr J u a (fun ω _ => Ubar J u a ω) := by
  rw [pythagoras]
  have : 0 ≤ ∑ ω, ∑ i, ∑ θ, J.P (ω, θ) i * (Ubar J u a ω - Ucur J u a ω i) ^ 2 :=
    sum_nonneg fun ω _ => sum_nonneg fun i _ => sum_nonneg fun θ _ =>
      mul_nonneg (J.nonneg _ _) (sq_nonneg _)
  linarith

/-- **S2, the equality case**: `E[(Ū^{cur}_a − u)²] = E[(Ū_a − u)²]` iff `Ū^{cur}_a(ω, i) = Ū_a(ω)` at
every `(ω, i)` of positive probability — iff the modification carries no information about the
conditional mean of `u_{θ,a}` given `ω` (which is what "carries no information about `u_{θ,a}`"
can mean for a mean-square statement; independence of `i` from `u_{θ,a}` given `ω` is sufficient,
not necessary).
Source: [[value-change-as-epistemic-update]] §2.4 Claim 4 ("Equality holds iff the modification
carries no information about `u_{θ,a}`")
Kind: P
Fidelity: variant: "no information" made precise as equality of conditional means
Hyps: (a) none -/
theorem msErr_eq_iff (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (a : A) :
    msErr J u a (Ucur J u a) = msErr J u a (fun ω _ => Ubar J u a ω) ↔
      ∀ ω i, 0 < Pωi J ω i → Ucur J u a ω i = Ubar J u a ω := by
  rw [pythagoras]
  have hterm : ∀ ω i, ∑ θ, J.P (ω, θ) i * (Ubar J u a ω - Ucur J u a ω i) ^ 2 =
      Pωi J ω i * (Ubar J u a ω - Ucur J u a ω i) ^ 2 := by
    intro ω i; unfold Pωi; rw [sum_mul]
  simp_rw [hterm]
  have hnn : ∀ ω ∈ (univ : Finset Ω), 0 ≤ ∑ i, Pωi J ω i * (Ubar J u a ω - Ucur J u a ω i) ^ 2 :=
    fun ω _ => sum_nonneg fun i _ => mul_nonneg (Pωi_nonneg J ω i) (sq_nonneg _)
  have hnn' : ∀ ω, ∀ i ∈ (univ : Finset I), 0 ≤ Pωi J ω i * (Ubar J u a ω - Ucur J u a ω i) ^ 2 :=
    fun ω i _ => mul_nonneg (Pωi_nonneg J ω i) (sq_nonneg _)
  constructor
  · intro h
    have h0 : ∑ ω, ∑ i, Pωi J ω i * (Ubar J u a ω - Ucur J u a ω i) ^ 2 = 0 := by linarith
    intro ω i hpos
    have h1 := (sum_eq_zero_iff_of_nonneg hnn).1 h0 ω (mem_univ ω)
    have h2 := (sum_eq_zero_iff_of_nonneg (hnn' ω)).1 h1 i (mem_univ i)
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hpos.ne'
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h3
      linarith
  · intro h
    have h0 : ∑ ω, ∑ i, Pωi J ω i * (Ubar J u a ω - Ucur J u a ω i) ^ 2 = 0 := by
      apply sum_eq_zero; intro ω _; apply sum_eq_zero; intro i _
      rcases (Pωi_nonneg J ω i).lt_or_eq with hpos | hzero
      · rw [h ω i hpos, sub_self]; ring
      · rw [← hzero, zero_mul]
    linarith

/-! ## The installed representation under (R⁺) -/

/-- **T10(a), the installed utility is the fine current utility on the realized slice**: under
(R⁺), at `P(ω, i) > 0`, `Ū^{(i)}_a(ω) := E_{Q_i}[U_a ∣ ω] = E_P[U_a ∣ ω, E_i] = Ū^{cur}_a(ω, i)`.
Source: [[value-change-as-epistemic-update]] §3.2 (the display `Ū^{(i)}_a(ω) = … = Ū^{cur}_a(ω,i)`)
Kind: P
Fidelity: exact
Hyps: (a) `h : Reflection`, `0 < P(ω, i)` -/
theorem fine_utility_eq {J : Joint (Ω × Θ) I} {Q : Installed (Ω × Θ) I} (h : Reflection J Q)
    (u : Θ → A → Ω → ℝ) (a : A) (ω : Ω) (i : I) (hpos : 0 < Pωi J ω i) :
    installedEffU Q u i a ω = Ucur J u a ω i := by
  have hπ : 0 < J.π i := by
    rcases (J.π_nonneg i).lt_or_eq with hp | hz
    · exact hp
    · exfalso
      have : Pωi J ω i = 0 := sum_eq_zero fun θ _ => J.P_eq_zero_of_π_eq_zero hz.symm _
      linarith
  have hQ : 0 < ∑ θ, Q.Q i (ω, θ) := by
    have : Pωi J ω i = J.π i * ∑ θ, Q.Q i (ω, θ) := by
      unfold Pωi; rw [mul_sum]; exact sum_congr rfl fun θ _ => h i hπ (ω, θ)
    rw [this] at hpos
    by_contra hneg
    have : ∑ θ, Q.Q i (ω, θ) ≤ 0 := not_lt.1 hneg
    nlinarith
  unfold installedEffU Ucur Pωi
  have e1 : ∀ θ, J.P (ω, θ) i = J.π i * Q.Q i (ω, θ) := fun θ => h i hπ (ω, θ)
  simp_rw [e1]
  rw [sum_div]
  refine sum_congr rfl fun θ _ => ?_
  rw [← mul_sum]
  field_simp

/-- **Claim 4, the representation improves**: under (R⁺), for every act,
`E[(Ū^{(i)}_a − u_{θ,a})²] ≤ E[(Ū_a − u_{θ,a})²]`, with `Ū^{(i)}_a(ω) = E_{Q_i}[U_a ∣ ω]` the utility
the modified agent acts on. (By `fine_utility_eq` the installed representation coincides with the
fine current utility wherever the joint has mass, so its error is `msErr … Ucur`.)
Source: [[value-change-as-epistemic-update]] §2.4 Claim 4
Kind: P
Fidelity: exact
Hyps: (a) `h : Reflection` -/
theorem representation_improves {J : Joint (Ω × Θ) I} {Q : Installed (Ω × Θ) I}
    (h : Reflection J Q) (u : Θ → A → Ω → ℝ) (a : A) :
    msErr J u a (fun ω i => installedEffU Q u i a ω) ≤ msErr J u a (fun ω _ => Ubar J u a ω) := by
  have heq : msErr J u a (fun ω i => installedEffU Q u i a ω) = msErr J u a (Ucur J u a) := by
    unfold msErr
    refine sum_congr rfl fun ω _ => sum_congr rfl fun i _ => ?_
    dsimp only
    rcases (Pωi_nonneg J ω i).lt_or_eq with hpos | hzero
    · rw [fine_utility_eq h u a ω i hpos]
    · refine sum_congr rfl fun θ _ => ?_
      rw [P_eq_zero_of_Pωi_eq_zero J hzero.symm θ, zero_mul, zero_mul]
  rw [heq]; exact msErr_Ucur_le J u a

/-- **S2 under (R⁺)**: equality in Claim 4 iff the installed utility equals the current one at
every `(ω, i)` of positive probability.
Source: [[value-change-as-epistemic-update]] §2.4 Claim 4 (equality clause)
Kind: C
Fidelity: variant (as `msErr_eq_iff`)
Hyps: (a) `h : Reflection` -/
theorem representation_eq_iff {J : Joint (Ω × Θ) I} {Q : Installed (Ω × Θ) I}
    (h : Reflection J Q) (u : Θ → A → Ω → ℝ) (a : A) :
    msErr J u a (fun ω i => installedEffU Q u i a ω) = msErr J u a (fun ω _ => Ubar J u a ω) ↔
      ∀ ω i, 0 < Pωi J ω i → installedEffU Q u i a ω = Ubar J u a ω := by
  have heq : msErr J u a (fun ω i => installedEffU Q u i a ω) = msErr J u a (Ucur J u a) := by
    unfold msErr
    refine sum_congr rfl fun ω _ => sum_congr rfl fun i _ => ?_
    dsimp only
    rcases (Pωi_nonneg J ω i).lt_or_eq with hpos | hzero
    · rw [fine_utility_eq h u a ω i hpos]
    · refine sum_congr rfl fun θ _ => ?_
      rw [P_eq_zero_of_Pωi_eq_zero J hzero.symm θ, zero_mul, zero_mul]
  rw [heq, msErr_eq_iff]
  constructor
  · intro hc ω i hpos; rw [fine_utility_eq h u a ω i hpos]; exact hc ω i hpos
  · intro hc ω i hpos; rw [← fine_utility_eq h u a ω i hpos]; exact hc ω i hpos

/-- **T10(b), the Gandhi agent and the corrigible agent have the same coarse utility**: the
`i`-flat extension `(ω, i) ↦ Ū_a(ω)` and the fine extension `Ū^{cur}_a` have the same `i`-average
at every `ω` of positive probability (both equal `Ū_a(ω)`), by (M^U). The two agents differ only
on the algebra containing the modification events. This is the tower identity `M_U` written in
the shape of §3.3's sentence (the right-hand side is `Ū_a(ω) · ∑_i P(ω,i)/P(ω) = Ū_a(ω)`): the two
"models" are the two utility extensions `Ū^{cur}` and the `i`-flat `Ū` of one joint, which is what
§3.3 compares.
Source: [[value-change-as-epistemic-update]] §3.3 ("The two agents have the same coarse
description")
Kind: L (`M_U` restated; audit r2 N3)
Fidelity: exact
Hyps: (a) `0 < P(ω)` -/
theorem gandhi_corrigible_same_coarse (J : Joint (Ω × Θ) I) (u : Θ → A → Ω → ℝ) (a : A) (ω : Ω)
    (h : 0 < Pω J ω) :
    ∑ i, (Pωi J ω i / Pω J ω) * Ucur J u a ω i = ∑ i, (Pωi J ω i / Pω J ω) * Ubar J u a ω := by
  rw [M_U J u a ω h, ← sum_mul]
  have : ∑ i, Pωi J ω i / Pω J ω = 1 := by
    rw [← sum_div]; exact div_self h.ne'
  rw [this, one_mul]

end

end Cleanroom.Corrigibility.CorrValueChange

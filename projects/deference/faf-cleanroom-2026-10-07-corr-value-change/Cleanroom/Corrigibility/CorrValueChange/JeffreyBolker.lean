import Cleanroom.Corrigibility.CorrValueChange.Model
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# corr-value-change — Jeffrey–Bolker, finite (T11 (a)–(e), (g))

Source: [[value-change-as-epistemic-update]] §5.1–5.3, §5.5–5.7. Over the finite Boolean
algebra of `Finset Ω`: desirability `V(A) = E_P[U ∣ A]` satisfies averaging (5.2); conversely an
averaging `V` on the non-null events (a function on the quotient by null events) is the
conditional expectation of the finite Radon–Nikodym derivative `U(ω) = μ({ω})/P({ω})` of the
goodness charge `μ(A) = P(A) V(A)` (5.3); the Bolker gauge `(P, U) ↦ (P', U')` preserves preference
(5.5); conditioning keeps the derivative (5.6); the example's desirabilities (5.7).
-/

namespace Cleanroom.Corrigibility.CorrValueChange

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ## (a) Kolmogorov → Jeffrey–Bolker: averaging -/

/-- **T11(a), averaging**: for disjoint non-null `A, B`,
`E[U ∣ A ∪ B] = (P(A) E[U ∣ A] + P(B) E[U ∣ B]) / (P(A) + P(B))`.
Source: [[value-change-as-epistemic-update]] §5.2 ("Averaging holds because
`∫_{A∪B} U dP = ∫_A U dP + ∫_B U dP`")
Kind: P
Fidelity: exact
Hyps: (a) `Disjoint A B`, `0 < P(A)`, `0 < P(B)` -/
theorem averaging_of_condexp (P : Prob Ω) (U : Ω → ℝ) {A B : Finset Ω} (hd : Disjoint A B)
    (hA : 0 < P.mass A) (hB : 0 < P.mass B) :
    P.condExp U (A ∪ B) = (P.mass A * P.condExp U A + P.mass B * P.condExp U B) / (P.mass A + P.mass B) := by
  rw [Prob.condExp, P.integral_union U hd, P.mass_union hd, P.integral_eq_condExp_mul U hA,
    P.integral_eq_condExp_mul U hB]
  ring

/-! ## (b) Jeffrey–Bolker → Kolmogorov: the finite Radon–Nikodym derivative -/

/-- The goodness charge `μ(A) = P(A) V(A)` (and `0` on null events).
Source: [[value-change-as-epistemic-update]] §5.3
Kind: D
Fidelity: exact -/
def goodness (P : Prob Ω) (V : Finset Ω → ℝ) (A : Finset Ω) : ℝ :=
  if 0 < P.mass A then P.mass A * V A else 0

/-- The finite Radon–Nikodym derivative `U(ω) = μ({ω})/P({ω}) = V({ω})` on the support.
Source: [[value-change-as-epistemic-update]] §5.3 ("`V(A) = E_P[U ∣ A]` with `U := μ({ω})/P({ω})`")
Kind: D
Fidelity: exact -/
def rnDeriv (P : Prob Ω) (V : Finset Ω → ℝ) (ω : Ω) : ℝ :=
  if 0 < P.p ω then V {ω} else 0

/-- **Averaging** on non-null disjoint pairs.
Source: [[value-change-as-epistemic-update]] §5.1 (the averaging axiom)
Kind: D
Fidelity: exact -/
def Averaging (P : Prob Ω) (V : Finset Ω → ℝ) : Prop :=
  ∀ A B : Finset Ω, Disjoint A B → 0 < P.mass A → 0 < P.mass B →
    V (A ∪ B) = (P.mass A * V A + P.mass B * V B) / (P.mass A + P.mass B)

/-- **Null-invariance**: `V` is a function on the quotient by the null ideal, `V(A ∪ N) = V(A)` for
null `N` and non-null `A`. (The note: "first pass to the quotient of `𝓔` by the ideal of null
propositions"; `V` is undefined on null propositions, so nothing is asked of `V` there — any
extension of a quotient-defined `V` qualifies. Audit r1, N7.)
Source: [[value-change-as-epistemic-update]] §5.3
Kind: D
Fidelity: exact -/
def NullInvariant (P : Prob Ω) (V : Finset Ω → ℝ) : Prop :=
  ∀ A N : Finset Ω, 0 < P.mass A → P.mass N = 0 → V (A ∪ N) = V A

/-- **`V = E[U ∣ ·]` is null-invariant** (with `averaging_of_condexp`, the witness for the hypothesis
package of `condexp_of_averaging`): adding a null set changes neither the mass nor the integral.
Source: [[value-change-as-epistemic-update]] §5.3; audit r1 (N8)
Kind: N+
Fidelity: exact -/
theorem nullInvariant_of_condexp (P : Prob Ω) (U : Ω → ℝ) : NullInvariant P (P.condExp U) := by
  intro A N _ hN
  have hsub : A ∪ N = A ∪ (N \ A) := (union_sdiff_self_eq_union).symm
  have hd : Disjoint A (N \ A) := disjoint_sdiff
  have hm0 : P.mass (N \ A) = 0 :=
    le_antisymm (hN ▸ P.mass_mono sdiff_subset) (P.mass_nonneg _)
  have hi0 : P.integral U (N \ A) = 0 :=
    sum_eq_zero fun ω hω => by rw [P.p_eq_zero_of_mass_eq_zero hm0 hω, zero_mul]
  unfold Prob.condExp
  rw [hsub, P.mass_union hd, P.integral_union _ hd, hm0, hi0, add_zero, add_zero]

/-- **T11(b), the finite Radon–Nikodym theorem**: if `V` satisfies averaging on non-null disjoint
pairs and is null-invariant, then `V(A) = E_P[U ∣ A]` for every non-null `A`, with
`U(ω) = μ({ω})/P({ω})`. Proof by induction on `A`, adding one world at a time.
Source: [[value-change-as-epistemic-update]] §5.3 (Jeffrey–Bolker → Kolmogorov, I)
Kind: P
Fidelity: exact (null-invariance made explicit; the note has it as "pass to the quotient")
Hyps: (a) `hav : Averaging`, `hni : NullInvariant`, `0 < P(A)` -/
theorem condexp_of_averaging (P : Prob Ω) (V : Finset Ω → ℝ) (hav : Averaging P V)
    (hni : NullInvariant P V) (A : Finset Ω) (hA : 0 < P.mass A) :
    V A = P.condExp (rnDeriv P V) A := by
  induction A using Finset.induction_on with
  | empty => simp [Prob.mass] at hA
  | @insert ω A' hω ih =>
    have hins : insert ω A' = A' ∪ {ω} := by ext x; simp [or_comm]
    have hdisj : Disjoint A' {ω} := by simpa using hω
    have hmass : P.mass (insert ω A') = P.mass A' + P.p ω := by
      rw [hins, P.mass_union hdisj]; simp [Prob.mass]
    have hint : P.integral (rnDeriv P V) (insert ω A') =
        P.integral (rnDeriv P V) A' + P.p ω * rnDeriv P V ω := by
      rw [hins, P.integral_union _ hdisj]; simp [Prob.integral]
    rcases (P.nonneg ω).lt_or_eq with hpω | hpω
    · -- the new world has positive weight
      have hU : rnDeriv P V ω = V {ω} := by simp [rnDeriv, hpω]
      have hmω : P.mass {ω} = P.p ω := by simp [Prob.mass]
      rcases (P.mass_nonneg A').lt_or_eq with hA' | hA'
      · -- both parts non-null: averaging
        rw [hins, hav A' {ω} hdisj hA' (hmω ▸ hpω), ih hA']
        unfold Prob.condExp
        rw [hmω, ← hins, hint, hmass, hU]
        have h1 : P.mass A' ≠ 0 := hA'.ne'
        have h2 : P.mass A' + P.p ω ≠ 0 := by positivity
        field_simp
      · -- `A'` is null: `V(A' ∪ {ω}) = V({ω})`
        have hVa : V (insert ω A') = V {ω} := by
          rw [hins, union_comm]; exact hni {ω} A' (hmω ▸ hpω) hA'.symm
        have hIa : P.integral (rnDeriv P V) A' = 0 := by
          unfold Prob.integral
          exact sum_eq_zero fun x hx => by
            rw [P.p_eq_zero_of_mass_eq_zero hA'.symm hx, zero_mul]
        rw [hVa]
        unfold Prob.condExp
        rw [hint, hmass, hIa, ← hA', hU]
        field_simp
        ring
    · -- the new world is null: nothing changes
      have hA' : 0 < P.mass A' := by rw [hmass, ← hpω, add_zero] at hA; exact hA
      have hVa : V (insert ω A') = V A' := by
        rw [hins]; exact hni A' {ω} hA' (by simp [Prob.mass, ← hpω])
      rw [hVa, ih hA']
      unfold Prob.condExp
      rw [hint, hmass, ← hpω, zero_mul, add_zero, add_zero]

/-- **The goodness charge is the integral of the derivative**, `μ(A) = ∫_A U dP` for every `A`, hence
finitely additive (the note's "multiply the averaging axiom out and `μ` is finitely additive").
Source: [[value-change-as-epistemic-update]] §5.3
Kind: C
Fidelity: exact
Hyps: (a) `hav`, `hni` -/
theorem goodness_eq_integral (P : Prob Ω) (V : Finset Ω → ℝ) (hav : Averaging P V)
    (hni : NullInvariant P V) (A : Finset Ω) :
    goodness P V A = P.integral (rnDeriv P V) A := by
  unfold goodness
  split_ifs with h
  · rw [condexp_of_averaging P V hav hni A h, mul_comm, P.condExp_mul_mass _ h]
  · have h0 : P.mass A = 0 := le_antisymm (not_lt.1 h) (P.mass_nonneg A)
    unfold Prob.integral
    exact (sum_eq_zero fun x hx => by rw [P.p_eq_zero_of_mass_eq_zero h0 hx, zero_mul]).symm

/-- `μ` is additive on disjoint events.
Source: [[value-change-as-epistemic-update]] §5.3 ("`μ(A ∨ B) = μ(A) + μ(B)` for disjoint `A, B`")
Kind: C
Fidelity: exact
Hyps: (a) `hav`, `hni` -/
theorem goodness_additive (P : Prob Ω) (V : Finset Ω → ℝ) (hav : Averaging P V)
    (hni : NullInvariant P V) {A B : Finset Ω} (hd : Disjoint A B) :
    goodness P V (A ∪ B) = goodness P V A + goodness P V B := by
  rw [goodness_eq_integral P V hav hni, goodness_eq_integral P V hav hni,
    goodness_eq_integral P V hav hni, P.integral_union _ hd]

/-! ## (c), (d) The Bolker gauge -/

/-- The tilted probability `dP'/dP ∝ cU + d`. The positivity `cU + d > 0` is asked at every world
where the note asks it `P`-almost surely; `bolker_gauge_ae` below recovers the almost-sure form.
Source: [[value-change-as-epistemic-update]] §5.5
Kind: D
Fidelity: exact up to null worlds (see `bolker_gauge_ae`) -/
def tilt (P : Prob Ω) (U : Ω → ℝ) (c d : ℝ) (hpos : ∀ ω, 0 < c * U ω + d) : Prob Ω where
  p := fun ω => (c * U ω + d) * P.p ω / ∑ ω', (c * U ω' + d) * P.p ω'
  nonneg := fun ω => by
    have hZ : 0 < ∑ ω', (c * U ω' + d) * P.p ω' := by
      obtain ⟨ω₀, h₀⟩ := P.exists_pos
      exact lt_of_lt_of_le (mul_pos (hpos ω₀) h₀)
        (single_le_sum (f := fun ω' => (c * U ω' + d) * P.p ω')
          (fun ω' _ => mul_nonneg (hpos ω').le (P.nonneg ω')) (mem_univ ω₀))
    exact div_nonneg (mul_nonneg (hpos ω).le (P.nonneg ω)) hZ.le
  sum_one := by
    have hZ : 0 < ∑ ω', (c * U ω' + d) * P.p ω' := by
      obtain ⟨ω₀, h₀⟩ := P.exists_pos
      exact lt_of_lt_of_le (mul_pos (hpos ω₀) h₀)
        (single_le_sum (f := fun ω' => (c * U ω' + d) * P.p ω')
          (fun ω' _ => mul_nonneg (hpos ω').le (P.nonneg ω')) (mem_univ ω₀))
    rw [← sum_div]; exact div_self hZ.ne'

/-- The gauged utility `U' = (aU + b)/(cU + d)`, a fixed pointwise map of `U`.
Source: [[value-change-as-epistemic-update]] §5.5
Kind: D
Fidelity: exact -/
def gaugeU (a b c d : ℝ) (U : Ω → ℝ) (ω : Ω) : ℝ := (a * U ω + b) / (c * U ω + d)

/-- The Möbius map `v ↦ (av + b)/(cv + d)` is strictly increasing where `cv + d > 0`, when
`ad − bc > 0`.
Source: [[value-change-as-epistemic-update]] §5.5 ("an increasing function of `V(A)`")
Kind: L
Fidelity: exact -/
theorem mobius_strictMono {a b c d v₁ v₂ : ℝ} (had : 0 < a * d - b * c) (h₁ : 0 < c * v₁ + d)
    (h₂ : 0 < c * v₂ + d) (hv : v₁ < v₂) :
    (a * v₁ + b) / (c * v₁ + d) < (a * v₂ + b) / (c * v₂ + d) := by
  rw [div_lt_div_iff₀ h₁ h₂]; nlinarith

/-- `cV(A) + d > 0` for non-null `A`, since `V(A)` is an average of `U` over `A`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem gauge_denom_pos (P : Prob Ω) (U : Ω → ℝ) (c d : ℝ) (hpos : ∀ ω, 0 < c * U ω + d)
    {A : Finset Ω} (hA : 0 < P.mass A) : 0 < c * P.condExp U A + d := by
  have hsmul : P.condExp (fun ω => c * U ω) A = c * P.condExp U A := by
    unfold Prob.condExp Prob.integral
    rw [← mul_div_assoc, mul_sum]
    congr 1; refine sum_congr rfl fun ω _ => ?_; ring
  have : c * P.condExp U A + d = P.condExp (fun ω => c * U ω + d) A := by
    have h := P.condExp_add (fun ω => c * U ω) (fun _ => d) A
    rw [h, P.condExp_const d hA, hsmul]
  rw [this]
  unfold Prob.condExp
  apply div_pos _ hA
  unfold Prob.integral
  obtain ⟨ω₀, hω₀, hp₀⟩ := P.exists_pos_of_mass_pos hA
  exact lt_of_lt_of_le (mul_pos hp₀ (hpos ω₀))
    (single_le_sum (f := fun ω => P.p ω * (c * U ω + d))
      (fun ω _ => mul_nonneg (P.nonneg ω) (hpos ω).le) hω₀)

/-- **T11(c), the Bolker gauge**: for `ad − bc > 0` and `cU + d > 0` everywhere, the gauged state
`(P', U')` has `V'(A) = E_{P'}[U' ∣ A] = (a V(A) + b)/(c V(A) + d)` on every non-null `A`, and this is
strictly increasing in `V(A)`, so `(P', V')` represents the same preference.
Source: [[value-change-as-epistemic-update]] §5.5 (the display and "so `(P', V')` represents the
same preference")
Kind: P
Fidelity: exact up to null worlds (`cU + d > 0` everywhere where the note has it `P`-a.s.; the
almost-sure form is `bolker_gauge_ae`)
Hyps: (a) `had`, `hpos` (the gauge's own conditions), `0 < P(A)` -/
theorem bolker_gauge (P : Prob Ω) (U : Ω → ℝ) (a b c d : ℝ) (had : 0 < a * d - b * c)
    (hpos : ∀ ω, 0 < c * U ω + d) {A : Finset Ω} (hA : 0 < P.mass A) :
    (tilt P U c d hpos).condExp (gaugeU a b c d U) A =
      (a * P.condExp U A + b) / (c * P.condExp U A + d) := by
  have hZ : 0 < ∑ ω', (c * U ω' + d) * P.p ω' := by
    obtain ⟨ω₀, h₀⟩ := P.exists_pos
    exact lt_of_lt_of_le (mul_pos (hpos ω₀) h₀)
      (single_le_sum (f := fun ω' => (c * U ω' + d) * P.p ω')
        (fun ω' _ => mul_nonneg (hpos ω').le (P.nonneg ω')) (mem_univ ω₀))
  set Z := ∑ ω', (c * U ω' + d) * P.p ω' with hZdef
  have hnum : (tilt P U c d hpos).integral (gaugeU a b c d U) A =
      (∑ ω ∈ A, P.p ω * (a * U ω + b)) / Z := by
    unfold Prob.integral; rw [sum_div]; refine sum_congr rfl fun ω _ => ?_
    show (c * U ω + d) * P.p ω / Z * ((a * U ω + b) / (c * U ω + d)) = P.p ω * (a * U ω + b) / Z
    have := hpos ω; field_simp
  have hden : (tilt P U c d hpos).mass A = (∑ ω ∈ A, P.p ω * (c * U ω + d)) / Z := by
    unfold Prob.mass; rw [sum_div]; refine sum_congr rfl fun ω _ => ?_
    show (c * U ω + d) * P.p ω / Z = P.p ω * (c * U ω + d) / Z
    ring
  have hdenpos : 0 < ∑ ω ∈ A, P.p ω * (c * U ω + d) := by
    obtain ⟨ω₀, hω₀, hp₀⟩ := P.exists_pos_of_mass_pos hA
    exact lt_of_lt_of_le (mul_pos hp₀ (hpos ω₀))
      (single_le_sum (f := fun ω => P.p ω * (c * U ω + d))
        (fun ω _ => mul_nonneg (P.nonneg ω) (hpos ω).le) hω₀)
  have hI : ∑ ω ∈ A, P.p ω * U ω = P.condExp U A * P.mass A := P.integral_eq_condExp_mul U hA
  have hnum' : ∑ ω ∈ A, P.p ω * (a * U ω + b) = a * (∑ ω ∈ A, P.p ω * U ω) + b * P.mass A := by
    unfold Prob.mass; rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun ω _ => ?_; ring
  have hden' : ∑ ω ∈ A, P.p ω * (c * U ω + d) = c * (∑ ω ∈ A, P.p ω * U ω) + d * P.mass A := by
    unfold Prob.mass; rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun ω _ => ?_; ring
  have hcd : 0 < c * P.condExp U A + d := gauge_denom_pos P U c d hpos hA
  rw [Prob.condExp, hnum, hden, div_div_div_cancel_right₀ hZ.ne', hnum', hden', hI]
  rw [div_eq_div_iff (by rw [hden', hI] at hdenpos; linarith) hcd.ne']
  ring

/-- `U` with its values on the `P`-null worlds replaced by its value at a fixed world `ω₀`.
Source: none: infrastructure (audit r3 fidelity N5)
Kind: D
Fidelity: n/a -/
def aeFix (P : Prob Ω) (U : Ω → ℝ) (ω₀ : Ω) : Ω → ℝ := fun ω => if 0 < P.p ω then U ω else U ω₀

/-- Changing `U` on null worlds changes no conditional expectation under `P`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condExp_aeFix (P : Prob Ω) (U : Ω → ℝ) (ω₀ : Ω) (A : Finset Ω) :
    P.condExp (aeFix P U ω₀) A = P.condExp U A := by
  unfold Prob.condExp Prob.integral
  congr 1
  refine sum_congr rfl fun ω _ => ?_
  unfold aeFix
  split_ifs with h
  · rfl
  · have : P.p ω = 0 := le_antisymm (not_lt.1 h) (P.nonneg ω)
    simp [this]

/-- **The Bolker gauge under the note's almost-sure condition**: if `cU + d > 0` only on the worlds
of positive `P`-probability, there is a utility `U'` agreeing with `U` on those worlds (so `P`-a.s.)
for which `cU' + d > 0` everywhere, and the gauged state `(tilt P U', gaugeU U')` has
`V'(A) = (a V(A) + b)/(c V(A) + d)` on every non-null `A`, with `V(A) = E_P[U ∣ A]` computed from `U`
itself. This is `bolker_gauge` with its everywhere-positivity discharged up to null worlds.
Source: [[value-change-as-epistemic-update]] §5.5 ("`cU + d > 0` `P`-a.s."); audit r3 fidelity N5
Kind: C (`bolker_gauge` at `aeFix P U ω₀`, with `condExp_aeFix`)
Fidelity: exact
Hyps: (a) `had`, `hpos` (the note's a.s. condition), `0 < P(A)` -/
theorem bolker_gauge_ae (P : Prob Ω) (U : Ω → ℝ) (a b c d : ℝ) (had : 0 < a * d - b * c)
    (hpos : ∀ ω, 0 < P.p ω → 0 < c * U ω + d) {A : Finset Ω} (hA : 0 < P.mass A) :
    ∃ (U' : Ω → ℝ) (hpos' : ∀ ω, 0 < c * U' ω + d), (∀ ω, 0 < P.p ω → U' ω = U ω) ∧
      (tilt P U' c d hpos').condExp (gaugeU a b c d U') A =
        (a * P.condExp U A + b) / (c * P.condExp U A + d) := by
  obtain ⟨ω₀, h₀⟩ := P.exists_pos
  have hpos' : ∀ ω, 0 < c * aeFix P U ω₀ ω + d := by
    intro ω; unfold aeFix; split_ifs with h
    · exact hpos ω h
    · exact hpos ω₀ h₀
  refine ⟨aeFix P U ω₀, hpos', fun ω h => by simp [aeFix, h], ?_⟩
  rw [bolker_gauge P (aeFix P U ω₀) a b c d had hpos' hA, condExp_aeFix]

/-- **Preference is preserved by the gauge**: `V(A) ≤ V(B) ↔ V'(A) ≤ V'(B)` on non-null `A, B`.
Source: [[value-change-as-epistemic-update]] §5.5
Kind: C
Fidelity: exact up to null worlds (as `bolker_gauge`)
Hyps: (a) `had`, `hpos`, `0 < P(A)`, `0 < P(B)` -/
theorem gauge_preserves_preference (P : Prob Ω) (U : Ω → ℝ) (a b c d : ℝ) (had : 0 < a * d - b * c)
    (hpos : ∀ ω, 0 < c * U ω + d) {A B : Finset Ω} (hA : 0 < P.mass A) (hB : 0 < P.mass B) :
    P.condExp U A ≤ P.condExp U B ↔
      (tilt P U c d hpos).condExp (gaugeU a b c d U) A ≤ (tilt P U c d hpos).condExp (gaugeU a b c d U) B := by
  rw [bolker_gauge P U a b c d had hpos hA, bolker_gauge P U a b c d had hpos hB]
  have h1 := gauge_denom_pos P U c d hpos hA
  have h2 := gauge_denom_pos P U c d hpos hB
  constructor
  · intro h
    rcases h.lt_or_eq with hlt | heq
    · exact (mobius_strictMono had h1 h2 hlt).le
    · rw [heq]
  · intro h
    by_contra hc
    have := mobius_strictMono had h2 h1 (not_le.1 hc)
    linarith

/-- **T11(d), pure belief change is gauge-invariant**: the gauge acts on the utility by the fixed
pointwise map `gaugeU a b c d`, independent of the probability. So a transition `(P, U) → (P₁, U)`
becomes `(P', U') → (P₁', U')` with the *same* gauged utility `U' = gaugeU a b c d U`, and at the new
belief `P₁` the gauged desirability is again `(a V₁(A) + b)/(c V₁(A) + d)` on every non-null `A`
(the first clause: `bolker_gauge` at `P₁`); and a transition that changes `U` somewhere where both
values keep `cU + d > 0` changes `U'` there (the second clause: the map is injective on that region).
Source: [[value-change-as-epistemic-update]] §5.5 remark (ii)
Kind: C (first clause `bolker_gauge` at the new belief; second from `mobius_strictMono`)
Fidelity: exact up to null worlds (as `bolker_gauge`)
Hyps: (a) `had`, `hpos` (the gauge's own conditions); positivity of the denominators at the
compared values -/
theorem pure_belief_change_gauge_invariant (a b c d : ℝ) (had : 0 < a * d - b * c) (U U₁ : Ω → ℝ)
    (hpos : ∀ ω, 0 < c * U ω + d) :
    (∀ (P₁ : Prob Ω) (A : Finset Ω), 0 < P₁.mass A →
      (tilt P₁ U c d hpos).condExp (gaugeU a b c d U) A =
        (a * P₁.condExp U A + b) / (c * P₁.condExp U A + d)) ∧
    ∀ ω, 0 < c * U ω + d → 0 < c * U₁ ω + d → U ω ≠ U₁ ω →
      gaugeU a b c d U ω ≠ gaugeU a b c d U₁ ω := by
  refine ⟨fun P₁ A hA => bolker_gauge P₁ U a b c d had hpos hA, fun ω h₁ h₂ hne => ?_⟩
  unfold gaugeU
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (mobius_strictMono had h₁ h₂ hlt).ne
  · exact (mobius_strictMono had h₂ h₁ hgt).ne'

/-! ## (e) Conditioning keeps the derivative -/

/-- The conditioned probability `P_E = P(· ∣ E)`.
Source: [[value-change-as-epistemic-update]] §5.6
Kind: D
Fidelity: exact -/
def condProb (P : Prob Ω) (E : Finset Ω) (hE : 0 < P.mass E) : Prob Ω where
  p := fun ω => if ω ∈ E then P.p ω / P.mass E else 0
  nonneg := fun ω => by split_ifs; exact div_nonneg (P.nonneg ω) hE.le; exact le_rfl
  sum_one := by
    rw [← sum_filter, filter_mem_eq_inter, univ_inter, ← sum_div]
    exact div_self hE.ne'

/-- **T11(e), conditioning preserves the derivative**: `V_E(A) := E_{P_E}[U ∣ A] = E_P[U ∣ A ∧ E] =
V(A ∧ E)` for `P(A ∧ E) > 0` — the state `(P_E, U)` with the *same* `U` represents the conditioned
desirabilities.
Source: [[value-change-as-epistemic-update]] §5.6 ("so the Radon–Nikodym derivative is unchanged
on `E`")
Kind: P
Fidelity: exact
Hyps: (a) `0 < P(E)`, `0 < P(A ∧ E)` -/
theorem conditioning_preserves_rn (P : Prob Ω) (U : Ω → ℝ) {E : Finset Ω} (hE : 0 < P.mass E)
    (A : Finset Ω) (hAE : 0 < P.mass (A ∩ E)) :
    (condProb P E hE).condExp U A = P.condExp U (A ∩ E) := by
  unfold Prob.condExp Prob.integral Prob.mass condProb
  have hpt : ∀ ω, (if ω ∈ E then P.p ω / P.mass E else 0) = (if ω ∈ E then P.p ω else 0) / P.mass E := by
    intro ω; split_ifs <;> simp
  simp_rw [hpt, div_mul_eq_mul_div, ← sum_div]
  rw [div_div_div_cancel_right₀ hE.ne', ← filter_mem_eq_inter, sum_filter, sum_filter]
  congr 1 <;> refine sum_congr rfl fun ω _ => ?_ <;> split_ifs <;> simp

/-! ## (g) The example in Jeffrey–Bolker -/

/-- The algebra generated by hypothesis, signal and act: worlds `(θ, i, a)`, the teacher's joint
at `r = 9/10` with the acts independent and equiprobable.
Source: [[value-change-as-epistemic-update]] §5.7 ("Take the algebra generated by act, signal
and hypothesis, with the acts independent of signal and hypothesis and given equal probability")
Kind: D
Fidelity: exact -/
def jbProb : Prob (Bool × Bool × Fin 3) where
  p := fun y => 1 / 2 * (if y.1 = y.2.1 then 9 / 10 else 1 / 10) * (1 / 3)
  nonneg := fun y => by split_ifs <;> norm_num
  sum_one := by
    simp [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three]; norm_num

/-- The utility on the algebra: `u_θ(a)` with `s = 3/5`.
Source: [[value-change-as-epistemic-update]] §5.7
Kind: D
Fidelity: exact -/
def jbU (y : Bool × Bool × Fin 3) : ℝ :=
  ![if y.1 then 1 else 0, if y.1 then 0 else 1, 3 / 5] y.2.2

/-- **T11(g), the desirabilities of §5.7**: `V(a₁) = 1/2`, `V(a₁ ∧ A) = 9/10`, `V(a₁ ∧ B) = 1/10`,
`V(a₃) = 3/5`, and `V((a₁ ∧ A) ∨ (a₂ ∧ B)) = 9/10` ("act on the signal").
Source: [[value-change-as-epistemic-update]] §5.7 (computed); fixture `jeffrey_bolker`
Kind: N+
Fidelity: exact -/
theorem jb_example :
    jbProb.condExp jbU (univ.filter fun y => y.2.2 = 0) = 1 / 2 ∧
    jbProb.condExp jbU (univ.filter fun y => y.2.2 = 0 ∧ y.2.1 = true) = 9 / 10 ∧
    jbProb.condExp jbU (univ.filter fun y => y.2.2 = 0 ∧ y.2.1 = false) = 1 / 10 ∧
    jbProb.condExp jbU (univ.filter fun y => y.2.2 = 2) = 3 / 5 ∧
    jbProb.condExp jbU (univ.filter fun y => (y.2.2 = 0 ∧ y.2.1 = true) ∨ (y.2.2 = 1 ∧ y.2.1 = false))
      = 9 / 10 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Prob.condExp, Prob.integral, Prob.mass, jbProb, jbU, sum_filter, Fintype.sum_prod_type,
      Fintype.sum_bool, Fin.sum_univ_three] <;> norm_num

end

end Cleanroom.Corrigibility.CorrValueChange

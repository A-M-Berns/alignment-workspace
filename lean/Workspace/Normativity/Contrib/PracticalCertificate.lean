/-
# Algebra of the practical-response certificate

The public certificate of the Normative Induction contract is, per admissible edge
`(e, s)`, the affine inequality `loss ≤ M * d + ε` between the anchored loss of
exposure `e` under the response realized at service occurrence `s` and the public
operative defect `d` at `s`.  This file proves the algebra of three ways of producing
it and of the joint-compatibility question when several exposures share one realized
response.  Nothing here formalizes settlement, legitimacy, counterfactual value or
response adequacy: each enters as a named hypothesis.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Workspace.Normativity.Contrib.NormativeInductor

namespace Workspace.Normativity.Contrib.PracticalCertificate

open scoped BigOperators
open Workspace.Normativity.Contrib.NormativeInductor

/-! ## 1. The proxy form

A route to the certificate factors through a *displayed proxy* `g`: a function of the
quote that the compiled region keeps below `ε₀`, that moves at most `C` per unit of
sup-distance, and against which the realized response's anchored loss is adequate
with constants `(L, εr)`.  The value-correspondence route and the adequate-set route
are both instances; the proxy form itself is equivalent to the certificate (take
`g := M d + ε`). -/

/-- A proxy that is at most `ε₀` at a region point `u`, and moves at most `C * d`
between the quote and `u`, is at most `C * d + ε₀` at the quote. -/
theorem proxy_le_defect {gb gu C d ε₀ : ℝ}
    (hlip : |gb - gu| ≤ C * d) (hregion : gu ≤ ε₀) :
    gb ≤ C * d + ε₀ := by
  have := (abs_le.mp hlip).2
  linarith

/-- The proxy route: region control of the proxy, Lipschitz transport of the proxy
from the region point to the quote, and response adequacy against the proxy give the
public certificate with `M = L * C` and `ε = L * ε₀ + εr`. -/
theorem proxy_route {gb gu C d ε₀ L εr loss : ℝ}
    (hL : 0 ≤ L)
    (hlip : |gb - gu| ≤ C * d) (hregion : gu ≤ ε₀)
    (hresp : loss ≤ L * gb + εr) :
    loss ≤ (L * C) * d + (L * ε₀ + εr) :=
  practical_response_compose hL (proxy_le_defect hlip hregion) hresp

/-! ## 2. The adequate-set route

The anchored loss of a response distribution on a finite menu is the expectation of
the per-response anchored loss `lam`.  No value vector appears. -/

/-- Expected anchored loss of the distribution `p` on `menu` against per-response
losses `lam`. -/
def anchoredLoss {Q : Type*} (menu : Finset Q) (p lam : Q → ℝ) : ℝ :=
  ∑ q ∈ menu, p q * lam q

/-- Adequate-set route.  If every response in `adequate` has anchored loss at most
`εad`, every response has loss at most `D`, and the realized distribution's mass off
the adequate set is at most `κ * d + θ`, then the anchored loss is at most
`(D * κ) * d + (εad + D * θ)`. -/
theorem adequate_set_route {Q : Type*} [DecidableEq Q] (menu adequate : Finset Q)
    {p lam : Q → ℝ} {εad D κ d θ : ℝ}
    (hsub : adequate ⊆ menu)
    (hp : ∀ q ∈ menu, 0 ≤ p q)
    (hprob : ∑ q ∈ menu, p q = 1)
    (hεad : 0 ≤ εad) (hD : 0 ≤ D)
    (hadequate : ∀ q ∈ adequate, lam q ≤ εad)
    (hbound : ∀ q ∈ menu, lam q ≤ D)
    (hcouple : ∑ q ∈ menu \ adequate, p q ≤ κ * d + θ) :
    anchoredLoss menu p lam ≤ (D * κ) * d + (εad + D * θ) := by
  unfold anchoredLoss
  rw [← Finset.sum_sdiff hsub]
  have hoff : ∑ q ∈ menu \ adequate, p q * lam q ≤ D * (κ * d + θ) := by
    calc
      ∑ q ∈ menu \ adequate, p q * lam q ≤ ∑ q ∈ menu \ adequate, p q * D := by
        apply Finset.sum_le_sum
        intro q hq
        have hqm : q ∈ menu := (Finset.mem_sdiff.mp hq).1
        exact mul_le_mul_of_nonneg_left (hbound q hqm) (hp q hqm)
      _ = D * ∑ q ∈ menu \ adequate, p q := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ ≤ D * (κ * d + θ) := mul_le_mul_of_nonneg_left hcouple hD
  have hon : ∑ q ∈ adequate, p q * lam q ≤ εad := by
    have hmass : ∑ q ∈ adequate, p q ≤ 1 := by
      rw [← hprob]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq _ => hp q hq)
    calc
      ∑ q ∈ adequate, p q * lam q ≤ ∑ q ∈ adequate, p q * εad := by
        apply Finset.sum_le_sum
        intro q hq
        exact mul_le_mul_of_nonneg_left (hadequate q hq) (hp q (hsub hq))
      _ = εad * ∑ q ∈ adequate, p q := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ ≤ εad * 1 := mul_le_mul_of_nonneg_left hmass hεad
      _ = εad := mul_one εad
  nlinarith [hoff, hon]

/-! ## 3. One-sided calibration suffices for the value route

`approximate_argmax_transfer` in `NormativeInductor` assumes two-sided calibration at
every response.  The argument uses only that the displayed value does not
*underestimate* the true best response by more than `r` and does not *overestimate*
any response by more than `r`. -/

/-- Deterministic one-sided form.  Underestimating a non-optimal response by any
amount is harmless. -/
theorem one_sided_argmax_transfer {Q : Type*} {b v : Q → ℝ} {qStar q : Q} {r η : ℝ}
    (hbest : v qStar ≤ b qStar + r) (hlow : b q - r ≤ v q)
    (hchoice : b qStar ≤ b q + η) :
    v qStar - v q ≤ 2 * r + η := by
  linarith

/-- Randomized one-sided form.  The true best response need not lie in the menu the
distribution is supported on; only its displayed value is compared. -/
theorem one_sided_randomized_argmax_transfer {Q : Type*} (actions : Finset Q)
    {p b v : Q → ℝ} {qStar : Q} {r η : ℝ}
    (hp : ∀ q ∈ actions, 0 ≤ p q)
    (hprob : ∑ q ∈ actions, p q = 1)
    (hbest : v qStar ≤ b qStar + r)
    (hlow : ∀ q ∈ actions, b q - r ≤ v q)
    (hchoice : b qStar ≤ (∑ q ∈ actions, p q * b q) + η) :
    v qStar - ∑ q ∈ actions, p q * v q ≤ 2 * r + η := by
  have hr : ∑ q ∈ actions, p q * r = r := by
    calc
      ∑ q ∈ actions, p q * r = ∑ q ∈ actions, r * p q := by
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ = r * ∑ q ∈ actions, p q := by rw [Finset.mul_sum]
      _ = r := by rw [hprob, mul_one]
  have hmean : (∑ q ∈ actions, p q * b q) - r ≤ ∑ q ∈ actions, p q * v q := by
    calc
      (∑ q ∈ actions, p q * b q) - r = ∑ q ∈ actions, (p q * b q - p q * r) := by
        rw [Finset.sum_sub_distrib, hr]
      _ ≤ ∑ q ∈ actions, p q * v q := by
        apply Finset.sum_le_sum
        intro q hq
        have := mul_le_mul_of_nonneg_left (hlow q hq) (hp q hq)
        nlinarith
  linarith

/-! ## 4. Joint compatibility

One service occurrence realizes one response distribution `Π b` as a function of the
quote `b`.  Every exposure matched to it must satisfy its own certificate against that
same distribution, uniformly in `b`.  Because the region is nonempty there is a quote
of zero defect, and at zero defect the certificate is `loss ≤ ε`.  Conversely a
distribution adequate for every exposure at zero defect certifies every edge at every
quote when used as a constant adapter. -/

/-- A bundle of edges over one service occurrence is jointly certifiable by some
adapter if and only if some single distribution is adequate for every exposure at
zero defect.  `P` is the type of response distributions, `Λ e Π` the anchored loss of
exposure `e` under `Π`, `d b` the public defect at quote `b`, and `b₀` any quote in
the compiled region. -/
theorem bundle_certifiable_iff_zero_defect_adequate {E B P : Type*}
    (Λ : E → P → ℝ) (M ε : E → ℝ) (d : B → ℝ)
    (hM : ∀ e, 0 ≤ M e) (hd : ∀ b, 0 ≤ d b) {b₀ : B} (hb₀ : d b₀ = 0) :
    (∃ adapter : B → P, ∀ e b, Λ e (adapter b) ≤ M e * d b + ε e) ↔
      (∃ common : P, ∀ e, Λ e common ≤ ε e) := by
  constructor
  · rintro ⟨adapter, h⟩
    refine ⟨adapter b₀, fun e => ?_⟩
    have := h e b₀
    rw [hb₀, mul_zero, zero_add] at this
    exact this
  · rintro ⟨common, h⟩
    refine ⟨fun _ => common, fun e b => ?_⟩
    have : 0 ≤ M e * d b := mul_nonneg (hM e) (hd b)
    linarith [h e]

/-- Two exposures whose adequate sets are disjoint cannot both be answered: any
distribution places total anchored loss at least `D` across the two, when every
response off an exposure's adequate set costs it at least `D`. -/
theorem disjoint_adequate_sets_force_loss {Q : Type*} [DecidableEq Q]
    (menu A₁ A₂ : Finset Q) {p lam₁ lam₂ : Q → ℝ} {D : ℝ}
    (h₁ : A₁ ⊆ menu) (h₂ : A₂ ⊆ menu) (hdisj : Disjoint A₁ A₂)
    (hp : ∀ q ∈ menu, 0 ≤ p q) (hprob : ∑ q ∈ menu, p q = 1) (hD : 0 ≤ D)
    (hlam₁ : ∀ q ∈ menu, 0 ≤ lam₁ q) (hlam₂ : ∀ q ∈ menu, 0 ≤ lam₂ q)
    (hoff₁ : ∀ q ∈ menu, q ∉ A₁ → D ≤ lam₁ q)
    (hoff₂ : ∀ q ∈ menu, q ∉ A₂ → D ≤ lam₂ q) :
    D ≤ anchoredLoss menu p lam₁ + anchoredLoss menu p lam₂ := by
  -- each anchored loss dominates `D` times the mass off its adequate set
  have lower : ∀ (A : Finset Q) (lam : Q → ℝ), A ⊆ menu →
      (∀ q ∈ menu, 0 ≤ lam q) → (∀ q ∈ menu, q ∉ A → D ≤ lam q) →
      D * ∑ q ∈ menu \ A, p q ≤ anchoredLoss menu p lam := by
    intro A lam hA hlam hoff
    unfold anchoredLoss
    calc
      D * ∑ q ∈ menu \ A, p q = ∑ q ∈ menu \ A, p q * D := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ ≤ ∑ q ∈ menu \ A, p q * lam q := by
        apply Finset.sum_le_sum
        intro q hq
        have hqm : q ∈ menu := (Finset.mem_sdiff.mp hq).1
        have hqA : q ∉ A := (Finset.mem_sdiff.mp hq).2
        exact mul_le_mul_of_nonneg_left (hoff q hqm hqA) (hp q hqm)
      _ ≤ ∑ q ∈ menu, p q * lam q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        intro q hq _
        exact mul_nonneg (hp q hq) (hlam q hq)
  have l₁ := lower A₁ lam₁ h₁ hlam₁ hoff₁
  have l₂ := lower A₂ lam₂ h₂ hlam₂ hoff₂
  -- the two off-sets cover the menu
  have hcover : (menu \ A₁) ∪ (menu \ A₂) = menu := by
    rw [← Finset.sdiff_inter_distrib_right, Finset.disjoint_iff_inter_eq_empty.mp hdisj,
      Finset.sdiff_empty]
  have hmass : 1 ≤ ∑ q ∈ menu \ A₁, p q + ∑ q ∈ menu \ A₂, p q := by
    have hunion := Finset.sum_union_inter (s₁ := menu \ A₁) (s₂ := menu \ A₂) (f := p)
    rw [hcover, hprob] at hunion
    have hinter : 0 ≤ ∑ q ∈ (menu \ A₁) ∩ (menu \ A₂), p q := by
      apply Finset.sum_nonneg
      intro q hq
      exact hp q (Finset.mem_sdiff.mp (Finset.mem_inter.mp hq).1).1
    linarith
  nlinarith [l₁, l₂, hmass, hD]

/-- Two exposures matched to one service occurrence whose value coordinates are
shared cannot both be calibrated to within `ζ₁`, `ζ₂` unless their authenticated
values disagree by at most `ζ₁ + ζ₂`. -/
theorem shared_coordinates_bound_disagreement {b v₁ v₂ ζ₁ ζ₂ : ℝ}
    (h₁ : |b - v₁| ≤ ζ₁) (h₂ : |b - v₂| ≤ ζ₂) : |v₁ - v₂| ≤ ζ₁ + ζ₂ := by
  calc
    |v₁ - v₂| ≤ |v₁ - b| + |b - v₂| := abs_sub_le v₁ b v₂
    _ = |b - v₁| + |b - v₂| := by rw [abs_sub_comm v₁ b]
    _ ≤ ζ₁ + ζ₂ := add_le_add h₁ h₂

/-! ## 5. Inhabitation witnesses

Concrete instances of the two finite-sum theorems, over a three-response menu. -/

/-- A three-response menu; response `0` is adequate for exposure one, response `1`
for exposure two, and the realized distribution splits evenly between them. -/
def witnessMenu : Finset (Fin 3) := Finset.univ

noncomputable def witnessP : Fin 3 → ℝ := ![1/2, 1/2, 0]
noncomputable def witnessLam₁ : Fin 3 → ℝ := ![0, 1, 1]
noncomputable def witnessLam₂ : Fin 3 → ℝ := ![1, 0, 1]

theorem witnessP_nonneg : ∀ q ∈ witnessMenu, 0 ≤ witnessP q := by
  intro q _
  fin_cases q <;> simp [witnessP]

theorem witnessP_sum : ∑ q ∈ witnessMenu, witnessP q = 1 := by
  simp [witnessMenu, witnessP, Fin.sum_univ_three]
  norm_num

theorem witnessP_off_zero : ∑ q ∈ witnessMenu \ {0}, witnessP q ≤ 0 * 0 + 1/2 := by
  have h : (witnessMenu \ {0} : Finset (Fin 3)) = {1, 2} := by decide
  rw [h]
  simp [witnessP]

/-- `adequate_set_route` is inhabited: with adequate set `{0}` and coupling slack
`θ = 1/2`, the half-mass on response `1` is exactly the coupled inadequacy mass. -/
theorem adequate_set_route_inhabited :
    anchoredLoss witnessMenu witnessP witnessLam₁ ≤ (1 * 0) * 0 + (0 + 1 * (1/2)) :=
  adequate_set_route witnessMenu {0} (Finset.subset_univ _) witnessP_nonneg witnessP_sum
    le_rfl zero_le_one
    (by intro q hq; simp only [Finset.mem_singleton] at hq; subst hq; simp [witnessLam₁])
    (by intro q _; fin_cases q <;> simp [witnessLam₁])
    witnessP_off_zero

/-- `disjoint_adequate_sets_force_loss` is inhabited, and its bound is attained:
the even split has anchored loss exactly `1/2` on each exposure. -/
theorem disjoint_adequate_sets_force_loss_inhabited :
    (1 : ℝ) ≤ anchoredLoss witnessMenu witnessP witnessLam₁ +
      anchoredLoss witnessMenu witnessP witnessLam₂ :=
  disjoint_adequate_sets_force_loss witnessMenu {0} {1}
    (Finset.subset_univ _) (Finset.subset_univ _) (by decide)
    witnessP_nonneg witnessP_sum zero_le_one
    (by intro q _; fin_cases q <;> simp [witnessLam₁])
    (by intro q _; fin_cases q <;> simp [witnessLam₂])
    (by intro q _ hq; fin_cases q <;> simp_all [witnessLam₁])
    (by intro q _ hq; fin_cases q <;> simp_all [witnessLam₂])

theorem witness_losses_attained :
    anchoredLoss witnessMenu witnessP witnessLam₁ = 1/2 ∧
      anchoredLoss witnessMenu witnessP witnessLam₂ = 1/2 := by
  constructor <;> simp [anchoredLoss, witnessMenu, witnessP, witnessLam₁, witnessLam₂,
    Fin.sum_univ_three]

/-! ## 6. Two necessity facts

The value route's response-adequacy clause presupposes that anchored loss is
regret-dominated.  A response that is value-optimal yet forbidden refutes it: any
`(L, εresp)` making the clause true has `εresp ≥ D`, the whole loss range.  And the
union-bound condition on adequate sets is necessary for joint adequacy with slacks. -/

/-- If a response has zero regret and anchored loss `D`, response adequacy against
regret forces the additive constant to absorb all of `D`. -/
theorem regret_dominance_vacuous_on_forbidden_optimum {L εresp D : ℝ}
    (hresp : D ≤ L * 0 + εresp) : D ≤ εresp := by
  simpa using hresp

/-- Union bound: a distribution whose mass off `A₁` is at most `θ₁` and off `A₂` at
most `θ₂` puts mass at least `1 - θ₁ - θ₂` on `A₁ ∩ A₂`; so if `θ₁ + θ₂ < 1` the
intersection is nonempty.  Stated for the masses. -/
theorem union_bound_two {Q : Type*} [DecidableEq Q] (menu A₁ A₂ : Finset Q)
    {p : Q → ℝ} {θ₁ θ₂ : ℝ}
    (h₁ : A₁ ⊆ menu)
    (hp : ∀ q ∈ menu, 0 ≤ p q) (hprob : ∑ q ∈ menu, p q = 1)
    (hoff₁ : ∑ q ∈ menu \ A₁, p q ≤ θ₁) (hoff₂ : ∑ q ∈ menu \ A₂, p q ≤ θ₂) :
    1 - θ₁ - θ₂ ≤ ∑ q ∈ A₁ ∩ A₂, p q := by
  -- mass on `A₁` is `1 - mass off A₁`; the part of `A₁` outside `A₂` is inside `menu \ A₂`
  have hA₁ : ∑ q ∈ A₁, p q = 1 - ∑ q ∈ menu \ A₁, p q := by
    have := Finset.sum_sdiff (f := p) h₁
    linarith
  have hsplit : ∑ q ∈ A₁, p q = ∑ q ∈ A₁ ∩ A₂, p q + ∑ q ∈ A₁ \ A₂, p q := by
    have := Finset.sum_sdiff (f := p) (Finset.inter_subset_left (s₁ := A₁) (s₂ := A₂))
    rw [Finset.sdiff_inter_self_left] at this
    linarith
  have hleak : ∑ q ∈ A₁ \ A₂, p q ≤ ∑ q ∈ menu \ A₂, p q := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      have hq' := Finset.mem_sdiff.mp hq
      exact Finset.mem_sdiff.mpr ⟨h₁ hq'.1, hq'.2⟩
    · intro q hq _
      exact hp q (Finset.mem_sdiff.mp hq).1
  linarith

/-! ## 7. Headline exposure loss versus edge response loss

The public Progress statistic is indexed by exposures, while practical certificates
are indexed by exposure/service edges.  This adapter lemma is the missing summation
step: supported edges dominate the headline exposure loss, and unmatched row mass is
charged at the global loss bound `D`. -/

/-- A subtransport whose supported edge losses dominate the headline exposure loss
bounds total headline loss by transported edge loss plus the usual residual charge. -/
theorem headline_loss_from_edge_losses {E S : Type*} [DecidableEq E] [DecidableEq S]
    (exposures : Finset E) (services : Finset S)
    {μ ell : E → ℝ} {T edgeLoss : E → S → ℝ} {D : ℝ}
    (hD : 0 ≤ D)
    (hμ : ∀ e ∈ exposures, 0 ≤ μ e)
    (hprob : ∑ e ∈ exposures, μ e = 1)
    (hT : ∀ e ∈ exposures, ∀ s ∈ services, 0 ≤ T e s)
    (hrow : ∀ e ∈ exposures, ∑ s ∈ services, T e s ≤ μ e)
    (hell0 : ∀ e ∈ exposures, 0 ≤ ell e)
    (hellD : ∀ e ∈ exposures, ell e ≤ D)
    (hedge : ∀ e ∈ exposures, ∀ s ∈ services, 0 < T e s → ell e ≤ edgeLoss e s) :
    ∑ e ∈ exposures, μ e * ell e ≤
      (∑ e ∈ exposures, ∑ s ∈ services, T e s * edgeLoss e s) +
        D * (1 - ∑ e ∈ exposures, ∑ s ∈ services, T e s) := by
  have hper : ∀ e ∈ exposures,
      μ e * ell e ≤ (∑ s ∈ services, T e s * edgeLoss e s) +
        D * (μ e - ∑ s ∈ services, T e s) := by
    intro e he
    have hmatched : (∑ s ∈ services, T e s) * ell e ≤
        ∑ s ∈ services, T e s * edgeLoss e s := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro s hs
      by_cases hpos : 0 < T e s
      · exact mul_le_mul_of_nonneg_left (hedge e he s hs hpos) (hT e he s hs)
      · have hz : T e s = 0 := le_antisymm (not_lt.mp hpos) (hT e he s hs)
        simp [hz]
    have hres0 : 0 ≤ μ e - ∑ s ∈ services, T e s := sub_nonneg.mpr (hrow e he)
    have hres : (μ e - ∑ s ∈ services, T e s) * ell e ≤
        D * (μ e - ∑ s ∈ services, T e s) := by
      nlinarith [mul_le_mul_of_nonneg_left (hellD e he) hres0]
    nlinarith
  calc
    ∑ e ∈ exposures, μ e * ell e ≤
        ∑ e ∈ exposures, ((∑ s ∈ services, T e s * edgeLoss e s) +
          D * (μ e - ∑ s ∈ services, T e s)) := by
            apply Finset.sum_le_sum
            intro e he
            exact hper e he
    _ = (∑ e ∈ exposures, ∑ s ∈ services, T e s * edgeLoss e s) +
        D * (1 - ∑ e ∈ exposures, ∑ s ∈ services, T e s) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          rw [Finset.sum_sub_distrib, hprob]

/-! A two-exposure, one-service witness: only the zero-loss exposure is transported;
the unit-loss exposure is paid entirely through residual mass. -/

def headlineWitnessExposures : Finset (Fin 2) := Finset.univ
def headlineWitnessServices : Finset (Fin 1) := Finset.univ
noncomputable def headlineWitnessMu : Fin 2 → ℝ := ![1/2, 1/2]
noncomputable def headlineWitnessLoss : Fin 2 → ℝ := ![0, 1]
noncomputable def headlineWitnessT : Fin 2 → Fin 1 → ℝ := fun e _ => ![1/2, 0] e
noncomputable def headlineWitnessEdgeLoss : Fin 2 → Fin 1 → ℝ := fun e _ => ![0, 1] e

theorem headline_loss_from_edge_losses_inhabited :
    ∑ e ∈ headlineWitnessExposures, headlineWitnessMu e * headlineWitnessLoss e ≤
      (∑ e ∈ headlineWitnessExposures, ∑ s ∈ headlineWitnessServices,
        headlineWitnessT e s * headlineWitnessEdgeLoss e s) +
        1 * (1 - ∑ e ∈ headlineWitnessExposures, ∑ s ∈ headlineWitnessServices,
          headlineWitnessT e s) := by
  apply headline_loss_from_edge_losses headlineWitnessExposures headlineWitnessServices
      (D := 1)
  · norm_num
  · intro e _; fin_cases e <;> simp [headlineWitnessMu]
  · simp [headlineWitnessExposures, headlineWitnessMu, Fin.sum_univ_two]
    norm_num
  · intro e _ s _; fin_cases e <;> fin_cases s <;> simp [headlineWitnessT]
  · intro e _; fin_cases e <;> simp [headlineWitnessT, headlineWitnessMu,
      headlineWitnessServices]
  · intro e _; fin_cases e <;> simp [headlineWitnessLoss]
  · intro e _; fin_cases e <;> simp [headlineWitnessLoss]
  · intro e _ s _ hpos
    fin_cases e <;> fin_cases s <;> simp_all [headlineWitnessT, headlineWitnessLoss,
      headlineWitnessEdgeLoss]

#print axioms proxy_le_defect
#print axioms proxy_route
#print axioms adequate_set_route
#print axioms one_sided_argmax_transfer
#print axioms one_sided_randomized_argmax_transfer
#print axioms bundle_certifiable_iff_zero_defect_adequate
#print axioms disjoint_adequate_sets_force_loss
#print axioms shared_coordinates_bound_disagreement
#print axioms adequate_set_route_inhabited
#print axioms disjoint_adequate_sets_force_loss_inhabited
#print axioms witness_losses_attained
#print axioms regret_dominance_vacuous_on_forbidden_optimum
#print axioms union_bound_two
#print axioms headline_loss_from_edge_losses
#print axioms headline_loss_from_edge_losses_inhabited

end Workspace.Normativity.Contrib.PracticalCertificate

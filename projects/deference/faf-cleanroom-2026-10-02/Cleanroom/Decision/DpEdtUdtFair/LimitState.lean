import Cleanroom.Decision.DpEdtUdtFair.Threat
import Cleanroom.Decision.DpCalibration.MiniDevices

/-!
# Limit-state EDT (D1) approves `(a, y)` on every two-point tree (T7(i), T8's D1 clause)

`calibration.md`'s D1 (`LimitStateEdt`: Definition 10's limit-calibrated states with `T_EDT`)
approves the dominated profile `(a, y)` = `outY` on `twoPoint r₀ r₁ r₂` for **every** payoff
triple, by critique C9's mechanism: the limit state at the null `p2` is *pinned*, not stipulated —
under `outY^ε`, `nuPoly O₂ = ε/2`, `nuPoly (x ∧ O₂) = ε²/4` and `nuPoly (y ∧ O₂) = ε/2 − ε²/4`, so
the limiting conditional probability of `x` given `O₂` is `0` and of `y` is `1`: the pinned state
is `δ_{inY}` with desirability `r₂`, `A_{p2}^+ = {y}`, and `T_EDT` approves `y` by the `A_d^+`
collapse — `x`'s value `r₁` (`= 2 > 0` on the threat tree) is never consulted. At `p1`
(`ν(O₁) = 1 > 0`) the limit state is the strictly calibrated one (`δ_{out}`, desirability `r₀`).

* `twoPoint_nuPoly`, `twoPoint_payPoly` — the tremble polynomials on `twoPoint` as indicator
  sums of products of `trembleW`.
* `trembleW_outY` — the four tremble weights of `(a, y)` as affine polynomials.
* `outY_limitOCAt_p1`, `outY_limitOCAt_p2` — Definition 10 at both points for the pinned states
  `sLimit`.
* **`outY_limitStateEdt`** — D1 approves `(a, y)` on every `twoPoint r₀ r₁ r₂`.
* `threat_outY_limitState`, `fantasy_outY_limitState` — the T8 and T7(i) clauses that
  round 0 left `partial`.
-/

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace Cleanroom.Decision.DpEdtUdtFair

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt
open Cleanroom.Decision.DpCalibration

section polys

variable (r₀ r₁ r₂ : ℚ)

/-- A sum over the three leaves of `twoPoint`, in any additive monoid (`dp-calibration`'s
`twoPoint_sum` is over `ℚ`). Source: none: infrastructure. Kind: L -/
theorem twoPoint_sum' {M : Type} [AddCommMonoid M] (f : (twoPoint r₀ r₁ r₂).Leaves → M) :
    ∑ ℓ, f ℓ = f ⟨.a, ()⟩ + f ⟨.b, .a, ()⟩ + f ⟨.b, .b, ()⟩ := by
  unfold twoPoint at f ⊢
  rw [sum_leaves_decision, Act2.sum_univ, sum_leaves_decision, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf]
  rw [add_assoc]

/-- `nuPoly` on `twoPoint` for any procedure: indicator sum of the three leaves' tremble-weight
products. Source: none: infrastructure. Kind: L -/
theorem twoPoint_nuPoly (C : Proc Pt2 (fun _ => Act2) ℚ) (X : Finset TwoW) :
    nuPoly C (twoPoint r₀ r₁ r₂) X =
      (if TwoW.out ∈ X then trembleW C .p1 .a else 0) +
      (if TwoW.inX ∈ X then trembleW C .p1 .b * trembleW C .p2 .a else 0) +
      (if TwoW.inY ∈ X then trembleW C .p1 .b * trembleW C .p2 .b else 0) := by
  rw [nuPoly_eq_sum, twoPoint_sum']
  simp [twoPoint, leafLawPoly, world_decision, world_leaf]

/-- `payPoly` on `twoPoint` for any procedure. Source: none: infrastructure. Kind: L -/
theorem twoPoint_payPoly (C : Proc Pt2 (fun _ => Act2) ℚ) (X : Finset TwoW) :
    payPoly C (twoPoint r₀ r₁ r₂) X =
      (if TwoW.out ∈ X then trembleW C .p1 .a * Polynomial.C r₀ else 0) +
      (if TwoW.inX ∈ X then trembleW C .p1 .b * trembleW C .p2 .a * Polynomial.C r₁ else 0) +
      (if TwoW.inY ∈ X then trembleW C .p1 .b * trembleW C .p2 .b * Polynomial.C r₂ else 0) := by
  rw [payPoly_eq_sum, twoPoint_sum']
  simp [twoPoint, leafLawPoly, world_decision, world_leaf, payoff_decision, payoff_leaf, mul_assoc]

/-- The tremble weights of `(a, y)`: `1 − ε/2`, `ε/2` at `p1`; `ε/2`, `1 − ε/2` at `p2`.
Source: `fair-repair.md` §3.2 ("Under trembles"); critique C9
Kind: L -/
theorem trembleW_outY :
    trembleW outY .p1 .a = Polynomial.C 1 + Polynomial.C (-1 / 2) * Polynomial.X ∧
    trembleW outY .p1 .b = Polynomial.C (1 / 2) * Polynomial.X ∧
    trembleW outY .p2 .a = Polynomial.C (1 / 2) * Polynomial.X ∧
    trembleW outY .p2 .b = Polynomial.C 1 + Polynomial.C (-1 / 2) * Polynomial.X := by
  have hc : (Fintype.card Act2 : ℚ) = 2 := by
    rw [Fintype.card, Act2.univ_eq, Finset.card_pair (by decide)]; norm_num
  simp only [trembleW, outY, proc2_p1, proc2_p2, FinDistr.act2_a, FinDistr.act2_b, hc]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-- `ν` and the payoff mass of `X ∧ O₁` under `(a, y)`: `[out ∈ X]` and `r₀ [out ∈ X]`.
Source: none: infrastructure. Kind: L -/
theorem outY_nu_paySum_inter_p1 (X : Finset TwoW) :
    nu outY (twoPoint r₀ r₁ r₂) (X ∩ twoObs .p1) = (if TwoW.out ∈ X then 1 else 0) ∧
    paySum outY (twoPoint r₀ r₁ r₂) (X ∩ twoObs .p1) = (if TwoW.out ∈ X then r₀ else 0) := by
  constructor
  · show nu (proc2 1 0 _ _ _ _) _ _ = _
    rw [twoPoint_nu]; simp [twoObs]
  · show paySum (proc2 1 0 _ _ _ _) _ _ = _
    rw [twoPoint_paySum]; simp [twoObs]

/-- `nuPoly (X ∧ O₂)` under `(a, y)`: `[x ∈ X] ε²/4 + [y ∈ X] (ε/2 − ε²/4)`.
Source: critique C9 (the pinned state's numbers)
Kind: L -/
theorem outY_nuPoly_inter_p2 (X : Finset TwoW) :
    nuPoly outY (twoPoint r₀ r₁ r₂) (X ∩ twoObs .p2) =
      (if TwoW.inX ∈ X then Polynomial.C (1 / 4) * Polynomial.X ^ 2 else 0) +
      (if TwoW.inY ∈ X then
        Polynomial.C (1 / 2) * Polynomial.X + Polynomial.C (-1 / 4) * Polynomial.X ^ 2 else 0) := by
  obtain ⟨-, hb1, ha2, hb2⟩ := trembleW_outY
  rw [twoPoint_nuPoly, hb1, ha2, hb2]
  have e1 : Polynomial.C (1 / 2 : ℚ) * Polynomial.X * (Polynomial.C (1 / 2) * Polynomial.X) =
      Polynomial.C (1 / 4 : ℚ) * Polynomial.X ^ 2 := by
    rw [show (1 / 4 : ℚ) = 1 / 2 * (1 / 2) by norm_num, Polynomial.C_mul]; ring
  have e2 : Polynomial.C (1 / 2 : ℚ) * Polynomial.X *
      (Polynomial.C 1 + Polynomial.C (-1 / 2) * Polynomial.X) =
      Polynomial.C (1 / 2 : ℚ) * Polynomial.X + Polynomial.C (-1 / 4 : ℚ) * Polynomial.X ^ 2 := by
    rw [show (-1 / 4 : ℚ) = 1 / 2 * (-1 / 2) by norm_num, Polynomial.C_mul, Polynomial.C_1]; ring
  rw [e1, e2]
  simp [twoObs]

/-- `payPoly (X ∧ O₂)` under `(a, y)`. Source: critique C9. Kind: L -/
theorem outY_payPoly_inter_p2 (X : Finset TwoW) :
    payPoly outY (twoPoint r₀ r₁ r₂) (X ∩ twoObs .p2) =
      (if TwoW.inX ∈ X then Polynomial.C (1 / 4) * Polynomial.X ^ 2 * Polynomial.C r₁ else 0) +
      (if TwoW.inY ∈ X then
        (Polynomial.C (1 / 2) * Polynomial.X + Polynomial.C (-1 / 4) * Polynomial.X ^ 2) *
          Polynomial.C r₂ else 0) := by
  obtain ⟨-, hb1, ha2, hb2⟩ := trembleW_outY
  rw [twoPoint_payPoly, hb1, ha2, hb2]
  have e1 : Polynomial.C (1 / 2 : ℚ) * Polynomial.X * (Polynomial.C (1 / 2) * Polynomial.X) =
      Polynomial.C (1 / 4 : ℚ) * Polynomial.X ^ 2 := by
    rw [show (1 / 4 : ℚ) = 1 / 2 * (1 / 2) by norm_num, Polynomial.C_mul]; ring
  have e2 : Polynomial.C (1 / 2 : ℚ) * Polynomial.X *
      (Polynomial.C 1 + Polynomial.C (-1 / 2) * Polynomial.X) =
      Polynomial.C (1 / 2 : ℚ) * Polynomial.X + Polynomial.C (-1 / 4 : ℚ) * Polynomial.X ^ 2 := by
    rw [show (-1 / 4 : ℚ) = 1 / 2 * (-1 / 2) by norm_num, Polynomial.C_mul, Polynomial.C_1]; ring
  rw [e1, e2]
  simp [twoObs]

/-- Coefficients `0`, `1` of `C a · X + C b · X²` and of `C b · X²`. Source: none: infrastructure.
Kind: L -/
theorem coeff01_quad (a b : ℚ) :
    (Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X ^ 2).coeff 0 = 0 ∧
    (Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X ^ 2).coeff 1 = a ∧
    (Polynomial.C b * Polynomial.X ^ 2).coeff 0 = 0 ∧
    (Polynomial.C b * Polynomial.X ^ 2).coeff 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Polynomial.coeff_add]

/-- The low coefficients of `nuPoly (X ∧ O₂)` under `(a, y)`: `0` and `[y ∈ X]/2`.
Source: critique C9
Kind: L -/
theorem outY_nuPoly_inter_p2_coeff (X : Finset TwoW) :
    (nuPoly outY (twoPoint r₀ r₁ r₂) (X ∩ twoObs .p2)).coeff 0 = 0 ∧
    (nuPoly outY (twoPoint r₀ r₁ r₂) (X ∩ twoObs .p2)).coeff 1 =
      (if TwoW.inY ∈ X then 1 / 2 else 0) := by
  rw [outY_nuPoly_inter_p2]
  obtain ⟨q0, q1, s0, s1⟩ := coeff01_quad (1 / 2 : ℚ) (-1 / 4)
  obtain ⟨-, -, t0, t1⟩ := coeff01_quad (0 : ℚ) (1 / 4)
  constructor <;> rw [Polynomial.coeff_add] <;> split_ifs <;> simp [q0, q1, t0, t1]

/-- The coefficient `1` of `payPoly (X ∧ O₂)` under `(a, y)`: `[y ∈ X] r₂/2`.
Source: critique C9
Kind: L -/
theorem outY_payPoly_inter_p2_coeff (X : Finset TwoW) :
    (payPoly outY (twoPoint r₀ r₁ r₂) (X ∩ twoObs .p2)).coeff 1 =
      (if TwoW.inY ∈ X then r₂ / 2 else 0) := by
  rw [outY_payPoly_inter_p2]
  obtain ⟨q0, q1, s0, s1⟩ := coeff01_quad (1 / 2 : ℚ) (-1 / 4)
  obtain ⟨-, -, t0, t1⟩ := coeff01_quad (0 : ℚ) (1 / 4)
  rw [Polynomial.coeff_add]
  split_ifs <;> simp only [Polynomial.coeff_mul_C, Polynomial.coeff_zero, q1, t1] <;> ring

/-- `nuPoly O₂` under `(a, y)` has order `1` with trailing coefficient `½` (`ε/2`).
Source: critique C9 ("`ν_ε(O₂) = ε/2`")
Kind: L -/
theorem outY_nuPoly_obs_p2 :
    (nuPoly outY (twoPoint r₀ r₁ r₂) (twoObs .p2)).natTrailingDegree = 1 ∧
    (nuPoly outY (twoPoint r₀ r₁ r₂) (twoObs .p2)).coeff 1 = 1 / 2 ∧
    nuPoly outY (twoPoint r₀ r₁ r₂) (twoObs .p2) ≠ 0 := by
  have h := outY_nuPoly_inter_p2_coeff r₀ r₁ r₂ Finset.univ
  rw [Finset.univ_inter] at h
  simp only [Finset.mem_univ, if_true] at h
  have hdeg : (nuPoly outY (twoPoint r₀ r₁ r₂) (twoObs .p2)).natTrailingDegree = 1 :=
    natTrailingDegree_eq_of_coeff _ 1
      (fun j hj => by
        have : j = 0 := by omega
        subst this; exact h.1)
      (by rw [h.2]; norm_num)
  refine ⟨hdeg, h.2, fun hz => ?_⟩
  rw [hz, Polynomial.coeff_zero] at h
  norm_num at h

end polys

/-! ### The pinned states and Definition 10 at both points -/

section states

variable (r₀ r₁ r₂ : ℚ)

/-- **The pinned limit states of `(a, y)`**: certain of `out` with desirability `r₀` at `p1`
(the strictly calibrated state), certain of `inY` with desirability `r₂` at the null `p2` (the
tremble-limit state: `x` has limiting conditional probability `0`).
Source: critique C9 ("the state is pinned"); [[decision-problems-v2]] Definition 10
Kind: D -/
noncomputable def sLimit : Pt2 → State TwoW ℚ
  | .p1 => State.dirac .out r₀
  | .p2 => State.dirac .inY r₂

/-- Definition 10 at `p1` for the pinned states: `ν(O₁) = 1 > 0`, so the limit clauses are the
strict ones (`P = δ_{out}`, `V = r₀` where `out ∈ X`).
Source: [[decision-problems-v2]] Definition 10, Lemma 2 proof
Kind: L -/
theorem outY_limitOCAt_p1 : LimitOCAt (sLimit r₀ r₂) twoObs outY (twoPoint r₀ r₁ r₂) .p1 := by
  intro _
  have hpos : 0 < nu outY (twoPoint r₀ r₁ r₂) (twoObs .p1) := by
    rw [(outY_nu_obs r₀ r₁ r₂).1]; exact one_pos
  refine ⟨fun X => ?_, fun X hX => ?_⟩
  · rw [limitCond_eq_of_pos _ _ _ _ hpos, (outY_nu_paySum_inter_p1 r₀ r₁ r₂ X).1,
      (outY_nu_obs r₀ r₁ r₂).1, div_one]
    show (State.dirac .out r₀).pr X = _
    rw [State.dirac_pr]
  · rw [limitCond_eq_of_pos _ _ _ _ hpos, (outY_nu_paySum_inter_p1 r₀ r₁ r₂ X).1,
      (outY_nu_obs r₀ r₁ r₂).1, div_one] at hX
    have hout : TwoW.out ∈ X := by
      by_contra h
      rw [if_neg h] at hX
      exact lt_irrefl _ hX
    have hXpos : 0 < nu outY (twoPoint r₀ r₁ r₂) (X ∩ twoObs .p1) := by
      rw [(outY_nu_paySum_inter_p1 r₀ r₁ r₂ X).1, if_pos hout]; exact one_pos
    rw [(natTrailingDegree_nuPoly_eq_zero _ _ _ hXpos).1, coeff_zero_nuPoly, coeff_zero_payPoly,
      (outY_nu_paySum_inter_p1 r₀ r₁ r₂ X).1, (outY_nu_paySum_inter_p1 r₀ r₁ r₂ X).2,
      if_pos hout, if_pos hout]
    show (State.dirac .out r₀).V X * 1 = r₀
    rw [State.dirac_V, mul_one]

/-- **Definition 10 at the null `p2` for the pinned states** (critique C9's mechanism): the
limiting conditional of `X` given `O₂` is `[y ∈ X]` (`nuPoly O₂ = ε/2`, `nuPoly (X ∧ O₂)` has
coefficient `[y ∈ X]/2` at `ε`), so `P_{s₂} = δ_{inY}`; where it is positive, `nuPoly (X ∧ O₂)`
has order `1` and the `V`-clause reads `V_{s₂}(X) · ½ = r₂/2`.
Source: critique C9; [[decision-problems-v2]] Definition 10
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem outY_limitOCAt_p2 : LimitOCAt (sLimit r₀ r₂) twoObs outY (twoPoint r₀ r₁ r₂) .p2 := by
  intro _
  obtain ⟨hdeg, hc1, -⟩ := outY_nuPoly_obs_p2 r₀ r₁ r₂
  refine ⟨fun X => ?_, fun X hX => ?_⟩
  · unfold limitCond
    rw [hdeg, hc1, (outY_nuPoly_inter_p2_coeff r₀ r₁ r₂ X).2]
    show (State.dirac .inY r₂).pr X = _
    rw [State.dirac_pr]
    split_ifs <;> norm_num
  · unfold limitCond at hX
    rw [hdeg, hc1, (outY_nuPoly_inter_p2_coeff r₀ r₁ r₂ X).2] at hX
    have hy : TwoW.inY ∈ X := by
      by_contra h
      rw [if_neg h] at hX
      norm_num at hX
    have hdeg' : (nuPoly outY (twoPoint r₀ r₁ r₂) (X ∩ twoObs .p2)).natTrailingDegree = 1 :=
      natTrailingDegree_eq_of_coeff _ 1
        (fun j hj => by
          have : j = 0 := by omega
          subst this; exact (outY_nuPoly_inter_p2_coeff r₀ r₁ r₂ X).1)
        (by rw [(outY_nuPoly_inter_p2_coeff r₀ r₁ r₂ X).2, if_pos hy]; norm_num)
    rw [hdeg', (outY_nuPoly_inter_p2_coeff r₀ r₁ r₂ X).2, outY_payPoly_inter_p2_coeff, if_pos hy,
      if_pos hy]
    show (State.dirac .inY r₂).V X * (1 / 2) = r₂ / 2
    rw [State.dirac_V]; ring

/-- **D1 (limit-state EDT) approves `(a, y)` on every two-point tree**, with the pinned states
`sLimit`: Definition 10 at both points, and `T_EDT` — at `p1`, `A^+ = {out}` and `out` is the
played act; at the null `p2`, `A^+ = {y}` (the limiting conditional probability of `x` is `0`),
so `y` is approved by the `A_d^+` collapse without its value `r₁` ever being compared. This is
C9's "pinned state" mechanism, the third untrembled sense of A36 (iii), now machine-checked.
Source: `critique.md` C9; `v2-amendments.md` A36 (iii); `calibration.md` D1; mandate T8
("`LimitStateEdt` (pinned state, `A^+ = {y}`)")
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem outY_limitStateEdt :
    LimitStateEdt twoObs twoActEv outY (twoPoint r₀ r₁ r₂) (sLimit r₀ r₂) := by
  refine ⟨fun d _ => ?_, fun d _ _ a ha => ?_⟩
  · cases d
    · exact outY_limitOCAt_p1 r₀ r₁ r₂
    · exact outY_limitOCAt_p2 r₀ r₁ r₂
  · rw [mem_argmaxPlus]
    cases d <;> cases a <;> simp [outY, proc2, FinDistr.act2] at ha <;>
      simp [APlus, sLimit, State.dirac_pr, State.dirac_V, twoActEv]

end states

/-! ### The T8 and T7(i) clauses -/

section rows

/-- **T8's D1 clause**: limit-state EDT approves `(a, y)` on the threat tree with the pinned
states (`A_{p2}^+ = {y}`), although `x`'s continuation value is `2 > 0`.
Source: `identity.md` Dead 1; A36 (iii); critique C9; mandate T8
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem threat_outY_limitState :
    ∃ s, LimitStateEdt twoObs twoActEv outY threat s ∧
      s .p2 = State.dirac .inY 0 ∧ (s .p2).pr (twoActEv .p2 .a) = 0 :=
  ⟨sLimit 1 0, outY_limitStateEdt 1 2 0, rfl, by
    show (State.dirac .inY 0).pr {TwoW.inX} = 0
    rw [State.dirac_pr]; simp⟩

/-- **T7(i)'s D1 clause**: limit-state EDT approves `(a, y)` on `fantasy241` with the pinned
states.
Source: `fair-repair.md` §3.2; A36 (iii); critique C9; mandate T7(i)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem fantasy_outY_limitState :
    ∃ s, LimitStateEdt twoObs twoActEv outY fantasy241 s ∧ s .p2 = State.dirac .inY 1 :=
  ⟨sLimit 2 1, outY_limitStateEdt 2 4 1, rfl⟩

/-- **T8, all untrembled senses on the threat tree** (the refutation row of identity Dead 1 with
its D1 clause): `threat_outY_untrembled`'s clauses — `threat ∈ 𝔉`, Definition 22 (pure, mixed),
Theorem 1, Theorem 2, strict-OC EDT, masked EDT, `¬ D2`, `¬ IsOptimal`, the values — together
with limit-state EDT's approval by the pinned states. Every untrembled sense named in A36 (iii)
approves `(a, y)`; only the tremble (D2) rejects it.
Source: `identity.md` Dead 1 (l. 124); A36 (iii); critique C9; mandate T8
Kind: N+ (refutation instance)
Fidelity: exact
Hyps: (a) all -/
theorem threat_outY_untrembled_all :
    FairClass twoObs twoActEv threat ∧
    Coherent outY threat ∧ CoherentPure outY threat ∧ Thm1 outY threat ∧
    (∀ d ∈ queried threat, ∀ m, ssaValue outY threat d m ≤ ssaValue outY threat d (outY d)) ∧
    (∃ s, StrictOC s twoObs outY threat ∧ TEdt s twoActEv outY threat) ∧
    (∃ s, MaskedOC s twoObs outY threat ∧ TEdt s twoActEv outY threat) ∧
    (∃ s, LimitStateEdt twoObs twoActEv outY threat s) ∧
    ¬ EventTrembleEdtConsistent twoObs twoActEv outY threat ∧
    ¬ IsOptimal outY threat ∧ value outY threat = 1 ∧ value inX threat = 2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := threat_outY_untrembled
  exact ⟨h1, h2, h3, h4, h5, h6, h7, ⟨_, outY_limitStateEdt 1 2 0⟩, h8, h9, h10, h11⟩

/-- **T7(i), no trembles, with the D1 clause**: on `fantasy241 ∈ 𝔉`, `(a, y)` is approved by
strict-OC EDT (stipulated state), masked EDT (vacuity), limit-state EDT (pinned state),
Definition 22 and Theorem 1, is D2-rejected and not optimal (`V = 2 < 4`).
Source: `fair-repair.md` §3.2; A36 (iii); critique C9; mandate T7(i)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem fantasy_outY_untrembled_all :
    FairClass twoObs twoActEv fantasy241 ∧
    (∃ s, StrictOC s twoObs outY fantasy241 ∧ TEdt s twoActEv outY fantasy241) ∧
    (∃ s, MaskedOC s twoObs outY fantasy241 ∧ TEdt s twoActEv outY fantasy241) ∧
    (∃ s, LimitStateEdt twoObs twoActEv outY fantasy241 s) ∧
    Coherent outY fantasy241 ∧ Thm1 outY fantasy241 ∧
    ¬ EventTrembleEdtConsistent twoObs twoActEv outY fantasy241 ∧
    ¬ IsOptimal outY fantasy241 ∧ value outY fantasy241 = 2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := fantasy_outY_untrembled
  exact ⟨h1, h2, h3, ⟨_, outY_limitStateEdt 2 4 1⟩, h4, h5, h6, h7, h8⟩

end rows

end Cleanroom.Decision.DpEdtUdtFair

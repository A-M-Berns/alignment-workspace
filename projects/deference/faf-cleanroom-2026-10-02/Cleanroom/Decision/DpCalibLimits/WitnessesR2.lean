import Cleanroom.Decision.DpCalibLimits.WitnessesR1
import Cleanroom.Decision.DpCalibLimits.SinglePoint
import Cleanroom.Decision.DpCalibLimits.Traps

/-!
# Repair round 2 — non-degenerate witnesses ([[STANDARDS]] §3)

Audit round 2 (adversarial B1; adversarial N2, N3; fidelity N1) found one witness graded N+ that
is degenerate, and three headlines whose non-degenerate inhabitants existed only in the
auditors' probes (`run/wp/dp-calib-limits/audit-r2-probes/`). This module ships them, lifted and
extended:

* **The corollary `condExp_deviate_eq` on a tree with coin-dependent payoffs** (adversarial B1):
  on `cqPay` (coin, then the query; payoff `1` on heads, `0` on tails, for either act) the whole
  hypothesis package holds, the masked and strict act values of `a` agree, and the common value is
  `½` — not `0`. `coinQuery_condExp_deviate` (`WitnessesR1.lean`) is regraded N−: every payoff on
  `coinQuery` is `0`, so its `0 = 0` says nothing about the cancellation.
* **Both sides of `tb_masked_flip`** (adversarial N2): at `θ = ½`, `m = (¼, ¾)` the event-conditioned
  masked state prices `cross` below `0`; at `θ = ¼`, `m = (½, ½)` above `0`.
* **`twoAct_single_point_ray_independent` with bite** (adversarial N3): on `coinQuery` with
  `C = δ_b`, the `δ_b`-null observation `{act = a}`, the uniform ray (`w_a = ε/2`, order `1`) and
  `raySq` (`w_a = ε²`, order `2`) give the same `P({(H, a)} | {act = a}) = ½`.
* **`msr17At_of_msrAt_recorded`'s package with a strict maximum** (fidelity N1): on the recorded
  `t1` with `δ_b` the four hypotheses hold and the supported act is the *strict* maximiser,
  `limitVal a = 0 < 1 = limitVal b`; `coinQuery_msr17_instance` stays as the N− (all payoffs tie).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-! ## B1: `condExp_deviate_eq` on a tree whose values are not identically `0` -/

section cqpay

/-- Coin, then the query, with payoff `1` on heads and `0` on tails for either act (`coinQuery`'s
shape with a coin-dependent payoff). Source: audit r2 adversarial B1. Kind: D -/
def cqPay : Tree CoinQueryW Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i =>
    .decision () fun act => .leaf (decide (i = 0), act) (if i = 0 then 1 else 0)

/-- A sum over the leaves of `cqPay`. Source: none: infrastructure. Kind: L -/
theorem cqPay_sum {M : Type} [AddCommMonoid M] (f : cqPay.Leaves → M) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ∑ act : Act2, f ⟨i, act, ()⟩ := by
  unfold cqPay at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun act _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- Every leaf of `cqPay` meets the query point once. Source: none: infrastructure. Kind: L -/
theorem cqPay_count (ℓ : cqPay.Leaves) : count () cqPay ℓ = 1 := by
  unfold cqPay at ℓ ⊢
  rcases ℓ with ⟨i, act, _⟩
  simp [count]

/-- `cqObs` covers `cqPay` under every procedure. Source: none: infrastructure. Kind: L -/
theorem cqPay_covers (C : Proc Unit (fun _ => Act2) ℚ) : Covers cqObs C cqPay () := by
  intro ℓ _ _
  rw [cqPay_count]; exact one_pos

/-- Leaf-level action veridicality on `cqPay`. Source: none: infrastructure. Kind: L -/
theorem cqPay_hav : ∀ (ℓ : cqPay.Leaves) (a : Act2),
    (⟨(), a⟩ : Σ d : Unit, Act2) ∈ draws cqPay ℓ → world cqPay ℓ ∈ cqActEv () a := by
  intro ℓ a h
  unfold cqPay at ℓ h ⊢
  rcases ℓ with ⟨i, act, _⟩
  simp [draws] at h
  subst h
  simp [world, cqActEv]

/-- The strict act value of `a` under `procQ ½` on `cqPay` is `½` (heads pays `1`, tails `0`).
Source: none: infrastructure. Kind: L -/
theorem cqPay_condExp_half :
    condExp (procQ (1/2) (by norm_num) (by norm_num)) cqPay (cqActEv () .a ∩ cqObs ()) = 1 / 2 := by
  unfold condExp
  rw [paySum_eq_sum_ite, nu_eq_sum, cqPay_sum, cqPay_sum]
  simp [cqPay, leafLaw, cqActEv, cqObs, procQ, Fin.sum_univ_two, Act2.sum_univ, FinDistr.fair,
    FinDistr.coin]
  try norm_num

/-- **`condExp_deviate_eq`'s package inhabited where the values are not `0`**: on `cqPay` with
`procQ ½` and the uniform self-model, `#_d ≤ 1`, coverage, leaf-level action veridicality,
disjoint action events and both positivities hold; the masked act value of `a` equals the strict
one; and the common value is `½` — numerator and denominator both carry the factor `m(a)`, which
is the lemma's mechanism, on a non-zero quantity. (`coinQuery_condExp_deviate` is the same
corollary where every value is `0`: N−.)
Source: mandate T6(b); dp-cf-2-042; audit r2 adversarial B1
Kind: N+
Fidelity: exact
Hyps: none -/
theorem cqPay_condExp_deviate_nontrivial :
    condExp ((procQ (1/2) (by norm_num) (by norm_num)).deviate () FinDistr.uniform) cqPay
        (cqActEv () .a ∩ cqObs ()) =
      condExp (procQ (1/2) (by norm_num) (by norm_num)) cqPay (cqActEv () .a ∩ cqObs ()) ∧
    condExp (procQ (1/2) (by norm_num) (by norm_num)) cqPay (cqActEv () .a ∩ cqObs ()) = 1 / 2 := by
  refine ⟨?_, cqPay_condExp_half⟩
  apply condExp_deviate_eq cqObs cqActEv _ cqPay () FinDistr.uniform .a
    (fun ℓ => (cqPay_count ℓ).le) (cqPay_covers _) cqPay_hav cqActEv_disjoint
  · rw [nu_eq_sum, cqPay_sum]
    simp [cqPay, leafLaw, cqActEv, cqObs, FinDistr.uniform_w, Proc.deviate_same, act2_card_rat,
      Fin.sum_univ_two, FinDistr.fair, FinDistr.coin]
    try norm_num
  · rw [nu_eq_sum, cqPay_sum]
    simp [cqPay, leafLaw, cqActEv, cqObs, procQ, Fin.sum_univ_two, FinDistr.fair, FinDistr.coin]
    try norm_num

end cqpay

/-! ## Adversarial N2: both sides of `tb_masked_flip` -/

section tbflip

/-- The self-model `(¼, ¾)`. Source: none: infrastructure. Kind: D -/
def quarter : FinDistr ℚ Act2 := FinDistr.act2 (1 / 4) (by norm_num) (by norm_num)

/-- `quarter` is full-support. Source: none: infrastructure. Kind: L -/
theorem quarter_pos (x : Act2) : 0 < quarter.w x := by cases x <;> norm_num [quarter]

/-- **Below `q*`**: `θ = ½`, `m(a) = ¼`, `(1−θ)m(a) = ⅛ < ½`, so the event-conditioned masked
state prices `cross` below `0` and `tb_masked_flip` approves `δ_not`.
Source: P11-11′, P11-12′(f); audit r2 adversarial N2. Kind: N+. Fidelity: exact. Hyps: none -/
theorem tb_flip_below :
    (tbMaskedState (1/2) (by norm_num) (by norm_num) quarter).V (tbActEv .d .a) < 0 :=
  (tb_masked_flip (1/2) (by norm_num) (by norm_num) quarter quarter_pos).1
    (by simp [quarter]; norm_num)

/-- **Above `q*`**: `θ = ¼`, `m(a) = ½`, `(1−θ)m(a) = ⅜ > ¼`, so the event-conditioned masked
state prices `cross` above `0` and `tb_masked_flip` rejects `δ_not`. With `tb_flip_below` the
verdict does flip.
Source: P11-11′, P11-12′(f); audit r2 adversarial N2. Kind: N+. Fidelity: exact. Hyps: none -/
theorem tb_flip_above :
    0 < (tbMaskedState (1/4) (by norm_num) (by norm_num) half).V (tbActEv .d .a) :=
  (tb_masked_flip (1/4) (by norm_num) (by norm_num) half half_pos).2.1
    (by simp [half]; norm_num)

end tbflip

/-! ## Adversarial N3: `twoAct_single_point_ray_independent` on a non-trivial instance -/

section twoact

/-- A full-support ray of `δ_b` with `w_a = ε²` (order `2`; the uniform ray has `w_a = ε/2`,
order `1`). Source: audit r2 adversarial N3. Kind: D -/
noncomputable def raySq : Ray Unit (fun _ => Act2) ℚ where
  w := fun _ x => match x with
    | .a => Polynomial.X ^ 2
    | .b => Polynomial.C 1 - Polynomial.X ^ 2
  sum_one _ := by rw [Act2.sum_univ]; simp only; ring
  posTrail _ x := by
    cases x
    · exact PosTrail.pow PosTrail.X 2
    · exact posTrail_one_sub_X_pow 2 two_pos

/-- `raySq` starts at `δ_b`. Source: none: infrastructure. Kind: L -/
theorem raySq_isRayOf : IsRayOf raySq procB1 := by
  intro _ x
  cases x <;> simp [raySq, procB1, Polynomial.coeff_sub, Polynomial.coeff_X_pow]

/-- `raySq` is full-support. Source: none: infrastructure. Kind: L -/
theorem raySq_fullSupport : raySq.FullSupport := by
  intro _ x
  cases x
  · exact pow_ne_zero 2 Polynomial.X_ne_zero
  · intro h
    have := congrArg (fun p : Polynomial ℚ => p.coeff 0) h
    simp [raySq, Polynomial.coeff_sub, Polynomial.coeff_X_pow] at this

/-- The uniform ray is full-support. Source: none: infrastructure. Kind: L -/
theorem uniformRay_fullSupport (C : Proc Unit (fun _ => Act2) ℚ) : (uniformRay C).FullSupport :=
  fun d x => trembleW_ne_zero C d x

/-- A sum over the leaves of `coinQuery` with values in any additive monoid (the ℚ-valued
`coinQuery_sum` does not cover polynomial sums). Source: none: infrastructure. Kind: L -/
theorem coinQuery_psum {M : Type} [AddCommMonoid M] (f : coinQuery.Leaves → M) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ∑ act : Act2, f ⟨i, act, ()⟩ := by
  unfold coinQuery at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun act _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- The uniform-ray coefficients of `δ_b` on `coinQuery` at the `a`-event: order `1`,
`coeff 1 = ½`; the heads sub-event has `coeff 1 = ¼`. Source: none: infrastructure. Kind: L -/
theorem procB1_uniform_coeffs :
    (nuPolyRay (uniformRay procB1) coinQuery (cqActEv () .a)).coeff 0 = 0 ∧
    (nuPolyRay (uniformRay procB1) coinQuery (cqActEv () .a)).coeff 1 = 1 / 2 ∧
    (nuPolyRay (uniformRay procB1) coinQuery ({(true, Act2.a)} ∩ cqActEv () .a)).coeff 1 = 1 / 4 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Polynomial.coeff_zero_eq_eval_zero, nuPolyRay_eq_sum, coinQuery_psum]
    simp [coinQuery, leafLawPolyRay, uniformRay, trembleW, cqActEv, procB1, FinDistr.pure_w,
      Fin.sum_univ_two, FinDistr.fair, FinDistr.coin, act2_card_rat]
  · rw [coeff_one_eq_eval_zero_derivative, nuPolyRay_eq_sum, coinQuery_psum]
    simp [coinQuery, leafLawPolyRay, uniformRay, trembleW, cqActEv, procB1, FinDistr.pure_w,
      Fin.sum_univ_two, FinDistr.fair, FinDistr.coin, act2_card_rat]
    try norm_num
  · rw [coeff_one_eq_eval_zero_derivative, nuPolyRay_eq_sum, coinQuery_psum]
    simp [coinQuery, leafLawPolyRay, uniformRay, trembleW, cqActEv, procB1, FinDistr.pure_w,
      Act2.sum_univ, FinDistr.fair, FinDistr.coin, act2_card_rat]
    try norm_num

/-- **`twoAct_single_point_ray_independent` has bite**: on `coinQuery` with `C = δ_b` the
observation `{act = a}` is `δ_b`-null (so the strict conditional is undefined and only a ray
decides), the uniform ray (`w_a = ε/2`, order `1`) gives `P({(H, a)} | {act = a}) = ½` from its
order-1 coefficients, and `raySq` (`w_a = ε²`, order `2` — a genuinely different full-support ray
of `δ_b`) gives the same `½` through the theorem. The theorem's own package is also inhabited
trivially (the uniform ray twice); this is the instance where the two rays differ.
Source: mandate T2(d); P07 I2′; audit r2 adversarial N3
Kind: N+
Fidelity: exact
Hyps: none -/
theorem coinQuery_twoAct_instance :
    nu procB1 coinQuery (cqActEv () .a) = 0 ∧
    limitCondRay (uniformRay procB1) coinQuery {(true, Act2.a)} (cqActEv () .a) = 1 / 2 ∧
    limitCondRay raySq coinQuery {(true, Act2.a)} (cqActEv () .a) = 1 / 2 := by
  obtain ⟨h0, h1, hX⟩ := procB1_uniform_coeffs
  have huni : limitCondRay (uniformRay procB1) coinQuery {(true, Act2.a)} (cqActEv () .a) = 1 / 2 := by
    rw [limitCondRay_of_coeff_one _ _ _ _ h0 (by rw [h1]; norm_num), hX, h1]; norm_num
  refine ⟨?_, huni, ?_⟩
  · rw [coinQuery_nu]; simp [cqActEv, procB1]
  · rw [twoAct_single_point_ray_independent coinQuery procB1 raySq (uniformRay procB1) raySq_isRayOf
      (isRayOf_uniformRay _) raySq_fullSupport (uniformRay_fullSupport _)]
    exact huni

end twoact

/-! ## Fidelity N1: `msr17At_of_msrAt_recorded`'s package with a strict maximum -/

section msr17

/-- The strict state of `δ_b` on `t1`. Source: none: infrastructure. Kind: D -/
noncomputable def t1BStrictState : State Act2 ℚ :=
  calibratedState procB1 t1 (t1Obs ()) (by show 0 < nu procB1 t1 Finset.univ; exact nu_univ_pos _ _)

/-- The uniform-ray coefficients of `δ_b` at `t1`: the `a`-event has order `1` with
`nuPoly.coeff 1 = ½` and `payPoly.coeff 1 = 0` (`a` pays `0`). Source: none: infrastructure.
Kind: L -/
theorem t1_a_coeffs :
    (nuPoly procB1 t1 (t1ActEv () .a ∩ t1Obs ())).coeff 0 = 0 ∧
    (nuPoly procB1 t1 (t1ActEv () .a ∩ t1Obs ())).coeff 1 = 1 / 2 ∧
    (payPoly procB1 t1 (t1ActEv () .a ∩ t1Obs ())).coeff 1 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Polynomial.coeff_zero_eq_eval_zero, nuPoly_eq_sum, t1_sum]
    simp [t1, leafLawPoly, trembleW, t1ActEv, t1Obs, procB1, act2_card_rat]
  · rw [coeff_one_eq_eval_zero_derivative, nuPoly_eq_sum, t1_sum]
    simp [t1, leafLawPoly, trembleW, t1ActEv, t1Obs, procB1, act2_card_rat]
  · rw [coeff_one_eq_eval_zero_derivative, payPoly_eq_sum, t1_sum]
    simp [t1, leafLawPoly, trembleW, t1ActEv, t1Obs, procB1, act2_card_rat]

/-- The tremble-pinned values of `δ_b` on `t1`: `limitVal a = 0` (order `1`, payoff `0`) and
`limitVal b = 1` (realized, `limitVal_eq_of_pos`). Source: none: infrastructure. Kind: L -/
theorem t1_procB1_limitVals :
    limitVal procB1 t1 (t1ActEv () .a ∩ t1Obs ()) = 0 ∧
    limitVal procB1 t1 (t1ActEv () .b ∩ t1Obs ()) = 1 := by
  obtain ⟨a0, a1, ap1⟩ := t1_a_coeffs
  have hbpos : 0 < nu procB1 t1 (t1ActEv () .b ∩ t1Obs ()) := by
    rw [t1_nu]; simp [t1ActEv, t1Obs, procB1]
  refine ⟨?_, ?_⟩
  · rw [limitVal_of_coeff_one _ _ _ a0 (by rw [a1]; norm_num), ap1, zero_div]
  · rw [limitVal_eq_of_pos _ _ _ hbpos]
    unfold condExp
    rw [t1_paySum, t1_nu]
    simp [t1ActEv, t1Obs, procB1]

/-- `δ_b` is MSR at `t1`'s point: its one supported act `b` is realized and its tremble-pinned
value `1` is at least `a`'s `0`. Source: SL-21 Definition 18′ (instance). Kind: L -/
theorem t1_procB1_msrAt : MSRAt t1Obs t1ActEv procB1 t1 () := by
  intro x hx
  have hxb : x = .b := by cases x <;> simp [procB1] at hx ⊢
  subst hxb
  obtain ⟨hva, hvb⟩ := t1_procB1_limitVals
  have hbpos : 0 < nu procB1 t1 (t1ActEv () .b ∩ t1Obs ()) := by
    rw [t1_nu]; simp [t1ActEv, t1Obs, procB1]
  have hbne : nuPoly procB1 t1 (t1ActEv () .b ∩ t1Obs ()) ≠ 0 := fun hz => by
    have := coeff_zero_nuPoly procB1 t1 (t1ActEv () .b ∩ t1Obs ())
    rw [hz, Polynomial.coeff_zero] at this
    exact absurd this.symm hbpos.ne'
  refine ⟨hbne, fun b' _ => ?_⟩
  cases b'
  · rw [hva, hvb]; norm_num
  · exact le_refl _

/-- **`msr17At_of_msrAt_recorded`'s package inhabited with a strict maximum** (the N+ the N−
`coinQuery_msr17_instance` is not): on `t1`, which records at `d` for every procedure
(`t1_recordsFor`), `δ_b` is strictly calibrated at `t1BStrictState`, `ν(O_d) = 1 > 0`, and
`MSRAt` holds with the supported act the *strict* maximiser — `limitVal a = 0 < 1 = limitVal b`
(the `a`-event has order `1` with payoff mass `0`; the `b`-event is realized with value `1`);
the conclusion `MSR¹⁷` (`T_EDT` at the strict state, `A_d^+ = {b}`) follows through the theorem.
The mirror of `t1_msr17_not_msr` (`δ_a`, where MSR fails): on the same recorded tree the
inclusion MSR ⊆ MSR¹⁷ is exercised at `δ_b` and strict at `δ_a`.
Source: SL-21; C2-9′ ("MSR ⊆ MSR¹⁷"); audit r2 fidelity N1
Kind: N+
Fidelity: exact
Hyps: none -/
theorem t1_msr17_instance :
    StrictOCAt (fun _ => t1BStrictState) t1Obs procB1 t1 () ∧
    RecordsFor t1Obs t1ActEv procB1 t1 () ∧
    0 < nu procB1 t1 (t1Obs ()) ∧
    MSRAt t1Obs t1ActEv procB1 t1 () ∧
    MSR17At t1ActEv procB1 (fun _ => t1BStrictState) () ∧
    limitVal procB1 t1 (t1ActEv () .a ∩ t1Obs ()) < limitVal procB1 t1 (t1ActEv () .b ∩ t1Obs ()) := by
  have hpos : 0 < nu procB1 t1 (t1Obs ()) := by
    show 0 < nu procB1 t1 Finset.univ; exact nu_univ_pos _ _
  have hs : StrictOCAt (fun _ => t1BStrictState) t1Obs procB1 t1 () :=
    strictOCAt_calibratedState t1Obs procB1 t1 (fun _ => t1BStrictState) () hpos rfl
  have hrec := t1_recordsFor procB1
  have hmsr := t1_procB1_msrAt
  obtain ⟨hva, hvb⟩ := t1_procB1_limitVals
  refine ⟨hs, hrec, hpos, hmsr, msr17At_of_msrAt_recorded _ _ _ _ _ () hs hrec hpos hmsr, ?_⟩
  rw [hva, hvb]; norm_num

end msr17

end Cleanroom.Decision.DpCalibLimits

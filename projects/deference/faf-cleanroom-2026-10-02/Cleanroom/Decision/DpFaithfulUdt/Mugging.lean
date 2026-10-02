import Cleanroom.Decision.DpFaithfulUdt.Pdc
import Cleanroom.Decision.DpCalibration.Mugging

/-!
# Remark 4.2 made exact on `B₁`: the three candidate `ρ`'s and FA-3 (T6); cUDT on the mugging
(T8 instances); the T12 witness

T6 of [[dp-faithful-udt-mandate]], on the four-world carrier `MugW` of `dp-core-tree`'s `mug1`
(the realized atoms of Proposition 6's algebra), with `s°` prior-calibrated under the self-model
`procQ q'`, `q' ∈ (0,1)`, `0 < x < y`:

* (a) act-event `ρ := mugActEv`: `V_{s°}(pay) = −x`, `V_{s°}(refuse) = 0`, refuses for every
  `q', x, y` (`mug1_actEvent_refuses`);
* (b) material conditional `ρ_d(a) := H ∨ a` (`mugMat`): `V = q'(y−x)/(1+q')` vs `q'y/(2−q')`,
  pays iff `y(1−2q') > x(2−q')` — refuses at `q' = ½`, pays at `q' = 1/10, x = 1, y = 3`
  (`mug1_material`, `mug1_material_half_refuses`, `mug1_material_tenth_pays`);
* (c) would-pay `E_pay := {(T,pay,0), (H,⊥,1)}`, `E_refuse := {(T,refuse,0), (H,⊥,0)}`
  (`mugWp`): law-faithful relative to `procQ q'` (`mugWp_lawFaithful`), values `(y−x)/2` vs
  `0`, pays iff `y > x` (`mug1_wouldPay`);
* (d) **FA-3 on the realized atoms**: the events law-faithful for pay are exactly `E_pay`, for
  refuse exactly `E_refuse` (`mug1_faithful_pay_iff`, `mug1_faithful_refuse_iff`); on `B₂` the
  faithful pay-event is `{(T,pay,0), (H,⊥,0)}` (`mug2_faithful_pay`), so **no event is faithful
  for both muggings** (`no_event_faithful_both`) — the problem-independence demand of amendment 1;
  `E_pay` used on `B₂` values `y − q'(x+y)` vs `0` (`mug2_wouldPay_values`).
* (f) finding against v2 Remark 4.2's "no such event exists in that example's algebra as
  modelled": refuted by (c), surviving claim (e) — `dp-faithful-udt-findings`.

T8 instances (faithful.md FA-7′ (ii′), (iv)): act-event cUDT with a `cf` counterfactually
calibrated to the deviation statistics at the act events refuses (`mug1_actEvent_cudt_refuses`);
R1-calibrated cUDT under the *strict* prior of `δ_refuse` pays while UDT at that prior refuses
(`mug1_r1_cudt_pays`). T12's witness: on `B₁` (almost fair, `occ(d) = ⊤`) Theorem 1's and
Theorem 2's argmaxes agree and both are `{pay}` when `y > x` (`mug1_thm1_thm2_agree`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFaithfulUdt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt

/-! ### The payoff masses of the two muggings -/

section masses

variable (x y : ℚ)

/-- `𝔼[r · 1_X]` on `B₁`: pay's fee on `(T,pay,0)`, the transfer on `(H,⊥,1)`.
Source: none: infrastructure (mirrors `dp-calibration`'s `mug1_nu`)
Kind: L -/
theorem mug1_paySum (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset MugW) :
    paySum C (mug1 x y) X =
      (if MugW.tPay ∈ X then (1 / 2 : ℚ) * (C ()).w .a * (-x) else 0) +
      (if MugW.hOne ∈ X then (1 / 2 : ℚ) * (C ()).w .a * y else 0) := by
  rw [paySum_eq_sum_ite, mug1_sum]
  simp only [Fin.sum_univ_two, Act2.sum_univ, mug1, mugWorld1, mugPay, leafLaw_chance,
    leafLaw_decision, leafLaw_leaf, world_chance, world_decision, world_leaf, payoff_chance,
    payoff_decision, payoff_leaf, FinDistr.fair, FinDistr.coin]
  simp
  split_ifs <;> ring

/-- `𝔼[r · 1_X]` on `B₂`: the transfer on `(H,⊥,1)` is reached by *refusing*.
Source: none: infrastructure (mirrors `dp-calibration`'s `mug2_nu`)
Kind: L -/
theorem mug2_paySum (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset MugW) :
    paySum C (mug2 x y) X =
      (if MugW.tPay ∈ X then (1 / 2 : ℚ) * (C ()).w .a * (-x) else 0) +
      (if MugW.hOne ∈ X then (1 / 2 : ℚ) * (C ()).w .b * y else 0) := by
  rw [paySum_eq_sum_ite, mug2_sum]
  simp only [Fin.sum_univ_two, Act2.sum_univ, mug2, mugWorld2, mugPay, leafLaw_chance,
    leafLaw_decision, leafLaw_leaf, world_chance, world_decision, world_leaf, payoff_chance,
    payoff_decision, payoff_leaf, FinDistr.fair, FinDistr.coin]
  simp
  split_ifs <;> ring

/-- `preEv id X = X`. Source: none: infrastructure. Kind: L -/
@[simp] theorem preEv_id {Ω : Type} [Fintype Ω] [DecidableEq Ω] (X : Finset Ω) :
    preEv (id : Ω → Ω) X = X := by
  ext w; simp

end masses

/-! ### Definition F1 per action -/

section perAct

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] {Ω' : Type} [Fintype Ω'] [DecidableEq Ω']

/-- **Definition F1 for one action**: the event `E` of the enriched carrier is law-faithful for
`(B, C')` at `d` for the action `a` (the clause of `LawFaithfulAt` at `a`, with `E` in place of
`ρ_d(a)`), so that FA-3's "the events faithful for pay are exactly …" can be stated.
Source: `faithful.md` Definition F1, FA-3
Kind: D -/
def LawFaithfulFor (π : Ω' → Ω) (s₀ : State Ω' K) (E : Finset Ω') (C' : Proc ι acts K)
    (B : Tree Ω ι acts K) (d : ι) (a : acts d) : Prop :=
  0 < s₀.pr E ∧
    (∀ X : Finset Ω, s₀.pr (preEv π X ∩ E) = s₀.pr E * nu (C'.deviatePure d a) B X) ∧
    (∀ X : Finset Ω,
      s₀.V (preEv π X ∩ E) * s₀.pr (preEv π X ∩ E) = s₀.pr E * paySum (C'.deviatePure d a) B X)

/-- `LawFaithfulAt` is `LawFaithfulFor` at every action. Source: none: infrastructure. Kind: L -/
theorem lawFaithfulAt_iff (π : Ω' → Ω) (s₀ : State Ω' K) (ρ : (d : ι) → acts d → Finset Ω')
    (C' : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) :
    LawFaithfulAt s₀ ρ C' B π d ↔ ∀ a, LawFaithfulFor π s₀ (ρ d a) C' B d a := Iff.rfl

end perAct

/-! ### T6: the three candidates on `B₁` -/

section t6

variable (x y : ℚ) (q' : ℚ) (hq0 : 0 < q') (hq1 : q' < 1) (s₀ : State MugW ℚ)

/-- The self-model `C'(pay) = q'`. Source: `faithful.md` §"Q10, one point". Kind: D -/
abbrev selfQ : Proc Unit (fun _ => Act2) ℚ := procQ q' hq0.le hq1.le

/-- Under prior calibration to `procQ q'`, `V_{s°}(X) = paySum(X)/ν(X)` on `ν`-positive events.
Source: none: infrastructure
Kind: L -/
theorem priorCal_V (hcal : PriorCalibrated (selfQ q' hq0 hq1) (mug1 x y) s₀) (X : Finset MugW)
    (hX : 0 < nu (selfQ q' hq0 hq1) (mug1 x y) X) :
    s₀.V X = paySum (selfQ q' hq0 hq1) (mug1 x y) X / nu (selfQ q' hq0 hq1) (mug1 x y) X := by
  rw [eq_div_iff hX.ne']
  exact hcal.2 X hX

/-- The prior state's beliefs on `B₁`: `(q'/2, (1−q')/2, (1−q')/2, q'/2)` on
`(T,pay,0), (T,refuse,0), (H,⊥,0), (H,⊥,1)`.
Source: `faithful.md` §"Q10, one point" ("`P_{s°} = (q'/2, (1−q')/2, (1−q')/2, q'/2)`")
Kind: L -/
theorem mug1_prior_atoms (hcal : PriorCalibrated (selfQ q' hq0 hq1) (mug1 x y) s₀) :
    s₀.pr {MugW.tPay} = q' / 2 ∧ s₀.pr {MugW.tRefuse} = (1 - q') / 2 ∧
    s₀.pr {MugW.hZero} = (1 - q') / 2 ∧ s₀.pr {MugW.hOne} = q' / 2 := by
  have h := hcal.1
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [h, mug1_nu] <;> simp [selfQ, procQ] <;> ring

/-- **T6(a) — the act-event `ρ` refuses on `B₁`** for every `q' ∈ (0,1)`, `x > 0`, `y`:
`V_{s°}(pay) = −x < 0 = V_{s°}(refuse)` (conditioning on the act event confines all weight to
tails-worlds: Remark 4.2's disjointness).
Source: `faithful.md` FA-2 ("Act-event `ρ_d(a) := a`: … values `−x` vs `0`, refuses for every
`q', x, y`"); v2 Remark 4.2
Kind: P
Fidelity: exact (realized atoms)
Hyps: (a) `PriorCalibrated (procQ q') B₁ s°`; (a) `0 < x` -/
theorem mug1_actEvent_refuses (hx : 0 < x) (hcal : PriorCalibrated (selfQ q' hq0 hq1) (mug1 x y) s₀) :
    s₀.V (mugActEv () .a) = -x ∧ s₀.V (mugActEv () .b) = 0 ∧
      udtProc s₀ mugActEv () = FinDistr.pure Act2.b := by
  obtain ⟨h1, h2, -, -⟩ := mug1_prior_atoms x y q' hq0 hq1 s₀ hcal
  have hpa : 0 < s₀.pr (mugActEv () .a) := by
    show 0 < s₀.pr {MugW.tPay}; rw [h1]; linarith
  have hpb : 0 < s₀.pr (mugActEv () .b) := by
    show 0 < s₀.pr {MugW.tRefuse}; rw [h2]; linarith
  have hVa : s₀.V (mugActEv () .a) = -x := by
    show s₀.V {MugW.tPay} = -x
    rw [priorCal_V x y q' hq0 hq1 s₀ hcal _ (by rw [← hcal.1]; exact hpa), mug1_paySum, mug1_nu]
    simp [selfQ, procQ]
    field_simp
  have hVb : s₀.V (mugActEv () .b) = 0 := by
    show s₀.V {MugW.tRefuse} = 0
    rw [priorCal_V x y q' hq0 hq1 s₀ hcal _ (by rw [← hcal.1]; exact hpb), mug1_paySum]
    simp
  refine ⟨hVa, hVb, ?_⟩
  rw [udtProc_eq_uniformArgmax s₀ mugActEv () fun a => by cases a <;> assumption]
  apply uniformArgmax_eq_pure
  apply argmaxFull_act2_eq_b
  simp only [hVa, hVb]; linarith

/-- The material-conditional interpretation `ρ_d(a) := ¬O_d ∨ a` on the realized atoms.
Source: v2 Remark 4.2 ("`ρ_d(a) := ¬O_d ∨ a`"); `faithful.md` FA-2 ("Material conditional
`H ∨ a`")
Kind: D -/
def mugMat : Unit → Act2 → Finset MugW
  | _, .a => {.tPay, .hOne, .hZero}
  | _, .b => {.tRefuse, .hOne, .hZero}

/-- **T6(b) — the material conditional on `B₁`**: `V_{s°}(H ∨ pay) = q'(y−x)/(1+q')`,
`V_{s°}(H ∨ refuse) = q'y/(2−q')`; `UDT` pays iff `y(1−2q') > x(2−q')` (antecedent reweighting:
the verdict follows `q'`, not the stakes).
Source: `faithful.md` FA-2 ("`V(H ∨ pay) = q'(y−x)/(1+q')`, `V(H ∨ refuse) = q'y/(2−q')` … pays
iff `y(1−2q') > x(2−q')`"); v2 Remark 4.2
Kind: P
Fidelity: exact
Hyps: (a) `PriorCalibrated (procQ q') B₁ s°` -/
theorem mug1_material (hcal : PriorCalibrated (selfQ q' hq0 hq1) (mug1 x y) s₀) :
    s₀.V (mugMat () .a) = q' * (y - x) / (1 + q') ∧ s₀.V (mugMat () .b) = q' * y / (2 - q') ∧
    (x * (2 - q') < y * (1 - 2 * q') → udtProc s₀ mugMat () = FinDistr.pure Act2.a) ∧
    (y * (1 - 2 * q') < x * (2 - q') → udtProc s₀ mugMat () = FinDistr.pure Act2.b) := by
  have hna : nu (selfQ q' hq0 hq1) (mug1 x y) (mugMat () .a) = (1 + q') / 2 := by
    rw [mug1_nu]; simp [mugMat, selfQ, procQ]; ring
  have hnb : nu (selfQ q' hq0 hq1) (mug1 x y) (mugMat () .b) = (2 - q') / 2 := by
    rw [mug1_nu]; simp [mugMat, selfQ, procQ]; ring
  have hpa : 0 < s₀.pr (mugMat () .a) := by rw [hcal.1, hna]; linarith
  have hpb : 0 < s₀.pr (mugMat () .b) := by rw [hcal.1, hnb]; linarith
  have hVa : s₀.V (mugMat () .a) = q' * (y - x) / (1 + q') := by
    rw [priorCal_V x y q' hq0 hq1 s₀ hcal _ (by rw [← hcal.1]; exact hpa), hna, mug1_paySum]
    simp [mugMat, selfQ, procQ]
    have : (1 + q') ≠ 0 := by linarith
    first | (field_simp; ring) | field_simp
  have hVb : s₀.V (mugMat () .b) = q' * y / (2 - q') := by
    rw [priorCal_V x y q' hq0 hq1 s₀ hcal _ (by rw [← hcal.1]; exact hpb), hnb, mug1_paySum]
    simp [mugMat, selfQ, procQ]
    have : (2 - q') ≠ 0 := by linarith
    first | (field_simp; ring) | field_simp
  have hdiff : s₀.V (mugMat () .a) - s₀.V (mugMat () .b) =
      q' * (y * (1 - 2 * q') - x * (2 - q')) / ((1 + q') * (2 - q')) := by
    rw [hVa, hVb]
    have h1 : (1 + q') ≠ 0 := by linarith
    have h2 : (2 - q') ≠ 0 := by linarith
    field_simp
    ring
  have hden : 0 < (1 + q') * (2 - q') := mul_pos (by linarith) (by linarith)
  refine ⟨hVa, hVb, fun h => ?_, fun h => ?_⟩
  · rw [udtProc_eq_uniformArgmax s₀ mugMat () fun a => by cases a <;> assumption]
    apply uniformArgmax_eq_pure
    apply argmaxFull_act2_eq_a
    have : 0 < s₀.V (mugMat () .a) - s₀.V (mugMat () .b) := by
      rw [hdiff]; exact div_pos (mul_pos hq0 (by linarith)) hden
    linarith
  · rw [udtProc_eq_uniformArgmax s₀ mugMat () fun a => by cases a <;> assumption]
    apply uniformArgmax_eq_pure
    apply argmaxFull_act2_eq_b
    have : s₀.V (mugMat () .a) - s₀.V (mugMat () .b) < 0 := by
      rw [hdiff]; exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hq0 (by linarith)) hden
    linarith

/-- At `q' = ½` the material conditional refuses (`(y−x)/3` vs `y/3`), for every `x > 0`.
Source: v2 Remark 4.2 ("at self-belief `q₀ = ½` the two sides score `(y−x)/3` against `y/3` and
it refuses"); `faithful.md` FA-2
Kind: N+ -/
theorem mug1_material_half_refuses (hx : 0 < x)
    (hcal : PriorCalibrated (selfQ (1 / 2) (by norm_num) (by norm_num)) (mug1 x y) s₀) :
    s₀.V (mugMat () .a) = (y - x) / 3 ∧ s₀.V (mugMat () .b) = y / 3 ∧
      udtProc s₀ mugMat () = FinDistr.pure Act2.b := by
  obtain ⟨hVa, hVb, -, hb⟩ := mug1_material x y (1 / 2) (by norm_num) (by norm_num) s₀ hcal
  refine ⟨by rw [hVa]; ring, by rw [hVb]; ring, hb (by linarith)⟩

/-- At `q' = 1/10`, `x = 1`, `y = 3` the material conditional pays (`2/11 > 3/19`): its verdict
drifts with the antecedent probability.
Source: `faithful.md` FA-2 ("at `q' = 1/10, x = 1, y = 3`, `2/11 > 3/19`, pays")
Kind: N+ -/
theorem mug1_material_tenth_pays
    (hcal : PriorCalibrated (selfQ (1 / 10) (by norm_num) (by norm_num)) (mug1 1 3) s₀) :
    s₀.V (mugMat () .a) = 2 / 11 ∧ s₀.V (mugMat () .b) = 3 / 19 ∧
      udtProc s₀ mugMat () = FinDistr.pure Act2.a := by
  obtain ⟨hVa, hVb, ha, -⟩ := mug1_material 1 3 (1 / 10) (by norm_num) (by norm_num) s₀ hcal
  refine ⟨by rw [hVa]; norm_num, by rw [hVb]; norm_num, ha (by norm_num)⟩

/-- The would-pay / would-refuse events on the realized atoms: `E_pay = (T ∧ pay) ∨ (H ∧
transfer = 1)`, `E_refuse = (T ∧ refuse) ∨ (H ∧ transfer = 0)`.
Source: v2 Remark 4.2 ("a would-pay coordinate"); `faithful.md` FA-2 (`E_pay`), FA-3
Kind: D -/
def mugWp : Unit → Act2 → Finset MugW
  | _, .a => {.tPay, .hOne}
  | _, .b => {.tRefuse, .hZero}

/-- `mugWp` is injective in the action. Source: none: infrastructure. Kind: L -/
theorem mugWp_injective : Function.Injective (mugWp ()) := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (exfalso; have := Finset.ext_iff.mp h MugW.tPay; simp [mugWp] at this)

/-- **T6(c) — the would-pay coordinate is law-faithful on `B₁`** relative to the self-model
`procQ q'` (Definition F1 in full): conditioning the prior on `E_pay` gives the pure-pay run's
world law and payoff masses, and likewise for `E_refuse`.
Source: `faithful.md` FA-2 ("Would-pay event `E_pay` … `ν_{C'}(· ∣ E_pay) = ½(T,pay,0) + ½(H,⊥,1)
= ν_{δ_pay}` … law- and value-faithful"); FA-1 (self-model independence)
Kind: P
Fidelity: exact (realized atoms)
Hyps: (a) `PriorCalibrated (procQ q') B₁ s°` -/
theorem mugWp_lawFaithful (hcal : PriorCalibrated (selfQ q' hq0 hq1) (mug1 x y) s₀) :
    LawFaithfulAt s₀ mugWp (selfQ q' hq0 hq1) (mug1 x y) id () := by
  intro a
  have hdev : (selfQ q' hq0 hq1).deviatePure () a = Proc.ofFun fun _ => a :=
    deviatePure_unit_eq_ofFun (selfQ q' hq0 hq1) a
  rw [hdev]
  have hpos : 0 < s₀.pr (mugWp () a) := by
    rw [hcal.1, mug1_nu]; cases a <;> simp [mugWp, selfQ, procQ] <;> linarith
  refine ⟨hpos, fun X => ?_, fun X => ?_⟩
  · rw [hcal.1, hcal.1, preEv_id, mug1_nu, mug1_nu, mug1_nu]
    cases a <;> simp [mugWp, selfQ, procQ] <;> split_ifs <;> ring
  · rw [preEv_id]
    by_cases hz : 0 < nu (selfQ q' hq0 hq1) (mug1 x y) (X ∩ mugWp () a)
    · rw [hcal.1, hcal.1, hcal.2 _ hz, mug1_paySum, mug1_paySum, mug1_nu]
      cases a <;> simp [mugWp, selfQ, procQ] <;> split_ifs <;> ring
    · push Not at hz
      have h0 : nu (selfQ q' hq0 hq1) (mug1 x y) (X ∩ mugWp () a) = 0 :=
        le_antisymm hz (nu_nonneg _ _ _)
      rw [hcal.1, hcal.1, h0, mul_zero, mug1_paySum]
      rw [mug1_nu] at h0
      cases a
      · simp [mugWp, selfQ, procQ] at h0 ⊢
        by_cases h1 : MugW.tPay ∈ X <;> by_cases h2 : MugW.hOne ∈ X <;> simp [h1, h2] at h0 ⊢ <;>
          nlinarith
      · simp [mugWp, selfQ, procQ]

/-- **T6(c), values**: `V_{s°}(E_pay) = (y−x)/2`, `V_{s°}(E_refuse) = 0`; `UDT` pays iff `y > x`.
Source: `faithful.md` FA-2 ("values `(y−x)/2` vs `0` … pays iff `y > x`"); v2 Remark 4.2
("`V_{s°}(would-pay) = ½(y−x) > 0 = V_{s°}(would-refuse)`")
Kind: P
Fidelity: exact
Hyps: (a) `PriorCalibrated (procQ q') B₁ s°` -/
theorem mug1_wouldPay (hcal : PriorCalibrated (selfQ q' hq0 hq1) (mug1 x y) s₀) :
    s₀.V (mugWp () .a) = (y - x) / 2 ∧ s₀.V (mugWp () .b) = 0 ∧
    (x < y → udtProc s₀ mugWp () = FinDistr.pure Act2.a) ∧
    (y < x → udtProc s₀ mugWp () = FinDistr.pure Act2.b) := by
  have hvf := (mugWp_lawFaithful x y q' hq0 hq1 s₀ hcal).valueFaithfulAt
  have hVa : s₀.V (mugWp () .a) = (y - x) / 2 := by
    rw [(hvf .a).2, deviatePure_unit_eq_ofFun, mug1_value_pay]
  have hVb : s₀.V (mugWp () .b) = 0 := by
    rw [(hvf .b).2, deviatePure_unit_eq_ofFun, mug1_value_refuse]
  refine ⟨hVa, hVb, fun h => ?_, fun h => ?_⟩
  · rw [udtProc_eq_uniformArgmax s₀ mugWp () fun a => (hvf a).1]
    apply uniformArgmax_eq_pure
    apply argmaxFull_act2_eq_a
    simp only [hVa, hVb]; linarith
  · rw [udtProc_eq_uniformArgmax s₀ mugWp () fun a => (hvf a).1]
    apply uniformArgmax_eq_pure
    apply argmaxFull_act2_eq_b
    simp only [hVa, hVb]; linarith

/-- The atom-level consequences of the world clause of law-faithfulness for pay on `B₁`: the two
pure-pay atoms are in `E`, the two others are not.
Source: `faithful.md` FA-3 (the four-case membership argument)
Kind: L -/
theorem mug1_faithful_pay_atoms (hcal : PriorCalibrated (selfQ q' hq0 hq1) (mug1 x y) s₀)
    (E : Finset MugW) (h : LawFaithfulFor id s₀ E (selfQ q' hq0 hq1) (mug1 x y) () .a) :
    MugW.tPay ∈ E ∧ MugW.tRefuse ∉ E ∧ MugW.hOne ∈ E ∧ MugW.hZero ∉ E := by
  obtain ⟨hpos, hw, -⟩ := h
  rw [deviatePure_unit_eq_ofFun] at hw
  have key : ∀ ω : MugW, s₀.pr ({ω} ∩ E) =
      s₀.pr E * nu (Proc.ofFun fun _ => Act2.a) (mug1 x y) {ω} := fun ω => by
    have := hw {ω}; rwa [preEv_id] at this
  have h1 := key .tPay
  have h2 := key .tRefuse
  have h3 := key .hOne
  have h4 := key .hZero
  rw [hcal.1, mug1_nu, mug1_nu] at h1 h2 h3 h4
  simp [selfQ, procQ] at h1 h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hc; simp [hc] at h1; linarith
  · intro hc; simp [hc] at h2; linarith
  · by_contra hc; simp [hc] at h3; linarith
  · intro hc; simp [hc] at h4; linarith

/-- **T6(d) — FA-3 on the realized atoms, pay**: the events of the four-world carrier law-faithful
for pay relative to `procQ q'` are exactly `E_pay = {(T,pay,0), (H,⊥,1)}`.
Source: `faithful.md` FA-3 ("the events faithful for `B₁` are exactly `E_pay` (for pay) …, up to
unrealized atoms")
Kind: P
Fidelity: variant: realized atoms only (the 8 unrealized atoms of the 12-atom product algebra
are not modelled; FA-3's "up to unrealized atoms")
Hyps: (a) `PriorCalibrated (procQ q') B₁ s°`; (a) `0 < q' < 1` -/
theorem mug1_faithful_pay_iff (hcal : PriorCalibrated (selfQ q' hq0 hq1) (mug1 x y) s₀)
    (E : Finset MugW) :
    LawFaithfulFor id s₀ E (selfQ q' hq0 hq1) (mug1 x y) () .a ↔ E = {MugW.tPay, MugW.hOne} := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3, h4⟩ := mug1_faithful_pay_atoms x y q' hq0 hq1 s₀ hcal E h
    ext ω; cases ω <;> simp [h1, h2, h3, h4]
  · rintro rfl
    exact (mugWp_lawFaithful x y q' hq0 hq1 s₀ hcal) .a

/-- The atom-level consequences for refuse. Source: `faithful.md` FA-3. Kind: L -/
theorem mug1_faithful_refuse_atoms (hcal : PriorCalibrated (selfQ q' hq0 hq1) (mug1 x y) s₀)
    (E : Finset MugW) (h : LawFaithfulFor id s₀ E (selfQ q' hq0 hq1) (mug1 x y) () .b) :
    MugW.tPay ∉ E ∧ MugW.tRefuse ∈ E ∧ MugW.hOne ∉ E ∧ MugW.hZero ∈ E := by
  obtain ⟨hpos, hw, -⟩ := h
  rw [deviatePure_unit_eq_ofFun] at hw
  have key : ∀ ω : MugW, s₀.pr ({ω} ∩ E) =
      s₀.pr E * nu (Proc.ofFun fun _ => Act2.b) (mug1 x y) {ω} := fun ω => by
    have := hw {ω}; rwa [preEv_id] at this
  have h1 := key .tPay
  have h2 := key .tRefuse
  have h3 := key .hOne
  have h4 := key .hZero
  rw [hcal.1, mug1_nu, mug1_nu] at h1 h2 h3 h4
  simp [selfQ, procQ] at h1 h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hc; simp [hc] at h1; linarith
  · by_contra hc; simp [hc] at h2; linarith
  · intro hc; simp [hc] at h3; linarith
  · by_contra hc; simp [hc] at h4; linarith

/-- **T6(d) — FA-3, refuse**: the events law-faithful for refuse are exactly
`E_refuse = {(T,refuse,0), (H,⊥,0)}`.
Source: `faithful.md` FA-3
Kind: P
Fidelity: variant: realized atoms only
Hyps: (a) `PriorCalibrated (procQ q') B₁ s°`; (a) `0 < q' < 1` -/
theorem mug1_faithful_refuse_iff (hcal : PriorCalibrated (selfQ q' hq0 hq1) (mug1 x y) s₀)
    (E : Finset MugW) :
    LawFaithfulFor id s₀ E (selfQ q' hq0 hq1) (mug1 x y) () .b ↔
      E = {MugW.tRefuse, MugW.hZero} := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3, h4⟩ := mug1_faithful_refuse_atoms x y q' hq0 hq1 s₀ hcal E h
    ext ω; cases ω <;> simp [h1, h2, h3, h4]
  · rintro rfl
    exact (mugWp_lawFaithful x y q' hq0 hq1 s₀ hcal) .b

end t6

/-! ### T6(e): no event is faithful for both muggings -/

section t6e

variable (x y : ℚ) (q' : ℚ) (hq0 : 0 < q') (hq1 : q' < 1)

/-- On `B₂` the law-faithful pay-event is `{(T,pay,0), (H,⊥,0)}` (the transfer coordinate records
the simulated draw the other way round): the world clause forces exactly these atoms.
Source: `faithful.md` FA-3 ("for `B₂` the transfer-swapped events")
Kind: P
Fidelity: variant: realized atoms only
Hyps: (a) `PriorCalibrated (procQ q') B₂ s°`; (a) `0 < q' < 1` -/
theorem mug2_faithful_pay (s₂ : State MugW ℚ)
    (hcal : PriorCalibrated (selfQ q' hq0 hq1) (mug2 x y) s₂) (E : Finset MugW)
    (h : LawFaithfulFor id s₂ E (selfQ q' hq0 hq1) (mug2 x y) () .a) :
    E = {MugW.tPay, MugW.hZero} := by
  obtain ⟨hpos, hw, -⟩ := h
  rw [deviatePure_unit_eq_ofFun] at hw
  have key : ∀ ω : MugW, s₂.pr ({ω} ∩ E) =
      s₂.pr E * nu (Proc.ofFun fun _ => Act2.a) (mug2 x y) {ω} := fun ω => by
    have := hw {ω}; rwa [preEv_id] at this
  have h1 := key .tPay
  have h2 := key .tRefuse
  have h3 := key .hOne
  have h4 := key .hZero
  rw [hcal.1, mug2_nu, mug2_nu] at h1 h2 h3 h4
  simp [selfQ, procQ] at h1 h2 h3 h4
  have e1 : MugW.tPay ∈ E := by by_contra hc; simp [hc] at h1; linarith
  have e2 : MugW.tRefuse ∉ E := by intro hc; simp [hc] at h2; linarith
  have e3 : MugW.hOne ∉ E := by intro hc; simp [hc] at h3; linarith
  have e4 : MugW.hZero ∈ E := by by_contra hc; simp [hc] at h4; linarith
  ext ω; cases ω <;> simp [e1, e2, e3, e4]

/-- **T6(e) — no event of the algebra is faithful for both muggings**: the pay-faithful event is
`{(T,pay,0), (H,⊥,1)}` on `B₁` and `{(T,pay,0), (H,⊥,0)}` on `B₂`, and they differ. Since `ρ_d` is
a function of the point and both problems query `d`, no `ρ` serves both — amendment 1's
problem-independence demand, Proposition 6's non-uniformity in `ρ`-clothing.
Source: `faithful.md` FA-3 ("**no event is uniformly faithful on `{B₁, B₂}`**"); v2 amendment 1
Kind: P (refutation of existence)
Fidelity: variant: realized atoms only
Hyps: (a) `PriorCalibrated (procQ q') B₁ s₁`, `PriorCalibrated (procQ q') B₂ s₂`; (a) `0 < q' < 1` -/
theorem no_event_faithful_both (s₁ s₂ : State MugW ℚ)
    (hcal1 : PriorCalibrated (selfQ q' hq0 hq1) (mug1 x y) s₁)
    (hcal2 : PriorCalibrated (selfQ q' hq0 hq1) (mug2 x y) s₂) :
    ¬ ∃ E : Finset MugW, LawFaithfulFor id s₁ E (selfQ q' hq0 hq1) (mug1 x y) () .a ∧
      LawFaithfulFor id s₂ E (selfQ q' hq0 hq1) (mug2 x y) () .a := by
  rintro ⟨E, h1, h2⟩
  have e1 := (mug1_faithful_pay_iff x y q' hq0 hq1 s₁ hcal1 E).mp h1
  have e2 := mug2_faithful_pay x y q' hq0 hq1 s₂ hcal2 E h2
  rw [e1] at e2
  have : MugW.hOne ∈ ({MugW.tPay, MugW.hZero} : Finset MugW) := by rw [← e2]; simp
  simp at this

/-- **`B₁`'s `E_pay` used on `B₂`**: `V_{s₂}(E_pay) = y − q'(x+y)`, `V_{s₂}(E_refuse) = 0` — pays iff
`(1−2q')y > q'x`, wrong for small `q'`.
Source: `faithful.md` FA-3 ("`B₁`'s `E_pay` used on `B₂`: `V = y − q'(x+y)` vs `0`")
Kind: P
Fidelity: exact
Hyps: (a) `PriorCalibrated (procQ q') B₂ s₂` -/
theorem mug2_wouldPay_values (s₂ : State MugW ℚ)
    (hcal : PriorCalibrated (selfQ q' hq0 hq1) (mug2 x y) s₂) :
    s₂.V (mugWp () .a) = y - q' * (x + y) ∧ s₂.V (mugWp () .b) = 0 := by
  have hna : nu (selfQ q' hq0 hq1) (mug2 x y) (mugWp () .a) = 1 / 2 := by
    rw [mug2_nu]; simp [mugWp, selfQ, procQ]; ring
  have hnb : nu (selfQ q' hq0 hq1) (mug2 x y) (mugWp () .b) = 1 / 2 := by
    rw [mug2_nu]; simp [mugWp, selfQ, procQ]; ring
  constructor
  · show s₂.V {MugW.tPay, MugW.hOne} = y - q' * (x + y)
    have := hcal.2 (mugWp () .a) (by rw [hna]; norm_num)
    rw [hna, mug2_paySum] at this
    simp [mugWp, selfQ, procQ] at this
    linarith
  · show s₂.V {MugW.tRefuse, MugW.hZero} = 0
    have := hcal.2 (mugWp () .b) (by rw [hnb]; norm_num)
    rw [hnb, mug2_paySum] at this
    simp [mugWp] at this
    linarith

end t6e

/-! ### T8 on the mugging: act-event cUDT under counterfactual calibration; R1-calibrated cUDT -/

section t8

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-- **Counterfactual calibration of `cf` at the event `X` to the deviation statistics**: `cf X` is
`(ν_{C[d↦a]}(· ∣ X), 𝔼_{C[d↦a]}[r ∣ · ∧ X])` (Definition F2's R1 at the `X`-conditioned weighting),
cross-multiplied. Success (`P^X(X) = 1`) follows (`Y := X`). This is Remark 3.11's "equating
supposed statistics with the deviation statistics", which v2 declines to impose by default — here
a hypothesis, never a definition of `cf`.
Source: [[decision-problems-v2]] §4 Definition 20 ("equating supposed statistics with the deviation
statistics `ν_{B,C[d↦a]}` … is *counterfactual calibration*"), Remark 3.11
Kind: D -/
def CfDeviationCalibratedAt (cf : Cf Ω K) (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)
    (a : acts d) (X : Finset Ω) : Prop :=
  (∀ Y, (cf X).pr Y * nu (C.deviatePure d a) B X = nu (C.deviatePure d a) B (Y ∩ X)) ∧
  (∀ Y, 0 < nu (C.deviatePure d a) B (Y ∩ X) →
    (cf X).V Y * nu (C.deviatePure d a) B (Y ∩ X) = paySum (C.deviatePure d a) B (Y ∩ X))

end t8

section t8mug

/-- `MugW` is inhabited (needed by the junk branch of `Cf.ofEvents`). Source: none: infrastructure.
Kind: D -/
instance : Nonempty MugW := ⟨.tPay⟩

variable (x y : ℚ)

/-- **T8(ii′) — act-event cUDT refuses on `B₁`** for every `cf` counterfactually calibrated at the
act events to the deviation statistics (hence supported on the realized atoms): success confines
the supposition of `pay` to `(T,pay,0)`, so `V^{pay}(pay) = −x < 0 = V^{refuse}(refuse)`. The
12-atom escape (a supposition sitting on the unrealized atom `(H,pay,1)`) is outside this carrier
(`dp-faithful-udt-findings`).
Source: `faithful.md` FA-7′ (ii′) ("For suppositions supported on realized atoms … success
confines a supposition of the act-event pay to `(T,pay,0)`, so `V^pay(pay) = −x` and act-event
cUDT refuses"); v2 Remark 4.2 (amended by amendment 1)
Kind: P
Fidelity: variant: counterfactual calibration to the deviation statistics at the act events
(which fixes `V`) in place of the source's "success + support" (which does not fix `V` in the
`State` model — `payCf_cudt_pays` below is a success-obeying supposition supported on the realized
atom `(T,pay,0)` under which act-event cUDT pays); realized atoms
Hyps: (a) `CfDeviationCalibratedAt cf C B₁ d a (act a)` for both acts; (a) `0 < x` -/
theorem mug1_actEvent_cudt_refuses (hx : 0 < x) (cf : Cf MugW ℚ) (C : Proc Unit (fun _ => Act2) ℚ)
    (hcf : ∀ a, CfDeviationCalibratedAt cf C (mug1 x y) () a (mugActEv () a)) :
    (cf (mugActEv () .a)).pr (mugActEv () .a) = 1 ∧
    (cf (mugActEv () .a)).V (mugActEv () .a) = -x ∧
    (cf (mugActEv () .b)).V (mugActEv () .b) = 0 ∧
    cudtProc cf mugActEv () = FinDistr.pure Act2.b := by
  have hna : nu (C.deviatePure () .a) (mug1 x y) (mugActEv () .a) = 1 / 2 := by
    rw [deviatePure_unit_eq_ofFun, mug1_nu]; simp [mugActEv]
  have hnb : nu (C.deviatePure () .b) (mug1 x y) (mugActEv () .b) = 1 / 2 := by
    rw [deviatePure_unit_eq_ofFun, mug1_nu]; simp [mugActEv]
  have hpa : (cf (mugActEv () .a)).pr (mugActEv () .a) = 1 := by
    have := (hcf .a).1 (mugActEv () .a)
    rw [Finset.inter_self, hna] at this
    linarith
  have hVa : (cf (mugActEv () .a)).V (mugActEv () .a) = -x := by
    show (cf {MugW.tPay}).V {MugW.tPay} = -x
    have := (hcf .a).2 (mugActEv () .a) (by rw [Finset.inter_self, hna]; norm_num)
    rw [Finset.inter_self, hna, deviatePure_unit_eq_ofFun, mug1_paySum] at this
    simp [mugActEv] at this
    linarith
  have hVb : (cf (mugActEv () .b)).V (mugActEv () .b) = 0 := by
    show (cf {MugW.tRefuse}).V {MugW.tRefuse} = 0
    have := (hcf .b).2 (mugActEv () .b) (by rw [Finset.inter_self, hnb]; norm_num)
    rw [Finset.inter_self, hnb, deviatePure_unit_eq_ofFun, mug1_paySum] at this
    simp [mugActEv] at this
    linarith
  refine ⟨hpa, hVa, hVb, ?_⟩
  unfold cudtProc
  apply uniformArgmax_eq_pure
  apply argmaxFull_act2_eq_b
  simp only [hVa, hVb]; linarith

/-- **T8(iv) on `B₁` — R1-calibrated cUDT is the closed-domain faithful updateless procedure**:
under the *strict* prior calibrated to the deterministic self-model `δ_refuse` (no mask),
`UDT_{s°,pol}` refuses (FA-6′'s collapse) while `cUDT` with the R1 counterfactual structure on the
disposition events pays (`(y−x)/2` vs `0`).
Source: `faithful.md` FA-7′ (iv) ("Strict prior for `C = δ_refuse` + `cf_{s°}(E_a) :=` law of
`μ_{δ_a}` … cUDT pays (`(y−x)/2` vs `0`) while UDT at the same prior refuses (FA-6′)")
Kind: N+
Fidelity: exact
Hyps: (a) `PriorCalibrated (lift (δ_refuse)) (Rel B₁) s°`; (a) `x < y` -/
theorem mug1_r1_cudt_pays (hxy : x < y) (s₀ : State (RW MugW (fun _ => Act2) {()}) ℚ)
    (hcal : PriorCalibrated (lift {()} (Proc.ofFun fun _ => Act2.b)) (relocRoot {()} (mug1 x y)) s₀) :
    udtProc s₀ (polEv {()}) () = FinDistr.pure Act2.b ∧
    cudtProc (r1Cf {()} (Proc.ofFun fun _ => Act2.b) (mug1 x y) ()) (polEv {()}) () =
      FinDistr.pure Act2.a := by
  have hmem : () ∈ ({()} : Finset Unit) := Finset.mem_singleton_self _
  refine ⟨udtProc_strict_collapse {()} (mug1 x y) s₀ _ hcal hmem, ?_⟩
  rw [cudtProc_r1 {()} _ (mug1 x y) hmem]
  apply uniformArgmax_eq_pure
  apply argmaxFull_act2_eq_a
  simp only [deviatePure_unit_eq_ofFun, value_lift_ofFun {()} (mug1 x y) (queried_unit_subset _),
    mug1_value_pay, mug1_value_refuse]
  linarith

/-- **T12's witness on `B₁`**: almost fair with `occ(d) = ⊤`, so Theorem 1's functional and Theorem
2's evaluator share their argmax for every procedure; both evaluate the pure acts at `(y−x)/2`
(pay) and `0` (refuse), so the common argmax is `{pay}` when `y > x`.
Source: `firstperson.md` FP-17 ("at `k = 1` all coincide"), FP-19′(i); mandate T12
Kind: N+
Fidelity: exact
Hyps: none -/
theorem mug1_thm1_thm2_agree (C : Proc Unit (fun _ => Act2) ℚ) :
    (∀ a b, siaSum C (mug1 x y) () b ≤ siaSum C (mug1 x y) () a ↔
      ssaValue C (mug1 x y) () (FinDistr.pure b) ≤ ssaValue C (mug1 x y) () (FinDistr.pure a)) ∧
    ssaValue C (mug1 x y) () (FinDistr.pure .a) = (y - x) / 2 ∧
    ssaValue C (mug1 x y) () (FinDistr.pure .b) = 0 := by
  have hocc : mass C (mug1 x y) (occ () (mug1 x y)) = 1 := by rw [mug1_occ, mass_univ]
  have hval : ∀ a, ssaValue C (mug1 x y) () (FinDistr.pure a) = value (Proc.ofFun fun _ => a) (mug1 x y) := by
    intro a
    rw [ssaValue_eq_div, hocc, div_one]
    unfold ssaNum value
    rw [mug1_occ, ← Proc.deviatePure, deviatePure_unit_eq_ofFun]
  refine ⟨fun a b => siaSum_le_iff_ssa C (mug1 x y) () (mug1_almostFair x y ()) (by rw [hocc]; exact one_pos) a b, ?_, ?_⟩
  · rw [hval, mug1_value_pay]
  · rw [hval, mug1_value_refuse]

/-! ### F15: "success + support on realized atoms" does not pin the supposed value -/

/-- A counterfactual structure on `MugW` that obeys v2 Definition 2's success axiom (the uniform
law on the supposed event) and is supported, at the pay event, on the realized atom `(T,pay,0)`
alone — with desirability `1` there: success and support say nothing about `V`.
Source: audit r1 (adversarial) probe `SuccessDoesNotPinValue.lean`; v2 Definition 2 (`V` is a
free component of a state)
Kind: D -/
noncomputable def payCf : Cf MugW ℚ := fun X =>
  if h : X.Nonempty then State.ofConst (uniformOn X h) (if X = {MugW.tPay} then 1 else 0)
  else State.trivial

/-- The uniform law on `S` puts probability `1` on `S`. Source: none: infrastructure. Kind: L -/
theorem probOf_uniformOn_self {α : Type} [Fintype α] [DecidableEq α] (S : Finset α)
    (h : S.Nonempty) : probOf (uniformOn (K := ℚ) S h) S = 1 := by
  unfold probOf
  have hw : ∀ ω ∈ S, (uniformOn (K := ℚ) S h).w ω = (S.card : ℚ)⁻¹ := fun ω hω => by
    rw [uniformOn_w, if_pos hω]
  rw [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul]
  have : (S.card : ℚ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr h).ne'
  exact mul_inv_cancel₀ this

/-- `payCf` obeys v2 Definition 2's success axiom. Source: v2 Definition 2 clause 3. Kind: L -/
theorem payCf_success : Success payCf := by
  intro X hX
  unfold payCf
  rw [dif_pos hX]
  exact probOf_uniformOn_self X hX

/-- At the pay event `payCf` is supported on the realized atom `(T,pay,0)` alone.
Source: `faithful.md` FA-7′ (ii′) ("suppositions supported on realized atoms"). Kind: L -/
theorem payCf_pay_supported : (payCf (mugActEv () .a)).pr {MugW.tPay} = 1 :=
  payCf_success _ (Finset.singleton_nonempty _)

/-- **F15 — a success-obeying supposition supported on the realized atoms under which act-event
cUDT *pays*.** FA-7′(ii′) and v2 Remark 4.2 ("equally any success-obeying supposition") infer
`V^{pay}(pay) = −x` from success and support alone; in the `State` model `V` is not determined by
`P`, so the inference needs the payoff clause of counterfactual calibration
(`CfDeviationCalibratedAt`, as `mug1_actEvent_cudt_refuses` assumes) or rigid atom values. The
source's sentence is refuted as phrased; its intended claim is `mug1_actEvent_cudt_refuses`.
Source: `faithful.md` FA-7′ (ii′) ("For suppositions supported on realized atoms … success
confines a supposition of the act-event pay to `(T,pay,0)`, so `V^pay(pay) = −x` and act-event
cUDT refuses"); v2 Remark 4.2; audit r1 (adversarial) N2
Kind: N+ (refutation witness)
Fidelity: exact (the source's hypothesis as phrased, on the realized-atom carrier)
Hyps: none -/
theorem payCf_cudt_pays : cudtProc payCf mugActEv () = FinDistr.pure Act2.a := by
  have ha : (payCf (mugActEv () .a)).V (mugActEv () .a) = 1 := by
    show (payCf {MugW.tPay}).V {MugW.tPay} = 1
    unfold payCf
    rw [dif_pos (Finset.singleton_nonempty _)]
    simp
  have hb : (payCf (mugActEv () .b)).V (mugActEv () .b) = 0 := by
    show (payCf {MugW.tRefuse}).V {MugW.tRefuse} = 0
    unfold payCf
    rw [dif_pos (Finset.singleton_nonempty _)]
    simp only [State.ofConst_V]
    rw [if_neg (by decide)]
  unfold cudtProc
  apply uniformArgmax_eq_pure
  apply argmaxFull_act2_eq_a
  show (payCf (mugActEv () .b)).V (mugActEv () .b) < (payCf (mugActEv () .a)).V (mugActEv () .a)
  rw [ha, hb]
  norm_num

end t8mug

end Cleanroom.Decision.DpFaithfulUdt

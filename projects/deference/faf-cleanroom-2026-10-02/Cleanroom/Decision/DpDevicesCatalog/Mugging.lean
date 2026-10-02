import Cleanroom.Decision.DpDevicesCatalog.Values
import Cleanroom.Decision.DpCalibration.Mugging
import Cleanroom.Decision.DpCalibration.Corollaries

set_option autoImplicit false

/-!
# `dp-devices-catalog` — T7: the mugging, first-person carriers (L1, FP-1/2/4/6, ID-15)

On `B₁ = mug1 x y` (`0 < x < y`) with the no-doubt state `mugState1 q₀` (`P(T) = 1`):

* (a) `mug1_strictOC_iff`: strictly OC-calibrated for `procQ q` exactly at `q = q₀` (L1);
* (b) `mug1_not_perRunSSC_all`, `mug1_not_perOccSSC_all`: no procedure makes the no-doubt state
  per-run or per-occurrence SSC (both demand `P(T) = ½`: `occ = univ`, `#_d ≡ 1`);
* (c) **FP-1 for every state** (the per-sense skeleton): strict, limit and masked OC at the
  tails point force `P_s(H) = 0`; per-run and per-occurrence SSC force `P_s(H) = ½`;
* (d) **FP-2 typed**: two strict states agree modulo junk (`strictClausesAt_unique`), and the
  transfer `y` is invisible — a strict state for `(C, mug1 x y)` is a strict state for
  `(C, mug1 x y')` (the finite-carrier rendering of "`V` undefined on heads events");
* (e) **FP-4 the third carrier**: dp-cf-2-013's act-supposition `½δ_{(T,pay,0)} + ½δ_{(H,pay,1)}`
  does not live on the four-world carrier `MugW` (no atom `(H, pay, 1)`); its pushforward
  `½δ_{tPay} + ½δ_{hOne}` has value `½(y−x)`, and "`ν(H ∧ pay) = 0` for every `C'`" is `T`
  here because the event is empty (findings F8);
* (f) **FP-6**: `B₁` and `B₂` have the same strict state at `q₀` (`Agree`) while
  `V_{B₁} − V_{B₂} = y(2q−1)/2` — they differ iff `q ≠ ½` (the mandate's "every interior `q`"
  is a slip, findings F7);
* (g) **the anthropic indifference axiom** `AnthropicIndiff` (`P_s ≪ μ(· ∣ occ(d))`, support
  inclusion on a finite carrier), a necessary condition of per-run clause 1; the tails-certain
  state satisfies it on `B₁` (N+) while the density bound fails (`2 > 1`, N−).

Cited from dp-calibration: `mug_maskedOC_all`, `mug1_masked_not_strict`, `mug1_perRun_not_strict`,
`mug1_occ`, `mug1_value`, `mug2_value`, `mug1_nu`, `mug2_nu`, `no_uniform_optimum`.
-/

namespace Cleanroom.Decision.DpDevicesCatalog

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt

/-- The heads worlds `{H}` of the mugging carrier. Source: v2 Prop. 6. Kind: D -/
def mugH : Finset MugW := {.hOne, .hZero}

section mugging

variable (x y : ℚ)

/-! ## Infrastructure -/

/-- `#_d ≡ 1` on `B₁`. Source: `firstperson.md` FP-1 ("`#_d ≡ 1`"). Kind: L -/
theorem mug1_count (ℓ : (mug1 x y).Leaves) : count () (mug1 x y) ℓ = 1 := by
  unfold mug1 at ℓ ⊢
  rcases ℓ with ⟨i, act, _⟩
  simp

/-- `𝔼[#_d 1_X] = ν(X)` on `B₁`. Source: none: infrastructure. Kind: L -/
theorem mug1_countMass (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset MugW) :
    countMass C (mug1 x y) () X = nu C (mug1 x y) X := by
  unfold countMass nu mass
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [mug1_count]; simp

/-- `𝔼[r 1_X]` on `B₁`: only `tPay` (`−x`) and `hOne` (`y`) pay.
Source: none: infrastructure. Kind: L -/
theorem mug1_paySum (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset MugW) :
    paySum C (mug1 x y) X =
      (if MugW.tPay ∈ X then (1/2 : ℚ) * (C ()).w .a * (-x) else 0) +
      (if MugW.hOne ∈ X then (1/2 : ℚ) * (C ()).w .a * y else 0) := by
  rw [paySum_eq_sum_ite, mug1_sum]
  simp [Fin.sum_univ_two, Act2.sum_univ, mug1, mugWorld1, mugPay, FinDistr.fair, FinDistr.coin]
  ring

/-- `𝔼[r 1_X]` on `B₂`: `tPay` (`−x`) and `hOne` (`y`, reached by refusing).
Source: none: infrastructure. Kind: L -/
theorem mug2_paySum (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset MugW) :
    paySum C (mug2 x y) X =
      (if MugW.tPay ∈ X then (1/2 : ℚ) * (C ()).w .a * (-x) else 0) +
      (if MugW.hOne ∈ X then (1/2 : ℚ) * (C ()).w .b * y else 0) := by
  rw [paySum_eq_sum_ite, mug2_sum]
  simp [Fin.sum_univ_two, Act2.sum_univ, mug2, mugWorld2, mugPay, FinDistr.fair, FinDistr.coin]
  ring

/-- `mugH ∩ O_T = ∅`. Source: none: infrastructure. Kind: L -/
theorem mugH_inter_obs : mugH ∩ mugObs () = ∅ := by decide

/-- `ν(H) = ½` for every procedure on `B₁`. Source: none: infrastructure. Kind: L -/
theorem mug1_nu_H (C : Proc Unit (fun _ => Act2) ℚ) : nu C (mug1 x y) mugH = 1 / 2 := by
  rw [mug1_nu]
  have := (C ()).sum_one
  rw [Act2.sum_univ] at this
  simp [mugH]; linarith

/-! ## (a) L1: strictly calibrated exactly at `q = q₀` -/

/-- **L1 completed**: the no-doubt state `mugState1 q₀` is strictly OC-calibrated at `d` for
`procQ q` iff `q = q₀` (clause 1 at `{tPay}` reads `q₀ · ½ = ½ q`).
Source: `sl-workflow/notes/repair/L1.md` line 79 ("strictly OC-calibrated exactly at
`q = q₀`"); v2 Proposition 6
Kind: P
Fidelity: exact
Hyps: (a) `0 ≤ q, q₀ ≤ 1` -/
theorem mug1_strictOC_iff (q₀ q : ℚ) (h0 : 0 ≤ q₀) (h1 : q₀ ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    StrictOCAt (fun _ => mugState1 x y q₀ h0 h1) mugObs (procQ q hq0 hq1) (mug1 x y) () ↔
      q = q₀ := by
  constructor
  · intro h
    have hpos : 0 < nu (procQ q hq0 hq1) (mug1 x y) (mugObs ()) := by rw [mug1_nu_obs]; norm_num
    have := (h hpos).1 {.tPay}
    rw [mug1_nu_obs, (mugState1_beliefs x y q₀ h0 h1).2.2, mug1_nu] at this
    simp [mugObs, procQ] at this
    linarith
  · rintro rfl
    exact strictOCAt_calibratedState mugObs _ (mug1 x y) _ () _ rfl

/-! ## (b) The no-doubt state is SSC-calibrated for no procedure -/

/-- **No procedure makes the no-doubt state per-run SSC at `d`**: `occ(d)` is every run, so
per-run clause 1 at `O_T` demands `P_s(O_T) = ν(O_T) = ½`, but `P_s(O_T) = 1`.
Source: `firstperson.md` FP-1 ("per-run … SSC … force `P_s(H) = ½`"); mandate T7(b)
Kind: P
Fidelity: exact (every procedure)
Hyps: none beyond `q₀ ∈ [0,1]` -/
theorem mug1_not_perRunSSC_all (q₀ : ℚ) (h0 : 0 ≤ q₀) (h1 : q₀ ≤ 1)
    (C : Proc Unit (fun _ => Act2) ℚ) :
    ¬ PerRunSSCAt (fun _ => mugState1 x y q₀ h0 h1) C (mug1 x y) () := by
  intro h
  have hpos : 0 < mass C (mug1 x y) (occ () (mug1 x y)) := by rw [mug1_occ, mass_univ]; norm_num
  have := (h hpos).1 (mugObs ())
  rw [mug1_occ, mass_univ, Finset.inter_univ, (mugState1_beliefs x y q₀ h0 h1).1] at this
  have h2 : mass C (mug1 x y) (worldEv (mug1 x y) (mugObs ())) = 1 / 2 := mug1_nu_obs x y C
  rw [h2] at this
  norm_num at this

/-- **No procedure makes the no-doubt state per-occurrence SSC at `d`** (`#_d ≡ 1` makes the
per-occurrence clause the per-run one).
Source: `firstperson.md` FP-1 ("per-occurrence SSC … force `P_s(H) = ½`"); mandate T7(b)
Kind: P
Fidelity: exact (every procedure) -/
theorem mug1_not_perOccSSC_all (q₀ : ℚ) (h0 : 0 ≤ q₀) (h1 : q₀ ≤ 1)
    (C : Proc Unit (fun _ => Act2) ℚ) :
    ¬ PerOccSSCAt (fun _ => mugState1 x y q₀ h0 h1) C (mug1 x y) () := by
  intro h
  have hpos : 0 < countMass C (mug1 x y) () Finset.univ := by
    rw [mug1_countMass, nu_univ]; norm_num
  have := (h hpos).1 (mugObs ())
  rw [mug1_countMass, mug1_countMass, nu_univ, mug1_nu_obs,
    (mugState1_beliefs x y q₀ h0 h1).1] at this
  norm_num at this

/-! ## (c) FP-1 for every state: the per-sense skeleton -/

/-- **FP-1, strict**: every strictly OC-calibrated state at the tails point is heads-blind,
`P_s(H) = 0` (clause 1 at `H`: `P_s(H) · ½ = ν(H ∧ O_T) = ν(∅) = 0`).
Source: `firstperson.md` FP-1 ("strict (Def 8) … force `P_s(H) = 0`")
Kind: P
Fidelity: exact (every state, every procedure)
Hyps: (a) strict OC at `d` -/
theorem mug1_strictOCAt_H_zero (s : Unit → State MugW ℚ) (C : Proc Unit (fun _ => Act2) ℚ)
    (h : StrictOCAt s mugObs C (mug1 x y) ()) : (s ()).pr mugH = 0 := by
  have hpos : 0 < nu C (mug1 x y) (mugObs ()) := by rw [mug1_nu_obs]; norm_num
  have := (h hpos).1 mugH
  rw [mug1_nu_obs, mugH_inter_obs, nu_empty] at this
  linarith

/-- **FP-1, limit**: every limit-calibrated state at the tails point has `P_s(H) = 0`
(limit calibration refines strict calibration at the realized point).
Source: `firstperson.md` FP-1 ("limit (Def 10) … force `P_s(H) = 0`")
Kind: C
Fidelity: exact
Hyps: (a) limit OC at `d` -/
theorem mug1_limitOCAt_H_zero (s : Unit → State MugW ℚ) (C : Proc Unit (fun _ => Act2) ℚ)
    (h : LimitOCAt s mugObs C (mug1 x y) ()) : (s ()).pr mugH = 0 :=
  mug1_strictOCAt_H_zero x y s C (limitOCAt_imp_strictOCAt s mugObs C (mug1 x y) () h)

/-- **FP-1, masked**: every masked-calibrated state at the tails point has `P_s(H) = 0` — the
self-model realizes `O_T` only through `T`-worlds, and the vacuity disjunct is impossible
(`ν_{C'}(O_T) = ½` for every self-model).
Source: `firstperson.md` FP-1 ("masked (Def 9, self-model `m(pay) = q₀`) … force `P_s(H) = 0`")
Kind: P
Fidelity: exact (LF, vacuity reading)
Hyps: (a) masked OC at `d` -/
theorem mug1_maskedOCAt_H_zero (s : Unit → State MugW ℚ) (C : Proc Unit (fun _ => Act2) ℚ)
    (h : MaskedOCAt s mugObs C (mug1 x y) ()) : (s ()).pr mugH = 0 := by
  rcases h with ⟨C', -, hpos, hcl⟩ | ⟨-, hvac⟩
  · have := hcl.1 mugH
    rw [mug1_nu_obs, mugH_inter_obs, nu_empty] at this
    linarith
  · exfalso
    have := hvac (C.deviate () FinDistr.uniform)
      ⟨FinDistr.uniform, fun a => FinDistr.uniform_w_pos a, rfl⟩
    rw [mug1_nu_obs] at this
    norm_num at this

/-- **FP-1, per-run SSC**: every per-run-SSC state at `d` is heads-aware, `P_s(H) = ½`
(`occ(d)` is every run and `ν(H) = ½`).
Source: `firstperson.md` FP-1 ("per-run … SSC … force `P_s(H) = ½`")
Kind: P
Fidelity: exact
Hyps: (a) per-run SSC at `d` -/
theorem mug1_perRunSSCAt_H_half (s : Unit → State MugW ℚ) (C : Proc Unit (fun _ => Act2) ℚ)
    (h : PerRunSSCAt s C (mug1 x y) ()) : (s ()).pr mugH = 1 / 2 := by
  have hpos : 0 < mass C (mug1 x y) (occ () (mug1 x y)) := by rw [mug1_occ, mass_univ]; norm_num
  have := (h hpos).1 mugH
  rw [mug1_occ, mass_univ, Finset.inter_univ, mul_one] at this
  rw [this]
  exact mug1_nu_H x y C

/-- **FP-1, per-occurrence SSC**: every per-occurrence-SSC state at `d` has `P_s(H) = ½`.
Source: `firstperson.md` FP-1
Kind: P
Fidelity: exact
Hyps: (a) per-occurrence SSC at `d` -/
theorem mug1_perOccSSCAt_H_half (s : Unit → State MugW ℚ) (C : Proc Unit (fun _ => Act2) ℚ)
    (h : PerOccSSCAt s C (mug1 x y) ()) : (s ()).pr mugH = 1 / 2 := by
  have hpos : 0 < countMass C (mug1 x y) () Finset.univ := by
    rw [mug1_countMass, nu_univ]; norm_num
  have := (h hpos).1 mugH
  rw [mug1_countMass, mug1_countMass, nu_univ, mul_one, mug1_nu_H] at this
  exact this

/-! ## (d) FP-2 typed -/

/-- **FP-2 typed, uniqueness**: any two strictly calibrated states at the tails point agree
modulo junk — the finite-carrier rendering of "`V_s` is undefined on heads events": `V` on
`H`-events (which are `P_s`-null by FP-1) is never read.
Source: `firstperson.md` FP-2 ("`V_s` *undefined* on every heads event (clause 2's domain)")
Kind: L
Fidelity: variant: finite-carrier rendering of "undefined" (junk off the support)
Hyps: (a) strict OC at `d` for both -/
theorem mug1_strict_states_agree (s s' : Unit → State MugW ℚ) (C : Proc Unit (fun _ => Act2) ℚ)
    (hs : StrictOCAt s mugObs C (mug1 x y) ()) (hs' : StrictOCAt s' mugObs C (mug1 x y) ()) :
    State.Agree (s ()) (s' ()) := by
  have hpos : 0 < nu C (mug1 x y) (mugObs ()) := by rw [mug1_nu_obs]; norm_num
  exact strictClausesAt_unique mugObs C (mug1 x y) s s' () hpos (hs hpos) (hs' hpos)

/-- **FP-2 typed, invisibility of the transfer**: a strict state for `(C, B₁(x, y))` is a
strict state for `(C, B₁(x, y'))` — the transfer `y` never enters `(P_s, V_s)` at the tails
point (`ν` is `y`-independent and no `O_T`-world pays `y`).
Source: `firstperson.md` FP-2 ("the `y` is excluded from `(P_s, V_s)` by type")
Kind: P
Fidelity: exact
Hyps: (a) strict OC at `d` -/
theorem mug1_strictOCAt_transfer_invisible (y' : ℚ) (s : Unit → State MugW ℚ)
    (C : Proc Unit (fun _ => Act2) ℚ) (h : StrictOCAt s mugObs C (mug1 x y) ()) :
    StrictOCAt s mugObs C (mug1 x y') () := by
  intro _
  have hpos : 0 < nu C (mug1 x y) (mugObs ()) := by rw [mug1_nu_obs]; norm_num
  obtain ⟨h1, h2⟩ := h hpos
  refine ⟨fun X => ?_, fun X hX hXO => ?_⟩
  · rw [mug1_nu, mug1_nu]
    have := h1 X
    rw [mug1_nu, mug1_nu] at this
    exact this
  · have hXO' : 0 < nu C (mug1 x y) (X ∩ mugObs ()) := by
      rw [mug1_nu] at hXO ⊢; exact hXO
    have := h2 X hX hXO'
    rw [mug1_nu, mug1_paySum] at this
    rw [mug1_nu, mug1_paySum]
    have hno : MugW.hOne ∉ X ∩ mugObs () := by simp [mugObs]
    simp only [hno, if_false] at this ⊢
    exact this

/-! ## (e) FP-4: the third carrier, on this encoding -/

/-- **The pushforward of dp-cf-2-013's act-supposition to the four-world carrier**:
`½ δ_{tPay} + ½ δ_{hOne}`. The source's atom `(H, pay, 1)` does not exist in `MugW` (the `H`-leaf
world `hOne = (H, ⊥, 1)` records the transfer, not the simulated act), so this is the nearest
carrier the encoding admits.
Source: `firstperson.md` FP-4 ("the act-supposition `½δ_{(T,pay,0)} + ½δ_{(H,pay,1)}`");
dp-cf-2-013; findings F8
Kind: D
Fidelity: variant: pushed forward to the four leaf-worlds -/
def thirdCarrier : FinDistr ℚ MugW where
  w := fun | .tPay => 1/2 | .hOne => 1/2 | .tRefuse => 0 | .hZero => 0
  nonneg := by intro w; cases w <;> norm_num
  sum_one := by
    have : (Finset.univ : Finset MugW) = {.tPay, .tRefuse, .hOne, .hZero} := by
      ext w; cases w <;> simp
    rw [this]; simp; norm_num

/-- **FP-4's value**: `∑_ω thirdCarrier(ω) · r(ω) = ½(y − x)`.
Source: `firstperson.md` FP-4 ("gives `V(pay) = ½(y−x)`")
Kind: T
Fidelity: exact on the pushforward -/
theorem thirdCarrier_value : ∑ w, thirdCarrier.w w * mugPay x y w = (y - x) / 2 := by
  have : (Finset.univ : Finset MugW) = {.tPay, .tRefuse, .hOne, .hZero} := by
    ext w; cases w <;> simp
  rw [this]; simp [thirdCarrier, mugPay]; ring

/-- **FP-4's "uncalibratable" clause on this encoding**: `ν_{C'}(H ∧ pay) = 0` for every `C'`,
because the world-event `H ∧ {choice = pay}` is *empty* in `MugW` (`mugActEv () .a = {tPay}`):
the clause is trivially true, not a calibration fact — findings F8.
Source: `firstperson.md` FP-4 ("`ν_{B₁,C'}(H ∧ pay) = 0` for every `C'`"); dp-cf-2-013
Kind: T
Fidelity: weaker: the event is empty on this carrier -/
theorem mug1_nu_H_pay_zero (C : Proc Unit (fun _ => Act2) ℚ) :
    mugH ∩ mugActEv () .a = ∅ ∧ nu C (mug1 x y) (mugH ∩ mugActEv () .a) = 0 := by
  have h : mugH ∩ mugActEv () .a = ∅ := by decide
  exact ⟨h, by rw [h, nu_empty]⟩

/-- **`thirdCarrier` is the `P` of the per-run-SSC-calibrated state at `C = δ_pay`**, not merely
a pushforward: on this carrier `occ(d) = Leaves`, so per-run clause 1 reads `P_s = ν`, and
`ν_{δ_pay} = ½δ_{tPay} + ½δ_{hOne}`. The state is dp-calibration's calibrated state at `⊤`,
per-run SSC at `d` by `mug1_perRun_not_strict`. So FP-4's "uncalibratable" supposition has, as
its nearest rendering on the four-world carrier, a *calibrated* state at the SSC grade for the
payer (findings F8).
Source: `firstperson.md` FP-4; dp-cf-2-013; audit round 1 (fidelity N7)
Kind: P
Fidelity: variant: the four-world carrier's pushforward in place of the 12-atom supposition -/
theorem thirdCarrier_perRunSSC :
    PerRunSSCAt (fun _ => calibratedState (procQ 1 zero_le_one le_rfl) (mug1 x y) Finset.univ
      (nu_univ_pos _ _)) (procQ 1 zero_le_one le_rfl) (mug1 x y) () ∧
    ∀ X, (calibratedState (procQ 1 zero_le_one le_rfl) (mug1 x y) Finset.univ
      (nu_univ_pos _ _)).pr X = probOf thirdCarrier X := by
  refine ⟨(mug1_perRun_not_strict x y _).1, fun X => ?_⟩
  rw [calibratedState_pr, Finset.inter_univ, nu_univ, div_one, mug1_nu]
  have hU : (Finset.univ : Finset MugW) = {.tPay, .tRefuse, .hOne, .hZero} := by
    ext w; cases w <;> simp
  have hR : probOf thirdCarrier X =
      ∑ ω ∈ (Finset.univ : Finset MugW), if ω ∈ X then thirdCarrier.w ω else 0 := by
    unfold probOf
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [hR, hU, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  split_ifs <;> simp [thirdCarrier, procQ, FinDistr.act2_a, FinDistr.act2_b]

/-! ## (f) FP-6: `B₁` versus `B₂` -/

/-- **FP-6**: `B₁` and `B₂` have the same strict state at `q₀` (`Agree`: `ν(· ∧ O_T)` and
`𝔼[r 1_{· ∧ O_T}]` coincide, the `H`-branch being outside `O_T`), while
`V_{B₁}(C) − V_{B₂}(C) = y(2q − 1)/2`, so the values differ iff `q ≠ ½` (for `y ≠ 0`):
Proposition 6's separating datum lives outside the state.
Source: `firstperson.md` FP-6 ("strict-OC states identical in `(P, V)`"); mandate T7(f)
("`mug1_value ≠ mug2_value` for every interior `q`" — corrected: iff `q ≠ ½`, findings F7)
Kind: P (the `Agree` conjunct, a general fact for every `q₀`) / N+ (the value gap, exhibited)
Fidelity: exact -/
theorem mug_fp6 (q₀ : ℚ) (h0 : 0 ≤ q₀) (h1 : q₀ ≤ 1) (C : Proc Unit (fun _ => Act2) ℚ) :
    State.Agree (mugState1 x y q₀ h0 h1) (mugState2 x y q₀ h0 h1) ∧
    value C (mug1 x y) - value C (mug2 x y) = y * (2 * (C ()).w .a - 1) / 2 := by
  refine ⟨⟨?_, fun X hX => ?_⟩, ?_⟩
  · apply FinDistr.ext'
    intro w
    have e1 : (mugState1 x y q₀ h0 h1).pr {w} =
        nu (procQ q₀ h0 h1) (mug1 x y) ({w} ∩ mugObs ()) / nu (procQ q₀ h0 h1) (mug1 x y) (mugObs ()) :=
      calibratedState_pr _ _ _ _ {w}
    have e2 : (mugState2 x y q₀ h0 h1).pr {w} =
        nu (procQ q₀ h0 h1) (mug2 x y) ({w} ∩ mugObs ()) / nu (procQ q₀ h0 h1) (mug2 x y) (mugObs ()) :=
      calibratedState_pr _ _ _ _ {w}
    simp only [State.pr, probOf_singleton] at e1 e2
    rw [e1, e2, mug1_nu_obs, mug2_nu_obs, mug1_nu, mug2_nu]
    cases w <;> simp [mugObs]
  · rw [mugState1, mugState2, calibratedState_V, calibratedState_V, mug1_nu, mug2_nu,
      mug1_paySum, mug2_paySum]
    have hno : MugW.hOne ∉ X ∩ mugObs () := by simp [mugObs]
    have hno' : MugW.hZero ∉ X ∩ mugObs () := by simp [mugObs]
    simp only [hno, hno', if_false]
  · rw [mug1_value, mug2_value]; ring

/-! ## (g) The anthropic indifference axiom -/

/-- **The anthropic indifference axiom** (ID-15): `P_s ≪ μ_{B,C}(· ∣ occ(d))` — on a finite
carrier, absolute continuity *is* support inclusion: every `P_s`-positive world has positive
`μ`-mass within `occ(d)`.
Source: `identity.md` ID-15 ("the **anthropic indifference axiom** `P_s ≪ μ(· ∣ occ(d))`");
dp-cf-070
Kind: D
Fidelity: exact (finite carrier: `≪` is support inclusion) -/
def AnthropicIndiff {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] {acts : ι → Type}
    [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] (s : State Ω ℚ) (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (d : ι) :
    Prop :=
  ∀ ω, 0 < s.pr {ω} → 0 < mass C B (worldEv B {ω} ∩ occ d B)

/-- **Per-run clause 1 implies anthropic indifference** (ID-15's "necessary condition of
Definition 13's per-run equation"), where `μ(occ(d)) > 0`.
Source: `identity.md` ID-15 ("a *necessary condition* of Def 13's per-run equation")
Kind: L (a two-line consequence of clause 1 at `{ω}`; relabelled from `P` in audit round 1)
Fidelity: exact
Hyps: (a) per-run clause 1 at `d`, `0 < μ(occ(d))` -/
theorem perRunClause1_imp_anthropicIndiff {Ω ι : Type} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq ι] {acts : ι → Type} [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
    (s : ι → State Ω ℚ)
    (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (d : ι) (hpos : 0 < mass C B (occ d B))
    (h : PerRunClause1At s C B d) : AnthropicIndiff (s d) C B d := by
  intro ω hω
  rw [← h {ω}]
  exact mul_pos hω hpos

/-- **The tails-certain state satisfies anthropic indifference on `B₁`** (interior `q₀`): its
positive worlds `tPay`, `tRefuse` have masses `q₀/2`, `(1−q₀)/2 > 0`; the `H`-worlds are
`P_s`-null.
Source: `identity.md` ID-15; mandate T7(g)
Kind: N+ -/
theorem mugState1_anthropicIndiff (q₀ : ℚ) (h0 : 0 < q₀) (h1 : q₀ < 1) :
    AnthropicIndiff (mugState1 x y q₀ h0.le h1.le) (procQ q₀ h0.le h1.le) (mug1 x y) () := by
  intro w hw
  rw [mug1_occ, Finset.inter_univ]
  change 0 < nu (procQ q₀ h0.le h1.le) (mug1 x y) {w}
  rw [mugState1, calibratedState_pr, mug1_nu_obs, mug1_nu] at hw
  rw [mug1_nu]
  cases w <;> simp [mugObs, procQ] at hw ⊢ <;> linarith

/-- **The density bound fails on `B₁`** (ID-15's "D–Z bound: density `2 > 1/μ(occ(d)) = 1`"):
the tails-certain state is not dominated by `μ(· ∣ occ(d))`: at `tPay`, `P_s = q₀` but
`μ(occ)⁻¹ · μ(tPay ∧ occ) = q₀/2`. Stated as the concrete inequality; degenerate as a witness.
Source: `identity.md` ID-15 ("on `B₁` density `2 > 1/μ(occ(d)) = 1`, fails")
Kind: N−
Fidelity: exact -/
theorem mugState1_density_bound_fails (q₀ : ℚ) (h0 : 0 < q₀) (h1 : q₀ < 1) :
    ¬ ∀ ω, (mugState1 x y q₀ h0.le h1.le).pr {ω} ≤
      (mass (procQ q₀ h0.le h1.le) (mug1 x y) (occ () (mug1 x y)))⁻¹ *
        mass (procQ q₀ h0.le h1.le) (mug1 x y) (worldEv (mug1 x y) {ω} ∩ occ () (mug1 x y)) := by
  intro h
  have := h .tPay
  rw [mug1_occ, mass_univ, Finset.inter_univ, mugState1, calibratedState_pr, mug1_nu_obs] at this
  change (nu _ _ _) / _ ≤ _ * nu _ _ _ at this
  rw [mug1_nu, mug1_nu] at this
  simp [mugObs, procQ] at this
  linarith

end mugging

end Cleanroom.Decision.DpDevicesCatalog

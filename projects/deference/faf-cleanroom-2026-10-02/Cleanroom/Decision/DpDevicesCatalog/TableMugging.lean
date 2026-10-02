import Cleanroom.Decision.DpDevicesCatalog.Devices
import Cleanroom.Decision.DpDevicesCatalog.Mugging
import Cleanroom.Decision.DpCalibration.MiniDevices

set_option autoImplicit false

/-!
# `dp-devices-catalog` — T8, the mugging column of the device table (CA-20′)

`B₁ = mug1 x y` with `0 < x < y`, observation `O_T`, action events `{pay}`, `{refuse}`; every
row is a universal statement in `q := C(d)(pay)` (every procedure is a `procQ q`):

| device | verdict | declaration |
|---|---|---|
| D1 limit-state EDT | pay, refuse (every mixed `q` rejected) | `mug1_limitStateEdt_pure`, `mug1_not_limitStateEdt_interior` |
| D2 event-tremble EDT | refuse only (`−x < 0`) | `mug1_eventTremble_iff` |
| D4 advice EDT | refuse only | `mug1_adviceEdt_iff` |
| D3 (`ε > 0`) | pay only (`(y−x)/2 > 0`) | `mug1_occTremble_iff` |
| D3⁰ Theorem 1 | pay only | `mug1_occEdt_iff` |
| Dev pure / mixed | pay only | `mug1_coherentPureAt_iff`, `mug1_coherentAt_iff` |
| `V`-optimal | pay only | `mug1_isOptimal_iff` |

The two "exploration" devices give opposite verdicts (D2 refuse vs D3 pay): dp-cf-135 ZO-18.
-/

namespace Cleanroom.Decision.DpDevicesCatalog

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt

section table

variable (x y : ℚ)

/-! ## Infrastructure on `B₁` -/

/-- The payoff at a leaf of `B₁` is `mugPay` of its world. Source: none: infrastructure. Kind: L -/
theorem mug1_payoff_world (ℓ : (mug1 x y).Leaves) :
    payoff (mug1 x y) ℓ = mugPay x y (world (mug1 x y) ℓ) := by
  unfold mug1 at ℓ ⊢
  rcases ℓ with ⟨i, act, _⟩
  simp

/-- Every leaf of `B₁` is chance-positive (weight `½`). Source: none: infrastructure. Kind: L -/
theorem mug1_chanceWeight_pos (ℓ : (mug1 x y).Leaves) : 0 < chanceWeight (mug1 x y) ℓ := by
  unfold mug1 at ℓ ⊢
  rcases ℓ with ⟨i, act, _⟩
  simp [FinDistr.fair, FinDistr.coin]
  fin_cases i <;> norm_num

/-- The tails leaves' worlds. Source: none: infrastructure. Kind: L -/
theorem mug1_world_tails :
    world (mug1 x y) ⟨0, .a, ()⟩ = .tPay ∧ world (mug1 x y) ⟨0, .b, ()⟩ = .tRefuse := by
  constructor <;> simp [mug1, mugWorld1]

/-- Leaf-worlds in `{pay} ∧ O_T` pay `−x`; in `{refuse} ∧ O_T` pay `0`.
Source: none: infrastructure. Kind: L -/
theorem mug1_actObs_payoff :
    (∀ ℓ, world (mug1 x y) ℓ ∈ mugActEv () .a ∩ mugObs () → payoff (mug1 x y) ℓ = -x) ∧
    (∀ ℓ, world (mug1 x y) ℓ ∈ mugActEv () .b ∩ mugObs () → payoff (mug1 x y) ℓ = 0) := by
  constructor <;> intro ℓ h <;> rw [mug1_payoff_world] <;> simp [mugActEv, mugObs] at h <;>
    rw [h] <;> rfl

/-- Both action events within `O_T` are realized under every full-support procedure.
Source: none: infrastructure. Kind: L -/
theorem mug1_nu_actObs_pos {C : Proc Unit (fun _ => Act2) ℚ} (hC : C.FullSupport) (a : Act2) :
    0 < nu C (mug1 x y) (mugActEv () a ∩ mugObs ()) := by
  obtain ⟨w1, w2⟩ := mug1_world_tails x y
  cases a
  · exact nu_pos_of_leaf_fullSupport hC (mug1 x y) _ ⟨0, .a, ()⟩
      (by rw [w1]; simp [mugActEv, mugObs]) (mug1_chanceWeight_pos x y _)
  · exact nu_pos_of_leaf_fullSupport hC (mug1 x y) _ ⟨0, .b, ()⟩
      (by rw [w2]; simp [mugActEv, mugObs]) (mug1_chanceWeight_pos x y _)

/-- Both action events within `O_T` are tremble-realizable. Source: none: infrastructure.
Kind: L -/
theorem mug1_nuPoly_actObs_ne_zero (C : Proc Unit (fun _ => Act2) ℚ) (a : Act2) :
    nuPoly C (mug1 x y) (mugActEv () a ∩ mugObs ()) ≠ 0 := by
  obtain ⟨w1, w2⟩ := mug1_world_tails x y
  cases a
  · exact nuPoly_ne_zero_of_leaf C (mug1 x y) _ ⟨0, .a, ()⟩
      (by rw [w1]; simp [mugActEv, mugObs]) (mug1_chanceWeight_pos x y _)
  · exact nuPoly_ne_zero_of_leaf C (mug1 x y) _ ⟨0, .b, ()⟩
      (by rw [w2]; simp [mugActEv, mugObs]) (mug1_chanceWeight_pos x y _)

/-- `O_T` is tremble-realizable. Source: none: infrastructure. Kind: L -/
theorem mug1_nuPoly_obs_ne_zero (C : Proc Unit (fun _ => Act2) ℚ) :
    nuPoly C (mug1 x y) (mugObs ()) ≠ 0 :=
  nuPoly_ne_zero_of_leaf C (mug1 x y) _ ⟨0, .a, ()⟩
    (by rw [(mug1_world_tails x y).1]; simp [mugObs]) (mug1_chanceWeight_pos x y _)

/-- The point is queried. Source: none: infrastructure. Kind: L -/
theorem mug1_queried_mem : () ∈ queried (mug1 x y) := by rw [mug1_queried]; simp

/-- **The act-conditional values under any tremble**: `−x` for pay, `0` for refuse.
Source: `calibration.md` CA-20′ (D2 row, mugging: "refuse (`−x < 0`)")
Kind: L -/
theorem mug1_tremble_condExp (C : Proc Unit (fun _ => Act2) ℚ) (ε : ℚ) (h0 : 0 < ε)
    (h1 : ε ≤ 1) :
    condExp (tremble C ε h0.le h1) (mug1 x y) (mugActEv () .a ∩ mugObs ()) = -x ∧
    condExp (tremble C ε h0.le h1) (mug1 x y) (mugActEv () .b ∩ mugObs ()) = 0 := by
  have hC := tremble_fullSupport C ε h0 h1
  obtain ⟨pa, pb⟩ := mug1_actObs_payoff x y
  exact ⟨condExp_const _ _ _ _ pa (mug1_nu_actObs_pos x y hC .a),
    condExp_const _ _ _ _ pb (mug1_nu_actObs_pos x y hC .b)⟩

/-- **Theorem 1's functional on `B₁`** for every procedure: `Φ(pay) = (y − x)/2`,
`Φ(refuse) = 0` (the disposition's value, both branches counted).
Source: `calibration.md` CA-20′ (D3 row, mugging: "pay (`(y−x)/2`)")
Kind: P
Fidelity: exact -/
theorem mug1_siaSum (C : Proc Unit (fun _ => Act2) ℚ) :
    siaSum C (mug1 x y) () .a = (y - x) / 2 ∧ siaSum C (mug1 x y) () .b = 0 := by
  constructor <;>
  · simp [mug1, siaSum_decision, Fin.sum_univ_two, Act2.sum_univ, value_leaf, mugWorld1,
      mugPay, FinDistr.fair, FinDistr.coin]
    try ring

/-! ## D2 — event-tremble EDT: refuse only -/

/-- **D2 on the mugging approves exactly refusal** (`q = 0`): under every tremble the
`O_T`-conditional act values are `−x < 0` (pay) and `0` (refuse), both events realized within
`O_T` (so Definition 18's escape clause is discharged), hence a procedure with `pay` in its
support is rejected at every `ε`. The hypothesis `0 < x` is load-bearing: at `x = 0` both
act-conditionals are `0` and every label is D2-consistent (`mug1_eventTremble_x_zero`).
Source: `calibration.md` CA-20′ (D2 row, mugging: "refuse (`−x < 0`)"); dp-cf-049
Kind: P
Fidelity: exact (universal in `q`)
Hyps: (a) `0 < x` -/
theorem mug1_eventTremble_iff (hx : 0 < x) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    EventTrembleEdtConsistent mugObs mugActEv (procQ q hq0 hq1) (mug1 x y) ↔ q = 0 := by
  constructor
  · rintro ⟨ε₀, hε₀, h⟩
    by_contra hq
    have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
    have hmin0 : 0 < min ε₀ 1 := lt_min hε₀ one_pos
    have h0 : 0 < min ε₀ 1 / 2 := by linarith
    have h1 : min ε₀ 1 / 2 ≤ 1 := by linarith [min_le_right ε₀ 1]
    have hlt : min ε₀ 1 / 2 < ε₀ := by linarith [min_le_left ε₀ 1]
    have hfs := tremble_fullSupport (procQ q hq0 hq1) _ h0 h1
    obtain ⟨-, hcmp⟩ := h _ h0 h1 hlt () (mug1_queried_mem x y) (mug1_nuPoly_obs_ne_zero x y _)
      ⟨.a, mug1_nu_actObs_pos x y hfs .a⟩ .a (by simp [procQ, hqpos])
    have := hcmp .b (mug1_nu_actObs_pos x y hfs .b)
    obtain ⟨ca, cb⟩ := mug1_tremble_condExp x y _ _ h0 h1
    rw [ca, cb] at this
    linarith
  · rintro rfl
    refine ⟨1, one_pos, fun ε h0 h1 _ d _ _ _ a ha => ?_⟩
    cases d
    have hfs := tremble_fullSupport (procQ 0 hq0 hq1) ε h0 h1
    obtain ⟨ca, cb⟩ := mug1_tremble_condExp x y _ ε h0 h1
    cases a
    · simp [procQ] at ha
    · refine ⟨mug1_nu_actObs_pos x y hfs .b, fun b _ => ?_⟩
      cases b
      · rw [ca, cb]; linarith
      · exact le_rfl

/-! ## D4 — advice EDT: refuse only -/

/-- The tremble-limit act values on `B₁`: `−x` and `0` (constant-payoff events).
Source: `calibration.md` CA-20′ (D4 row, mugging: refuse)
Kind: L -/
theorem mug1_limitVal (C : Proc Unit (fun _ => Act2) ℚ) :
    limitVal C (mug1 x y) (mugActEv () .a ∩ mugObs ()) = -x ∧
    limitVal C (mug1 x y) (mugActEv () .b ∩ mugObs ()) = 0 := by
  obtain ⟨pa, pb⟩ := mug1_actObs_payoff x y
  exact ⟨limitVal_of_const _ _ _ _ pa (mug1_nuPoly_actObs_ne_zero x y C .a),
    limitVal_of_const _ _ _ _ pb (mug1_nuPoly_actObs_ne_zero x y C .b)⟩

/-- **D4 on the mugging approves exactly refusal**.
Source: `calibration.md` CA-20′ (D4 row, mugging: "refuse")
Kind: P
Fidelity: exact (universal in `q`)
Hyps: (a) `0 < x` -/
theorem mug1_adviceEdt_iff (hx : 0 < x) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    AdviceEdt mugObs mugActEv (procQ q hq0 hq1) (mug1 x y) ↔ q = 0 := by
  obtain ⟨la, lb⟩ := mug1_limitVal x y (procQ q hq0 hq1)
  constructor
  · intro h
    by_contra hq
    have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
    have := (h () (mug1_queried_mem x y) (mug1_nuPoly_obs_ne_zero x y _)
      ⟨.a, mug1_nuPoly_actObs_ne_zero x y _ .a⟩ .a (by simp [procQ, hqpos])).2 .b
      (mug1_nuPoly_actObs_ne_zero x y _ .b)
    rw [la, lb] at this
    linarith
  · rintro rfl
    intro d _ _ _ a ha
    cases d
    cases a
    · simp [procQ] at ha
    · refine ⟨mug1_nuPoly_actObs_ne_zero x y _ .b, fun b _ => ?_⟩
      cases b
      · rw [la, lb]; linarith
      · exact le_rfl

/-! ## D3⁰, D3 — Theorem 1 with and without trembles: pay only -/

/-- **D3⁰ (Theorem 1) on the mugging approves exactly paying** (`q = 1`), for `x < y`.
Source: `calibration.md` CA-20′ (D3⁰ row, mugging: "pay")
Kind: P
Fidelity: exact (universal in `q`)
Hyps: (a) `x < y` -/
theorem mug1_occEdt_iff (hxy : x < y) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    OccEdtConsistent (procQ q hq0 hq1) (mug1 x y) ↔ q = 1 := by
  rw [occEdtConsistent_iff_thm1]
  obtain ⟨ha, hb⟩ := mug1_siaSum x y (procQ q hq0 hq1)
  constructor
  · intro h
    have hth := (thm1At_procQ_iff (mug1 x y) q hq0 hq1).mp (h () (mug1_queried_mem x y))
    by_contra hne
    have hlt : 0 < 1 - q := by
      rcases lt_or_eq_of_le hq1 with h' | h'
      · linarith
      · exact absurd h' hne
    have := hth.2 hlt
    rw [ha, hb] at this
    linarith
  · rintro rfl
    intro d _
    cases d
    rw [thm1At_procQ_iff]
    exact ⟨fun _ => by rw [ha, hb]; linarith, fun h => by norm_num at h⟩

/-- **D3 (`ε > 0`) on the mugging approves exactly paying**: Theorem 1's functional is
procedure-independent on `B₁`, so the tremble changes nothing.
Source: `calibration.md` CA-20′ (D3 row, mugging: "pay (`(y−x)/2`)")
Kind: P
Fidelity: exact (universal in `q`)
Hyps: (a) `x < y` -/
theorem mug1_occTremble_iff (hxy : x < y) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    OccTrembleEdtConsistent (procQ q hq0 hq1) (mug1 x y) ↔ q = 1 := by
  rw [occTrembleEdtConsistent_iff]
  constructor
  · rintro ⟨ε₀, hε₀, h⟩
    by_contra hne
    have hlt1 : 0 < 1 - q := by
      rcases lt_or_eq_of_le hq1 with h' | h'
      · linarith
      · exact absurd h' hne
    have hmin0 : 0 < min ε₀ 1 := lt_min hε₀ one_pos
    have h0 : 0 < min ε₀ 1 / 2 := by linarith
    have h1 : min ε₀ 1 / 2 ≤ 1 := by linarith [min_le_right ε₀ 1]
    have hlt : min ε₀ 1 / 2 < ε₀ := by linarith [min_le_left ε₀ 1]
    have := h _ h0 h1 hlt () (mug1_queried_mem x y) .b (by simp [procQ]; linarith) .a
    obtain ⟨ha, hb⟩ := mug1_siaSum x y (tremble (procQ q hq0 hq1) _ h0.le h1)
    rw [ha, hb] at this
    linarith
  · rintro rfl
    refine ⟨1, one_pos, fun ε h0 h1 _ d _ a ha b => ?_⟩
    cases d
    obtain ⟨ha', hb'⟩ := mug1_siaSum x y (tremble (procQ 1 hq0 hq1) ε h0.le h1)
    cases a
    · cases b
      · exact le_rfl
      · rw [ha', hb']; linarith
    · simp [procQ] at ha

/-! ## Dev, opt — pay only -/

/-- **Mixed Definition 22 on the mugging holds exactly at paying** (`V = q(y−x)/2` is maximised
at `q = 1` only).
Source: `calibration.md` CA-20′ (Dev mixed row, mugging: "pay")
Kind: P
Fidelity: exact (universal in `q`)
Hyps: (a) `x < y` -/
theorem mug1_coherentAt_iff (hxy : x < y) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    CoherentAt (procQ q hq0 hq1) (mug1 x y) () ↔ q = 1 := by
  rw [coherentAt_procQ_iff]
  simp only [mug1_value, procQ, FinDistr.act2_a]
  have hyx : 0 < y - x := sub_pos.2 hxy
  constructor
  · intro h
    have := h 1 zero_le_one le_rfl
    have h2 : (1 - q) * (y - x) ≤ 0 := by linarith
    have h3 : 0 ≤ (1 - q) * (y - x) := mul_nonneg (by linarith) hyx.le
    rcases mul_eq_zero.mp (le_antisymm h2 h3) with h' | h'
    · linarith
    · linarith
  · rintro rfl
    intro r r0 r1
    nlinarith

/-- **Pure Definition 22 on the mugging holds exactly at paying**.
Source: `calibration.md` CA-20′ (Dev pure row, mugging: "pay")
Kind: P
Fidelity: exact
Hyps: (a) `x < y` -/
theorem mug1_coherentPureAt_iff (hxy : x < y) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    CoherentPureAt (procQ q hq0 hq1) (mug1 x y) () ↔ q = 1 := by
  rw [coherentPureAt_procQ_iff]
  simp only [mug1_value, procQ, FinDistr.act2_a]
  have hyx : 0 < y - x := sub_pos.2 hxy
  constructor
  · rintro ⟨h, -⟩
    have h2 : (1 - q) * (y - x) ≤ 0 := by linarith
    have h3 : 0 ≤ (1 - q) * (y - x) := mul_nonneg (by linarith) hyx.le
    rcases mul_eq_zero.mp (le_antisymm h2 h3) with h' | h'
    · linarith
    · linarith
  · rintro rfl
    constructor <;> nlinarith

/-- **`V`-optimality on the mugging holds exactly at paying** (the direction is
`no_uniform_optimum`'s; here the full iff).
Source: `calibration.md` CA-20′ (`V`-optimal row, mugging: "pay"); v2 Proposition 6
Kind: P
Fidelity: exact
Hyps: (a) `x < y` -/
theorem mug1_isOptimal_iff (hxy : x < y) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsOptimal (procQ q hq0 hq1) (mug1 x y) ↔ q = 1 := by
  rw [isOptimal_procQ_iff, ← coherentAt_procQ_iff]
  exact mug1_coherentAt_iff x y hxy q hq0 hq1

/-! ## D1 — limit-state EDT: the two pure procedures, no mixed one -/

/-- The strict (= limit, the point being realized) state of `procQ q` at `O_T`.
Source: none: infrastructure. Kind: D -/
noncomputable def mugLimitState (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : State MugW ℚ :=
  calibratedState (procQ q h0 h1) (mug1 x y) (mugObs ()) (by rw [mug1_nu_obs]; norm_num)

/-- `P_s(pay) = q`, `P_s(refuse) = 1 − q` at the strict state. Source: none: infrastructure.
Kind: L -/
theorem mugLimitState_pr (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (mugLimitState x y q h0 h1).pr (mugActEv () .a) = q ∧
    (mugLimitState x y q h0 h1).pr (mugActEv () .b) = 1 - q := by
  simp only [mugLimitState, calibratedState_pr, mug1_nu_obs, mug1_nu, mugActEv, mugObs, procQ,
    FinDistr.act2_a, FinDistr.act2_b]
  constructor <;> simp <;> ring

/-- The strict state is limit-calibrated (the point is realized).
Source: v2 Lemma 2's converse at realized points (`limitOCAt_of_strictOCAt_of_pos`)
Kind: L -/
theorem mugLimitState_limitOC (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    LimitOC (fun _ => mugLimitState x y q h0 h1) mugObs (procQ q h0 h1) (mug1 x y) := by
  intro d _
  cases d
  exact limitOCAt_of_strictOCAt_of_pos _ mugObs _ (mug1 x y) () (by rw [mug1_nu_obs]; norm_num)
    (strictOCAt_calibratedState mugObs _ (mug1 x y) _ () _ rfl)

/-- **D1 approves both pure procedures on the mugging** (CA-17′: at a recorded on-path point
the limit state has `A⁺ = supp C(d)`, so `T_EDT` is vacuous): with the strict state of `δ_pay`
(resp. `δ_refuse`), `A⁺ = {pay}` (resp. `{refuse}`).
Source: `calibration.md` CA-17′ ("D1 approves pay and refuse on the mugging"), CA-20′ (D1 row)
Kind: N+
Fidelity: exact -/
theorem mug1_limitStateEdt_pure :
    LimitStateEdt mugObs mugActEv (procQ 1 zero_le_one le_rfl) (mug1 x y)
      (fun _ => mugLimitState x y 1 zero_le_one le_rfl) ∧
    LimitStateEdt mugObs mugActEv (procQ 0 le_rfl zero_le_one) (mug1 x y)
      (fun _ => mugLimitState x y 0 le_rfl zero_le_one) := by
  constructor
  · refine ⟨mugLimitState_limitOC x y 1 _ _, fun d _ _ a ha => ?_⟩
    cases d
    obtain ⟨pa, pb⟩ := mugLimitState_pr x y 1 zero_le_one le_rfl
    cases a
    · rw [mem_argmaxPlus]
      refine ⟨by simp [APlus, pa], fun b hb => ?_⟩
      cases b
      · exact le_rfl
      · simp [APlus, pb] at hb
    · simp [procQ] at ha
  · refine ⟨mugLimitState_limitOC x y 0 _ _, fun d _ _ a ha => ?_⟩
    cases d
    obtain ⟨pa, pb⟩ := mugLimitState_pr x y 0 le_rfl zero_le_one
    cases a
    · simp [procQ] at ha
    · rw [mem_argmaxPlus]
      refine ⟨by simp [APlus, pb], fun b hb => ?_⟩
      cases b
      · simp [APlus, pa] at hb
      · exact le_rfl

/-- **D1 rejects every mixed procedure on the mugging**, with every state assignment: a
limit-calibrated state at the realized `O_T` is the strict one, whose act values are `−x`
(pay) and `0` (refuse), both acts subjectively possible; `pay ∈ supp` is then not in the argmax.
Source: `calibration.md` CA-17′/CA-20′ (D1 row: "both" = the two pure procedures)
Kind: P
Fidelity: exact (every `s`)
Hyps: (a) `0 < x`, `0 < q < 1` -/
theorem mug1_not_limitStateEdt_interior (hx : 0 < x) (q : ℚ) (h0 : 0 < q) (h1 : q < 1)
    (s : Unit → State MugW ℚ) :
    ¬ LimitStateEdt mugObs mugActEv (procQ q h0.le h1.le) (mug1 x y) s := by
  rintro ⟨hlim, hedt⟩
  have hpos : 0 < nu (procQ q h0.le h1.le) (mug1 x y) (mugObs ()) := by
    rw [mug1_nu_obs]; norm_num
  obtain ⟨c1, c2⟩ := limitOCAt_imp_strictOCAt s mugObs _ (mug1 x y) ()
    (hlim () (mug1_queried_mem x y)) hpos
  -- beliefs
  have hpa : (s ()).pr (mugActEv () .a) = q := by
    have := c1 (mugActEv () .a)
    rw [mug1_nu_obs, mug1_nu] at this
    simp [mugActEv, mugObs, procQ, State.pr] at this ⊢
    linarith
  have hpb : (s ()).pr (mugActEv () .b) = 1 - q := by
    have := c1 (mugActEv () .b)
    rw [mug1_nu_obs, mug1_nu] at this
    simp [mugActEv, mugObs, procQ, State.pr] at this ⊢
    linarith
  -- values
  have hnua : 0 < nu (procQ q h0.le h1.le) (mug1 x y) (mugActEv () .a ∩ mugObs ()) := by
    rw [mug1_nu]; simp [mugActEv, mugObs, procQ]; linarith
  have hnub : 0 < nu (procQ q h0.le h1.le) (mug1 x y) (mugActEv () .b ∩ mugObs ()) := by
    rw [mug1_nu]; simp [mugActEv, mugObs, procQ]; linarith
  have hva : (s ()).V (mugActEv () .a) = -x := by
    have := c2 (mugActEv () .a) (by rw [hpa]; exact h0) hnua
    rw [mug1_nu, mug1_paySum] at this
    simp [mugActEv, mugObs, procQ] at this
    have hq : q ≠ 0 := h0.ne'
    field_simp at this
    simpa [mugActEv] using this
  have hvb : (s ()).V (mugActEv () .b) = 0 := by
    have := c2 (mugActEv () .b) (by rw [hpb]; linarith) hnub
    rw [mug1_nu, mug1_paySum] at this
    simp [mugActEv, mugObs, procQ] at this
    rcases this with h | h
    · simpa [mugActEv] using h
    · linarith
  -- `pay` is played and in `A⁺`, so it must be in the argmax; but `V(refuse) = 0 > −x = V(pay)`
  have hne : (APlus s mugActEv ()).Nonempty := ⟨.a, by simp [APlus, hpa, h0]⟩
  have hmem := hedt () (mug1_queried_mem x y) hne .a (by simp [procQ, h0])
  rw [mem_argmaxPlus] at hmem
  have := hmem.2 .b (by simp [APlus, hpb]; linarith)
  rw [hva, hvb] at this
  linarith

end table

/-- **`mug1_eventTremble_iff`'s `0 < x` is load-bearing**: at `x = 0` every label is
D2-consistent on `B₁(0, y)`, both act-conditional values being `0` under every tremble.
Source: none: infrastructure (audit round 1, adversarial probe P6)
Kind: N− -/
theorem mug1_eventTremble_x_zero (y q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    EventTrembleEdtConsistent mugObs mugActEv (procQ q hq0 hq1) (mug1 0 y) := by
  refine ⟨1, one_pos, fun ε h0 h1 _ d _ _ _ a _ => ?_⟩
  cases d
  have hfs := tremble_fullSupport (procQ q hq0 hq1) ε h0 h1
  obtain ⟨ca, cb⟩ := mug1_tremble_condExp 0 y (procQ q hq0 hq1) ε h0 h1
  refine ⟨mug1_nu_actObs_pos 0 y hfs a, fun b _ => ?_⟩
  cases a <;> cases b <;> simp only [ca, cb] <;> norm_num

end Cleanroom.Decision.DpDevicesCatalog

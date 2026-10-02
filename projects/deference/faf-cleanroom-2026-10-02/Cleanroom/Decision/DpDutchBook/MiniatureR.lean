import Cleanroom.Decision.DpDutchBook.Cast
import Cleanroom.Decision.DpDutchBook.EpsFixed

/-!
# T8(d): the `ℝ` witnesses of `d2At_exists` and `testSeq_exists` on the cast miniature

Audit round 1 (adversarial §3.3) noted that `d2At_exists` and `testSeq_exists` carried their
non-vacuity by citation to `dp-calib-limits`' miniature witnesses over `ℚ`, while the theorems
are over `ℝ`. This file inhabits the `ℝ` statements on `miniR := castTree miniature`, computed
directly (no `dp-calib-limits` import):

* `act2R`, `procR` — a real label `(q, 1 − q)` at the miniature's one point.
* `miniR_nu_live`, `miniR_paySum_live_a/_b`, `miniR_condExp` — `ν(a ∧ ⊤) = C(a)` and the strictly
  calibrated values `(2·C(b), C(a))` at every full-support real label (the `ℝ` twin of
  `dp-calibration`'s `miniature_condExp`).
* `qStarR ε = (4 − 3ε)/(6(1 − ε))`, `procStarR` — the label whose own `ε`-tremble is exactly
  `2/3` (`tremble_procStarR`), for `ε ∈ (0, ½]`.
* `miniR_d2At_qStar` — **`D2At` at every `ε ∈ (0, ½]`** for `procStarR ε` on `miniR`: both
  acts supported, both values `2/3` at the tremble. Inhabits `d2At_exists`'s conclusion over `ℝ`.
* `miniR_testSeq` — **`TestSeqTrembleEdtConsistent`** for `procR (2/3)` on `miniR` along
  `ε_n = 1/(n+2)`, `C_n = procStarR ε_n`. Inhabits `testSeq_exists`'s conclusion over `ℝ`, with a
  non-constant sequence of procedures.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpDutchBook

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-! ## Real labels on `Act2` -/

/-- The mixed action `(q, 1 − q)` on `Act2` over `ℝ` (the `ℝ` twin of `FinDistr.act2`).
Source: none: infrastructure
Kind: D -/
def act2R (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : FinDistr ℝ Act2 where
  w := fun | .a => q | .b => 1 - q
  nonneg := by intro x; cases x <;> simp <;> linarith
  sum_one := by rw [Act2.sum_univ]; simp

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem act2R_a (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : (act2R q h0 h1).w .a = q := rfl

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem act2R_b (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : (act2R q h0 h1).w .b = 1 - q := rfl

/-- The one-point real procedure `C(d) = (q, 1 − q)`. Source: none: infrastructure. Kind: D -/
def procR (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : Proc Unit (fun _ => Act2) ℝ :=
  fun _ => act2R q h0 h1

/-- `|Act2| = 2` in `ℝ`. Source: none: infrastructure. Kind: L -/
theorem act2_card_real : (Fintype.card Act2 : ℝ) = 2 := by
  rw [Fintype.card, Act2.univ_eq, Finset.card_pair (by decide)]; norm_num

/-! ## The cast miniature's masses and values at a real label -/

/-- `ν(live = a ∧ ⊤) = C(d)(a)` on the cast miniature, for every real procedure.
Source: `dp-calibration` `miniature_nu_live` (the `ℚ` statement); mandate T8(d)
Kind: L -/
theorem miniR_nu_live (C' : Proc Unit (fun _ => Act2) ℝ) (a : Act2) :
    nu C' miniR (miniActEv () a ∩ miniObs ()) = (C' ()).w a := by
  rw [miniObs, Finset.inter_univ, miniR_eq, nu_eq_sum, miniRx_sum]
  have := (C' ()).sum_one
  rw [Act2.sum_univ] at this
  cases a
  · simp [Act2.sum_univ, miniRx, miniActEv, leafLaw_decision, world_decision]
    linear_combination (C' ()).w Act2.a * this
  · simp [Act2.sum_univ, miniRx, miniActEv, leafLaw_decision, world_decision]
    linear_combination (C' ()).w Act2.b * this

/-- `𝔼[r · 1_{live = a}] = 2·C(d)(b)·C(d)(a)` on the cast miniature.
Source: `dp-calibration` `miniature_paySum_live_a`; mandate T8(d)
Kind: L -/
theorem miniR_paySum_live_a (C' : Proc Unit (fun _ => Act2) ℝ) :
    paySum C' miniR (miniActEv () .a ∩ miniObs ()) = 2 * (C' ()).w .b * (C' ()).w .a := by
  rw [miniObs, Finset.inter_univ, miniR_eq, paySum_eq_sum_ite, miniRx_sum]
  simp [Act2.sum_univ, miniRx, miniActEv, miniPay, leafLaw_decision, world_decision]
  ring

/-- `𝔼[r · 1_{live = b}] = C(d)(a)·C(d)(b)` on the cast miniature.
Source: `dp-calibration` `miniature_paySum_live_b`; mandate T8(d)
Kind: L -/
theorem miniR_paySum_live_b (C' : Proc Unit (fun _ => Act2) ℝ) :
    paySum C' miniR (miniActEv () .b ∩ miniObs ()) = (C' ()).w .a * (C' ()).w .b := by
  rw [miniObs, Finset.inter_univ, miniR_eq, paySum_eq_sum_ite, miniRx_sum]
  simp [Act2.sum_univ, miniRx, miniActEv, miniPay, leafLaw_decision, world_decision]

/-- **The strictly calibrated act values on the cast miniature at a full-support real label**:
`𝔼[r ∣ a ∧ ⊤] = 2·C(d)(b)`, `𝔼[r ∣ b ∧ ⊤] = C(d)(a)` (the `ℝ` twin of `dp-calibration`'s
`miniature_condExp`, for every procedure rather than `procQ q`).
Source: [[decision-problems-v2]] Remark 4.3 (`2(1 − q)`, `q`); mandate T8(d)
Kind: P
Fidelity: exact
Hyps: (a) both weights positive -/
theorem miniR_condExp (C' : Proc Unit (fun _ => Act2) ℝ) (ha : 0 < (C' ()).w .a)
    (hb : 0 < (C' ()).w .b) :
    condExp C' miniR (miniActEv () .a ∩ miniObs ()) = 2 * (C' ()).w .b ∧
    condExp C' miniR (miniActEv () .b ∩ miniObs ()) = (C' ()).w .a := by
  simp only [condExp, miniR_nu_live, miniR_paySum_live_a, miniR_paySum_live_b]
  constructor
  · rw [mul_div_assoc, div_self ha.ne', mul_one]
  · rw [mul_div_assoc, div_self hb.ne', mul_one]

/-! ## The nonstandard label `q*(ε)` over `ℝ` -/

/-- The miniature's label `q*(ε) = (4 − 3ε)/(6(1 − ε))` over `ℝ`: the label whose own
`ε`-tremble is exactly `2/3`.
Source: P07 I1′(ii) ("on Remark 4.3's miniature the unique such label … is
`m*(a) = (4−3ε)/(6(1−ε))`"); dp-sl-2-021; mandate T8(d)
Kind: D -/
noncomputable def qStarR (ε : ℝ) : ℝ := (4 - 3 * ε) / (6 * (1 - ε))

/-- `0 ≤ q*(ε)` for `ε ∈ [0, ½]`. Source: none: infrastructure. Kind: L -/
theorem qStarR_nonneg (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) : 0 ≤ qStarR ε := by
  unfold qStarR; apply div_nonneg <;> linarith

/-- `q*(ε) ≤ 1` for `ε ∈ [0, ½]`. Source: none: infrastructure. Kind: L -/
theorem qStarR_le_one (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) : qStarR ε ≤ 1 := by
  unfold qStarR; rw [div_le_one (by linarith)]; linarith

/-- `q*(ε) − 2/3 = ε/(6(1 − ε))`. Source: none: infrastructure. Kind: L -/
theorem qStarR_sub_two_thirds (ε : ℝ) (h1 : ε ≤ 1 / 2) :
    qStarR ε - 2 / 3 = ε / (6 * (1 - ε)) := by
  unfold qStarR
  have : (1 - ε) ≠ 0 := by linarith
  field_simp
  ring

/-- `|q*(ε) − 2/3| ≤ ε` for `ε ∈ [0, ½]`. Source: none: infrastructure. Kind: L -/
theorem abs_qStarR_sub_le (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) : |qStarR ε - 2 / 3| ≤ ε := by
  rw [qStarR_sub_two_thirds ε h1, abs_of_nonneg (div_nonneg h0 (by linarith))]
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- `2/3 ≤ q*(ε)` for `ε ∈ [0, ½]` (so both acts are supported). Source: none: infrastructure.
Kind: L -/
theorem two_thirds_le_qStarR (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) : 2 / 3 ≤ qStarR ε := by
  have := qStarR_sub_two_thirds ε h1
  have hd : 0 ≤ ε / (6 * (1 - ε)) := div_nonneg h0 (by linarith)
  linarith

/-- The procedure `procR (q* ε)`. Source: P07 I1′(ii); mandate T8(d). Kind: D -/
noncomputable def procStarR (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) : Proc Unit (fun _ => Act2) ℝ :=
  procR (qStarR ε) (qStarR_nonneg ε h0 h1) (qStarR_le_one ε h0 h1)

/-- **The tremble of `q*(ε)` at `ε` is exactly `2/3`** over `ℝ`, as procedures.
Source: P07 I1′(ii) ("with `(m*)^ε(a) = 2/3` exactly"); mandate T8(d)
Kind: P
Fidelity: exact -/
theorem tremble_procStarR (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) :
    tremble (procStarR ε h0.le h1) ε h0.le (by linarith) =
      procR (2 / 3) (by norm_num) (by norm_num) := by
  funext d
  apply FinDistr.ext'
  intro a
  have hne : (1 - ε) ≠ 0 := by linarith
  cases a <;> simp [tremble_w, procStarR, procR, qStarR, act2_card_real] <;> field_simp <;> ring

/-! ## The `ℝ` witnesses -/

/-- **The `ℝ` witness of `d2At_exists` (T8(d))**: on the cast miniature `procStarR ε` satisfies
`D2At` at every `ε ∈ (0, ½]` — its tremble is `procR (2/3)`, at which both act values are `2/3`
(`miniR_condExp`), so every supported act is a best reply; both acts are supported
(`q*(ε) ∈ [2/3, 5/6]`), so the comparison clause is exercised at each.
Source: P07 I1′(ii); `dp-calib-limits` `miniature_d2At_qStar` (the `ℚ` witness, cited in the
ledger before this file); audit round 1 adversarial §3.3; mandate T8(d)
Kind: N+
Fidelity: exact (the conclusion of `d2At_exists` at `B = miniR`, inhabited for every
`ε ∈ (0, ½]`)
Hyps: (a) `0 < ε ≤ ½` -/
theorem miniR_d2At_qStar (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) :
    D2At miniObs miniActEv miniR (procStarR ε h0.le h1) ε h0 (by linarith) := by
  intro d _ _ _ a _
  cases d
  rw [tremble_procStarR ε h0 h1]
  obtain ⟨hva, hvb⟩ := miniR_condExp (procR (2 / 3) (by norm_num) (by norm_num))
    (by norm_num [procR]) (by norm_num [procR])
  refine ⟨?_, fun b _ => ?_⟩
  · cases a <;> norm_num [miniR_nu_live, procR]
  · cases a <;> cases b <;> simp only [hva, hvb] <;> (try norm_num [procR])

/-- `1/(n+2) ≤ ½`. Source: none: infrastructure. Kind: L -/
theorem one_div_add_two_le_half_real (n : ℕ) : (1 : ℝ) / ((n : ℝ) + 2) ≤ 1 / 2 := by
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- The weights of `procStarR ε` are within `ε` of those of `procR (2/3)`, at both acts.
Source: none: infrastructure. Kind: L -/
theorem procStarR_w_sub_le (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) (a : Act2) :
    |(procStarR ε h0 h1 ()).w a - (procR (2 / 3) (by norm_num) (by norm_num) ()).w a| ≤ ε := by
  have habs := abs_qStarR_sub_le ε h0 h1
  cases a
  · simpa [procStarR, procR] using habs
  · simp only [procStarR, procR, act2R_b]
    rw [show (1 - qStarR ε) - (1 - 2 / 3) = -(qStarR ε - 2 / 3) by ring, abs_neg]
    exact habs

/-- **The `ℝ` witness of `testSeq_exists` (T8(d))**: on the cast miniature `procR (2/3)` is
test-sequence tremble-EDT-consistent along `ε_n = 1/(n+2)` with `C_n = procStarR ε_n` — a
non-constant sequence of procedures converging to `2/3`, each `D2At` at its own `ε_n`
(`miniR_d2At_qStar`). The miniature is the tree where D2 proper is empty (`dp-calibration`), so
this is the test-sequence form doing real work.
Source: P07 I1′(ii) ("`st(m*)` is test-sequence tremble-consistent along `ε_n = 1/n` with
`C_n := m*(1/n)`"); `dynamic.md` DY-3; `dp-calib-limits` `miniature_testSeq` (the `ℚ` witness);
audit round 1 adversarial §3.3; mandate T8(d)
Kind: N+
Fidelity: exact (`ε_n = 1/(n+2)` rather than `1/n`, to stay in `(0, ½]`)
Hyps: (a) none -/
theorem miniR_testSeq :
    TestSeqTrembleEdtConsistent miniObs miniActEv (procR (2 / 3) (by norm_num) (by norm_num))
      miniR := by
  refine ⟨fun n => 1 / ((n : ℝ) + 2),
    fun n => procStarR (1 / ((n : ℝ) + 2)) (epsSeq_mem n).1.le (one_div_add_two_le_half_real n),
    fun n => epsSeq_mem n, ?_, ?_,
    fun n => miniR_d2At_qStar _ (epsSeq_mem n).1 (one_div_add_two_le_half_real n)⟩
  · intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
    refine ⟨N, fun n hn => ?_⟩
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    show 1 / ((n : ℝ) + 2) < δ
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hN
    nlinarith
  · intro d a δ hδ
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
    refine ⟨N, fun n hn => ?_⟩
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hlt : 1 / ((n : ℝ) + 2) < δ := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hδ] at hN
      nlinarith
    cases d
    exact lt_of_le_of_lt
      (procStarR_w_sub_le _ (epsSeq_mem n).1.le (one_div_add_two_le_half_real n) a) hlt

end Cleanroom.Decision.DpDutchBook

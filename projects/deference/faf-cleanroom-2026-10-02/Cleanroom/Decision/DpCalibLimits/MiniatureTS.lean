import Cleanroom.Decision.DpCalibLimits.TwoRoute

/-!
# T3(c) — The miniature's test sequence: FF ⊊ TS on Remark 4.3's miniature

[[dp-calib-limits-mandate]] T3(c) (P07 I1′(ii) instance, dp-sl-2-021, S21).

The nonstandard label `q*(ε) = (4 − 3ε)/(6(1 − ε))` is exactly the label whose `ε`-tremble is
`2/3`: `tremble (procQ (q* ε)) ε = procQ (2/3)` as procedures (`tremble_procQStar`). At the
trembled procedure both act values on the miniature tie (`2(1 − 2/3) = 2/3`), so the D2
condition at `ε` holds for `procQ (q* ε)` at every `ε ∈ (0, ½]` (`miniature_d2At_qStar`), and
`C_n := procQ (q*(1/(n+2)))`, `ε_n := 1/(n+2)` is a test sequence for `procQ (2/3)`
(`miniature_testSeq`). With `miniature_not_eventTremble` (the constant sequence `2/3` is not a
test sequence — FF is empty on the miniature) this is **FF ⊊ TS on the miniature**
(`miniature_ff_strict_ts`): the first inhabitant of `TestSeqTrembleEdtConsistent` that is not
a constant sequence, on the tree where D2 is empty.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-- **The miniature's nonstandard label** `q*(ε) = (4 − 3ε)/(6(1 − ε))`: the unique label whose
own `ε`-tremble is an exact best reply on the miniature.
Source: P07 I1′(ii) ("on Remark 4.3's miniature the unique such label … is
`m*(a) = (4−3ε)/(6(1−ε))`"); dp-sl-2-021
Kind: D -/
def qStar (ε : ℚ) : ℚ := (4 - 3 * ε) / (6 * (1 - ε))

/-- `0 ≤ q*(ε)` for `ε ∈ [0, ½]`. Source: none: infrastructure. Kind: L -/
theorem qStar_nonneg (ε : ℚ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) : 0 ≤ qStar ε := by
  unfold qStar; apply div_nonneg <;> linarith

/-- `q*(ε) ≤ 1` for `ε ∈ [0, ½]`. Source: none: infrastructure. Kind: L -/
theorem qStar_le_one (ε : ℚ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) : qStar ε ≤ 1 := by
  unfold qStar; rw [div_le_one (by linarith)]; linarith

/-- `q*(ε) − 2/3 = ε/(6(1 − ε))`. Source: none: infrastructure. Kind: L -/
theorem qStar_sub_two_thirds (ε : ℚ) (h1 : ε ≤ 1 / 2) :
    qStar ε - 2 / 3 = ε / (6 * (1 - ε)) := by
  unfold qStar
  have : (1 - ε) ≠ 0 := by linarith
  field_simp
  ring

/-- `|q*(ε) − 2/3| ≤ ε` for `ε ∈ [0, ½]`. Source: none: infrastructure. Kind: L -/
theorem abs_qStar_sub_le (ε : ℚ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) : |qStar ε - 2 / 3| ≤ ε := by
  rw [qStar_sub_two_thirds ε h1, abs_of_nonneg (div_nonneg h0 (by linarith))]
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- The procedure `procQ (q* ε)`. Source: P07 I1′(ii). Kind: D -/
def procQStar (ε : ℚ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) : Proc Unit (fun _ => Act2) ℚ :=
  procQ (qStar ε) (qStar_nonneg ε h0 h1) (qStar_le_one ε h0 h1)

/-- **The tremble of `q*(ε)` at `ε` is exactly `2/3`**, as procedures (weights).
Source: P07 I1′(ii) ("with `(m*)^ε(a) = 2/3` exactly"); mandate T3(c)
Kind: P
Fidelity: exact -/
theorem tremble_procQStar (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) :
    tremble (procQStar ε h0.le h1) ε h0.le (by linarith) =
      procQ (2 / 3) (by norm_num) (by norm_num) := by
  funext d
  apply FinDistr.ext'
  intro a
  have hne : (1 - ε) ≠ 0 := by linarith
  cases a <;> simp [tremble_w, procQStar, procQ, qStar, act2_card_rat] <;> field_simp <;> ring

/-- **The D2 condition at `ε` for `procQ (q* ε)`** on the miniature: the trembled procedure is
`procQ (2/3)`, at which both act values tie, so every act is a best reply.
Source: P07 I1′(ii); mandate T3(c)
Kind: P
Fidelity: exact
Hyps: (a) `0 < ε ≤ ½` -/
theorem miniature_d2At_qStar (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) :
    D2At miniObs miniActEv miniature (procQStar ε h0.le h1) ε h0 (by linarith) := by
  intro d _ _ _ a _
  cases d
  rw [tremble_procQStar ε h0 h1]
  obtain ⟨hva, hvb⟩ := miniature_condExp (2 / 3) (by norm_num) (by norm_num)
  simp only [miniObs, Finset.inter_univ] at hva hvb ⊢
  refine ⟨?_, fun b _ => ?_⟩
  · cases a <;> simp [miniature_nu_live, procQ] <;> norm_num
  · cases a <;> cases b <;> simp only [hva, hvb] <;> norm_num

/-- `1/(n+2) ≤ ½`. Source: none: infrastructure. Kind: L -/
theorem one_div_add_two_le_half (n : ℕ) : (1 : ℚ) / ((n : ℚ) + 2) ≤ 1 / 2 := by
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith [(Nat.cast_nonneg n : (0 : ℚ) ≤ n)]

/-- `1/(n+2) → 0`. Source: none: infrastructure. Kind: L -/
theorem one_div_add_two_tendsto (δ : ℚ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, (1 : ℚ) / ((n : ℚ) + 2) < δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  refine ⟨N, fun n hn => ?_⟩
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hδ] at hN
  have hnN : (N : ℚ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- **The miniature's test sequence**: `ε_n = 1/(n+2)`, `C_n = procQ (q*(ε_n))` converge to
`0` and to `procQ (2/3)`, and the D2 condition holds along the sequence
(`miniature_d2At_qStar`). This inhabits DY-3 on the tree where D2 is empty — the first
`TestSeqTrembleEdtConsistent` witness that is not a constant sequence.
Source: P07 I1′(ii) ("then `st(m*)` is test-sequence tremble-consistent along `ε_n = 1/n`
with `C_n := m*(1/n)`"); `dynamic.md` DY-3; S21
Kind: N+
Fidelity: exact (`ε_n = 1/(n+2)` rather than `1/n`, to stay in `(0, ½]`)
Hyps: none -/
theorem miniature_testSeq :
    TestSeqTrembleEdtConsistent miniObs miniActEv (procQ (2 / 3) (by norm_num) (by norm_num))
      miniature := by
  refine ⟨fun n => 1 / ((n : ℚ) + 2),
    fun n => procQStar (1 / ((n : ℚ) + 2)) (by positivity) (one_div_add_two_le_half n),
    fun n => ⟨by positivity, by linarith [one_div_add_two_le_half n]⟩, ?_, ?_, ?_⟩
  · intro δ hδ
    exact one_div_add_two_tendsto δ hδ
  · intro d a δ hδ
    obtain ⟨N, hN⟩ := one_div_add_two_tendsto δ hδ
    refine ⟨N, fun n hn => ?_⟩
    have hb := abs_qStar_sub_le (1 / ((n : ℚ) + 2)) (by positivity) (one_div_add_two_le_half n)
    have hlt := hN n hn
    cases a
    · simp only [procQStar, procQ, FinDistr.act2_a]
      linarith
    · simp only [procQStar, procQ, FinDistr.act2_b]
      rw [show (1 : ℚ) - qStar (1 / ((n : ℚ) + 2)) - (1 - 2 / 3) =
        -(qStar (1 / ((n : ℚ) + 2)) - 2 / 3) by ring, abs_neg]
      linarith
  · intro n
    exact miniature_d2At_qStar _ (by positivity) (one_div_add_two_le_half n)

/-- **FF ⊊ TS on the miniature**: `procQ (2/3)` is not fixed-form tremble-EDT-consistent (the
constant sequence `2/3` is not a test sequence, `miniature_not_eventTremble`) but is
test-sequence tremble-EDT-consistent.
Source: SL-21 ("the first inclusion strict on Remark 4.3's miniature (the fixed form is empty
there)"); P07 I1′(ii); dp-sl-005
Kind: N+
Fidelity: exact
Hyps: none -/
theorem miniature_ff_strict_ts :
    ¬ FF miniObs miniActEv (procQ (2 / 3) (by norm_num) (by norm_num)) miniature ∧
    TS miniObs miniActEv (procQ (2 / 3) (by norm_num) (by norm_num)) miniature :=
  ⟨miniature_not_eventTremble _ _ _, miniature_testSeq⟩

end Cleanroom.Decision.DpCalibLimits

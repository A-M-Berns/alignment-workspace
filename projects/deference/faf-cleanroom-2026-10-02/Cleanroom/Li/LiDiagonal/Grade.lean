import Cleanroom.Li.LiDiagonal.Deferred
import LogicalInduction.Framework.Machine.ThresholdMachine
import LogicalInduction.Properties.ExpectationAffine

/-!
# `li-diagonal` · Grade: the N+ product side of soft self-trust on the deferred liar (T5f)

The first formalizer left T5f's N+ grading half-done: at `p' + δ < p` the confidence factor's
expectation tends to `1` (`confidence_expect_tendsto_one`, `Deferred.lean`), but the product
side `𝔼_n(A_n) → p` needed a lemma FAF lacks — two LUV families whose completed-world values
eventually agree have asymptotically equal expectations. That lemma is
`expect_asympEq_of_eventually_values_close` below: `def-self-trust`'s tail trick
(`expect_asympEq_zero_of_eventually_abs_le`) on the constant combination `A_n − Y_n`
(`constComb 0 [(1, A), (-1, Y)]`). With `Y_n := 𝟙χ_n` and `thm:ei` (`lic_expectation_indicator`)
this gives `product_expect_tendsto_p : 𝔼_n(A_n) ≈ₙ p`, and `soft_self_trust_nondegenerate`
records the N+ certificate: both sides of `thm:st` have positive limits `p` and `p'` with
`p' < p` — the instance holds with slack, not degenerately.

Scope: single-market; threshold `p`, deferral `f`; `defDiag` of FAF's Kleene diagonal. The
paper-market instance is in `Paper.lean` (`paper_product_expect_tendsto`).
-/

namespace Cleanroom.Li.LiDiagonal

open LogicalInduction LO.Propositional Cleanroom.Found.LiAsympCalc Cleanroom.Deference.DefSelfTrust
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open Filter Topology

/-! ### The two-LUV difference as a constant combination -/

/-- Value of the pair combination `A_n − Y_n` at an assignment `ν`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma constComb_pair_value (P : History) (A Y : ℕ → LUV) (n : ℕ) (ν : LUV → ℝ) :
    (constComb 0 [(1, A), (-1, Y)] n).value P ν = ν (A n) - ν (Y n) := by
  rw [constComb_value]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

/-- Diagonal expectation of the pair combination `A_n − Y_n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma constComb_pair_expect (P : History) (A Y : ℕ → LUV) (n : ℕ) :
    (constComb 0 [(1, A), (-1, Y)] n).expect P n = (A n).expect P n - (Y n).expect P n := by
  rw [constComb_expect]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

/-- `L¹` norm of the pair combination is `2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma constComb_pair_l1Norm (P : History) (A Y : ℕ → LUV) (n : ℕ) :
    (constComb 0 [(1, A), (-1, Y)] n).l1Norm P ≤ 2 := by
  rw [constComb_l1Norm]
  norm_num

/-- **Two LUV families whose completed-world values eventually agree have asymptotically equal
diagonal expectations.** The "same determined value ⟹ same expectation" lemma, at a
world-dependent value (the values may be payouts): `def-self-trust`'s tail trick on the pair
combination `A_n − Y_n`. FAF API request (K9's family): FAF's expectation provability induction
needs a constant determined value.
Scope: single-market.
Source: none: infrastructure ([[li-diagonal-mandate]] T5f; LI paper `thm:expprovind`)
Kind: C
Fidelity: n/a
Hyps: (a) none -/
theorem expect_asympEq_of_eventually_values_close (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (A Y : ℕ → LUV) (hA : LUV.MachineThresholdCodeSeq A)
    (hY : LUV.MachineThresholdCodeSeq Y) (α β : ℕ → PCWorld → ℝ)
    (hAval : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → v.ValuesAt (A n) (α n v))
    (hYval : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → v.ValuesAt (Y n) (β n v))
    (hclose : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      |α n v - β n v| ≤ ε)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (A n).expect P n) ≈ₙ fun n => (Y n).expect P n := by
  classical
  have hmem : ∀ q ∈ [((1 : ℚ), A), ((-1 : ℚ), Y)], LUV.MachineThresholdCodeSeq q.2 := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hA
    · exact hY
  have hwv : LUVCombination.WorldValued (constComb 0 [(1, A), (-1, Y)]) DP := by
    intro n v hv
    refine ⟨fun X => if X = A n then α n v else β n v, ?_⟩
    intro q hq
    simp only [constComb, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · simp only [if_true]
      exact hAval n v hv
    · by_cases hAY : Y n = A n
      · simp only [hAY, if_true]
        exact hAval n v hv
      · simp only [hAY, if_false]
        exact hYval n v hv
  have hval : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      ∀ ν, (constComb 0 [(1, A), (-1, Y)] n).ValuesAt v ν →
        |(constComb 0 [(1, A), (-1, Y)] n).value P ν| ≤ ε := by
    intro ε hε
    filter_upwards [hclose ε hε] with n hn v hv ν hν
    have hνA : ν (A n) = α n v := by
      have h := hν (EF.const 1, A n) (by simp [constComb])
      exact h.eq (hAval n v hv)
    have hνY : ν (Y n) = β n v := by
      have h := hν (EF.const (-1), Y n) (by simp [constComb])
      exact h.eq (hYval n v hv)
    rw [constComb_pair_value, hνA, hνY]
    exact hn v hv
  have hzero := expect_asympEq_zero_of_eventually_abs_le (P := P) (DP := DP)
    (constCombSyntax 0 [(1, A), (-1, Y)] hmem) (B := 2) (constComb_pair_l1Norm P A Y) hwv hval
    hworld
  have heq : (fun n => (constComb 0 [(1, A), (-1, Y)] n).expect P n) =
      fun n => (A n).expect P n - (Y n).expect P n := by
    funext n; exact constComb_pair_expect P A Y n
  rw [heq] at hzero
  unfold AsympEq at hzero ⊢
  simpa using hzero

/-! ### T5f's N+ product side -/

section SelfTrustGrade

variable {DP : DeductiveProcess} {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T]
  (Q : QuotationTheoryPresentation DP T) (P : History) [IsLogicalInductor P DP]
  (market : MarketComputation P) (p : ℚ) (f : DeferralFunction)

include Q

/-- **T5f, the N+ product side.** At `p' + δ < p` the quoted confidence factor is eventually
`1`, so the product LUV `A_n` (valued at `payout(χ_n) · Ind_δ(P_{f(n)}(χ_n) > p')` in every
completed world) is eventually valued like the indicator `𝟙χ_n`; hence `𝔼_n(A_n) ≈ₙ 𝔼_n(𝟙χ_n)`
(`expect_asympEq_of_eventually_values_close`) `≈ₙ P_n(χ_n)` (`thm:ei`) `≈ₙ p` (T5c, taken as the
hypothesis `hpres`, which `defDiag_present_price_of_quote` derives).
Scope: single-market; threshold `p`, deferral `f`; `defDiag` of FAF's Kleene diagonal.
Source: [[trust-lab-inventory]] 024; [[li-diagonal-mandate]] T5f
Kind: C
Fidelity: exact
Hyps: (a) `hA`, `hArefl` (the `thm:st` package's product fields; discharged over the paper market in `Paper.lean`), `hχ` (K9), `hpres` (T5c's conclusion, derived in `Deferred.lean`) -/
theorem product_expect_tendsto_p (hp0 : 0 < p) (hp1 : p < 1) (δ p' : ℚ) (hδ : 0 < δ)
    (hlt : p' + δ < p) (A : ℕ → LUV)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hA : LUV.MachineThresholdCodeSeq A)
    (hArefl : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (A n) (v.payout (defDiag (kleeneDiag T market p) f n) *
        ctsInd δ (P (f n) (defDiag (kleeneDiag T market p) f n)) (p' : ℝ)))
    (hχ : MachineSentenceCodes (defDiag (kleeneDiag T market p) f))
    (hpres : (fun n => P n (defDiag (kleeneDiag T market p) f n)) ≈ₙ fun _ => (p : ℝ)) :
    (fun n => (A n).expect P n) ≈ₙ fun _ => (p : ℝ) := by
  have hfut := defDiag_future_price_tendsto Q P market p f hp0 hp1 hworld
  have hev : ∀ᶠ n in atTop,
      ctsInd δ (P (f n) (defDiag (kleeneDiag T market p) f n)) (p' : ℝ) = 1 := by
    have hgap : (p' : ℝ) + δ < p := by exact_mod_cast hlt
    filter_upwards [hfut.eventually (Ioi_mem_nhds hgap)] with n hn
    have hn' : (p' : ℝ) + δ < P (f n) (defDiag (kleeneDiag T market p) f n) := hn
    exact ctsInd_eq_one_of_le_sub δ _ _ hδ (by linarith)
  have h1 := expect_asympEq_of_eventually_values_close P DP A
    (fun n => LUV.indicatorOf (defDiag (kleeneDiag T market p) f n)) hA
    (LUV.indicatorOf_machineThresholdCodeSeq hχ)
    (fun n v => v.payout (defDiag (kleeneDiag T market p) f n) *
      ctsInd δ (P (f n) (defDiag (kleeneDiag T market p) f n)) (p' : ℝ))
    (fun n v => v.payout (defDiag (kleeneDiag T market p) f n))
    hArefl
    (fun n v hv => (LUV.indicatorOf_isIndicator (defDiag (kleeneDiag T market p) f n) DP).valuesAt hv)
    (fun ε hε => by
      filter_upwards [hev] with n hn v hv
      rw [hn, mul_one, _root_.sub_self, abs_zero]
      exact hε.le)
    hworld
  have h2 := lic_expectation_indicator P DP (defDiag (kleeneDiag T market p) f) hχ
    (fun n => LUV.indicatorOf (defDiag (kleeneDiag T market p) f n))
    (LUV.indicatorOf_machineThresholdCodeSeq hχ) hworld
    (fun n => LUV.indicatorOf_isIndicator (defDiag (kleeneDiag T market p) f n) DP)
  exact h1.trans (h2.trans hpres)

/-- **T5f graded N+.** At `0 < p'` and `p' + δ < p`, both sides of `thm:st`'s instance on the
deferred liar have positive limits: `𝔼_n(A_n) → p` and `p' · 𝔼_n(B_n) → p'`, with `p' < p`. The
inequality `𝔼_n(A_n) ≳ₙ p' · 𝔼_n(B_n)` therefore holds with slack `p − p' > 0`, not degenerately
(contrast `p' = p`, where both sides `→ 0`: `product_expect_tendsto_zero`).
Scope: single-market; threshold `p`, deferral `f`.
Source: [[trust-lab-inventory]] 024; [[li-diagonal-mandate]] T5f ("at `p' = ¼` both sides have positive limits")
Kind: N+
Fidelity: exact
Hyps: (a) as in `product_expect_tendsto_p` and `confidence_expect_tendsto_one` -/
theorem soft_self_trust_nondegenerate (hp0 : 0 < p) (hp1 : p < 1) (δ p' : ℚ) (hδ : 0 < δ)
    (hp'0 : 0 < p') (hlt : p' + δ < p) (A B : ℕ → LUV)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hA : LUV.MachineThresholdCodeSeq A)
    (hArefl : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (A n) (v.payout (defDiag (kleeneDiag T market p) f n) *
        ctsInd δ (P (f n) (defDiag (kleeneDiag T market p) f n)) (p' : ℝ)))
    (hB : LUV.MachineThresholdCodeSeq B)
    (hBrefl : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (B n) (ctsInd δ (P (f n) (defDiag (kleeneDiag T market p) f n)) (p' : ℝ)))
    (hχ : MachineSentenceCodes (defDiag (kleeneDiag T market p) f))
    (hpres : (fun n => P n (defDiag (kleeneDiag T market p) f n)) ≈ₙ fun _ => (p : ℝ)) :
    Tendsto (fun n => (A n).expect P n) atTop (𝓝 (p : ℝ)) ∧
      Tendsto (fun n => (p' : ℝ) * (B n).expect P n) atTop (𝓝 (p' : ℝ)) ∧
      (0 : ℝ) < p' ∧ (p' : ℝ) < p := by
  have hAlim := product_expect_tendsto_p Q P market p f hp0 hp1 δ p' hδ hlt A hworld hA hArefl hχ
    hpres
  have hBlim := confidence_expect_tendsto_one Q P market p f hp0 hp1 δ p' hδ hlt B hworld hB hBrefl
  unfold AsympEq at hAlim hBlim
  refine ⟨by simpa using hAlim.add_const (p : ℝ), ?_, by exact_mod_cast hp'0, ?_⟩
  · have hB1 : Tendsto (fun n => (B n).expect P n) atTop (𝓝 1) := by
      simpa using hBlim.add_const (1 : ℝ)
    simpa using hB1.const_mul (p' : ℝ)
  · have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
    have : (p' : ℝ) + δ < p := by exact_mod_cast hlt
    linarith

end SelfTrustGrade

end Cleanroom.Li.LiDiagonal

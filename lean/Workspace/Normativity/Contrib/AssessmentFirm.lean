/-
# The live-world TradingFirm, dominance, and `LIC_L`

The source's TradingFirm depends on its deductive process at exactly one place:
the `Budgeter` it mixes.  Weights, cutoffs, the `ℓ¹` strategy bounds, the gate and
the trader enumeration mention no worlds at all and are reused verbatim from the
pinned dependency.

Replacing the Budgeter by the assessment-process Budgeter of
`Contrib.AssessmentProcess` therefore yields dominance over any assessment
process, and the source's MarketMaker lemma — whose upper bound is uniform over
*all* propositionally consistent worlds, plausible or not — supplies the other
half with no hypothesis.  Composing them gives `LIC_L` for the recursive market.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.AssessmentProcess

namespace Workspace.Normativity.Contrib.AssessmentFirm

open LogicalInduction
open Workspace.Normativity.Contrib.AssessmentProcess

/-! ## Exploitation transfers under a uniform net-worth difference -/

theorem exploits_of_boundedDifference {L : Assessment} {Tr Tr' : Trader}
    {P P' : History} (h : L.Exploits Tr P) (C : ℝ)
    (hdiff : ∀ n v, L.Live n v → |Tr.netWorth P v n - Tr'.netWorth P' v n| ≤ C) :
    L.Exploits Tr' P' := by
  rcases h with ⟨⟨lo, hlo⟩, hnotAbove⟩
  refine ⟨⟨lo - C, ?_⟩, ?_⟩
  · rintro x ⟨n, v, hv, rfl⟩
    have hbase := hlo ⟨n, v, hv, rfl⟩
    have herr := hdiff n v hv
    rw [abs_le] at herr
    linarith
  · intro hUpper
    apply hnotAbove
    rcases hUpper with ⟨U, hU⟩
    refine ⟨U + C, ?_⟩
    rintro x ⟨n, v, hv, rfl⟩
    have hbase := hU ⟨n, v, hv, rfl⟩
    have herr := hdiff n v hv
    rw [abs_le] at herr
    linarith

/-- Gating a trader preserves exploitation: the two differ by a fixed finite
prefix, uniformly over worlds. -/
theorem exploits_gate {L : Assessment} (Tr : Trader) (P : History)
    (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1)
    (hEx : L.Exploits Tr P) (start : ℕ) :
    L.Exploits (Tr.gate start) P := by
  apply exploits_of_boundedDifference hEx
    ((∑ i ∈ Finset.range start, (Tr.strat i).absBound : ℚ) : ℝ)
  intro n v _
  exact Tr.gate_netWorth_difference_le P hP start v n

/-! ## The firm

Only `BudgeterAt` changes; the weights, cutoff and enumeration are the source's. -/

/-- The finite list of explicitly retained positive-budget components. -/
def budgetComponents (L : Assessment) (Q : ℕ → Sentence → ℚ)
    (n j : ℕ) : List (Strategy n) :=
  (List.range (tradingFirmCutoff n)).map fun r =>
    (AssessmentProcess.BudgeterAt L (firmRawTrader j) (r + 1) Q n).scaleConst
      (tradingFirmWeight j (r + 1))

/-- One enumerated trader's exact finite day contribution. -/
def componentAt (L : Assessment) (Q : ℕ → Sentence → ℚ)
    (n j : ℕ) : Strategy n :=
  Strategy.join (budgetComponents L Q n j ++
    [((firmRawTrader j).strat n).scaleConst
      (tradingFirmWeight j (tradingFirmCutoff n))])

/-- `def:tradingfirm` over an assessment process. -/
def TradingFirmAt (L : Assessment) (Q : ℕ → Sentence → ℚ)
    (n : ℕ) : Strategy n :=
  Strategy.join ((List.range (n + 1)).map fun j => componentAt L Q n j)

/-- Static realization against a supplied complete rational market table. -/
def tradingFirmTrader (L : Assessment) (Q : ℕ → Sentence → ℚ) :
    Trader where
  strat n := TradingFirmAt L Q n

/-- One gated enumeration index's contribution to the realized firm. -/
def componentTrader (L : Assessment) (Q : ℕ → Sentence → ℚ)
    (j : ℕ) : Trader where
  strat n := if j ≤ n then componentAt L Q n j else Trader.zero.strat n

/-- Adaptive form consumed by the recursive construction. -/
def TradingFirm (L : Assessment) : AdaptiveTrader where
  action n past := TradingFirmAt L (rationalHistory past) n

lemma budgetComponents_eq_of_eq_prefix (L : Assessment) (Q R : ℕ → Sentence → ℚ)
    (n j : ℕ) (hQR : ∀ day, day < n → ∀ φ, Q day φ = R day φ) :
    budgetComponents L Q n j = budgetComponents L R n j := by
  unfold budgetComponents
  apply List.map_congr_left
  intro r _
  rw [AssessmentProcess.BudgeterAt_eq_of_eq_prefix L (firmRawTrader j) (r + 1) Q R n hQR]

lemma componentAt_eq_of_eq_prefix (L : Assessment) (Q R : ℕ → Sentence → ℚ)
    (n j : ℕ) (hQR : ∀ day, day < n → ∀ φ, Q day φ = R day φ) :
    componentAt L Q n j = componentAt L R n j := by
  unfold componentAt
  rw [budgetComponents_eq_of_eq_prefix L Q R n j hQR]

lemma TradingFirmAt_eq_of_eq_prefix (L : Assessment) (Q R : ℕ → Sentence → ℚ)
    (n : ℕ) (hQR : ∀ day, day < n → ∀ φ, Q day φ = R day φ) :
    TradingFirmAt L Q n = TradingFirmAt L R n := by
  unfold TradingFirmAt
  apply congrArg Strategy.join
  apply List.map_congr_left
  intro j _
  exact componentAt_eq_of_eq_prefix L Q R n j hQR

lemma TradingFirmAt_value_eq_sum (L : Assessment) (Q : ℕ → Sentence → ℚ) (n : ℕ)
    (P : History) (w : Sentence → ℝ) :
    (TradingFirmAt L Q n).value P w =
      ∑ j ∈ Finset.range (n + 1), (componentAt L Q n j).value P w := by
  rw [TradingFirmAt, Strategy.join_value]
  simp only [List.map_map, Function.comp_def]
  congr 1

lemma tradingFirmTrader_netWorth_eq_component_sum (L : Assessment)
    (Q : ℕ → Sentence → ℚ) (P : History) (v : PCWorld) (n : ℕ) :
    (tradingFirmTrader L Q).netWorth P v n =
      ∑ j ∈ Finset.range (n + 1), (componentTrader L Q j).netWorth P v n := by
  unfold Trader.netWorth
  change (∑ d ∈ Finset.range (n + 1), (TradingFirmAt L Q d).value P v.payout) = _
  simp_rw [TradingFirmAt_value_eq_sum]
  calc
    (∑ d ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (d + 1),
        (componentAt L Q d j).value P v.payout) =
        ∑ d ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          if j ≤ d then (componentAt L Q d j).value P v.payout else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdn : d ≤ n := by simp only [Finset.mem_range] at hd; omega
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext j
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      · intro j hj
        simp only [Finset.mem_filter] at hj
        simp
    _ = ∑ j ∈ Finset.range (n + 1), ∑ d ∈ Finset.range (n + 1),
          if j ≤ d then (componentAt L Q d j).value P v.payout else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range (n + 1), (componentTrader L Q j).netWorth P v n := by
      apply Finset.sum_congr rfl
      intro j _
      unfold Trader.netWorth
      apply Finset.sum_congr rfl
      intro d _
      by_cases hjd : j ≤ d
      · simp [componentTrader, hjd]
      · simp [componentTrader, hjd, Trader.zero, Strategy.value]

/-! ## Above the cutoff the budget never binds -/

lemma BudgeterAt_firmRaw_value_eq_of_cutoff (L : Assessment) (P : History)
    (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1) (Q : ℕ → Sentence → ℚ) (n j b : ℕ)
    (hQ : ∀ day, day < n → ∀ φ, P day φ = (Q day φ : ℝ))
    (hj : j ≤ n) (hb : tradingFirmCutoff n < b) (w : Sentence → ℝ) :
    (AssessmentProcess.BudgeterAt L (firmRawTrader j) b Q n).value P w =
      ((firmRawTrader j).strat n).value P w := by
  apply AssessmentProcess.BudgeterAt_value_eq_of_safe L (firmRawTrader j) b (by omega)
    P Q n hQ
  intro m hm v _
  have habs := firmRaw_netWorth_abs_lt_cutoff P hP hj hm v
  have hbR : (tradingFirmCutoff n : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hlow := neg_abs_le ((firmRawTrader j).netWorth P v m)
  linarith

lemma BudgeterAt_firmRaw_value_eq_zero_of_lt (L : Assessment) (P : History)
    (Q : ℕ → Sentence → ℚ) (n j b : ℕ) (hb : 0 < b) (hnj : n < j)
    (hQ : ∀ day, day < n → ∀ φ, P day φ = (Q day φ : ℝ)) (w : Sentence → ℝ) :
    (AssessmentProcess.BudgeterAt L (firmRawTrader j) b Q n).value P w = 0 := by
  rw [AssessmentProcess.BudgeterAt_value_eq_of_safe L (firmRawTrader j) b hb P Q n hQ]
  · rw [firmRawTrader, Trader.gate_strat_of_lt (enumeratedTrader j) hnj]
    simp [Trader.zero, Strategy.value]
  · intro m hm v _
    rw [firmRaw_netWorth_eq_zero_of_lt P v (by omega)]
    exact_mod_cast (neg_neg_of_pos (by exact_mod_cast hb) : -(b : ℝ) < 0)

lemma componentAt_value_hasSum (L : Assessment) (P : History)
    (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1) (Q : ℕ → Sentence → ℚ) (n j : ℕ)
    (hQ : ∀ day, day < n → ∀ φ, P day φ = (Q day φ : ℝ)) (hj : j ≤ n)
    (w : Sentence → ℝ) :
    HasSum (fun r : ℕ =>
      (tradingFirmWeight j (r + 1) : ℝ) *
        (AssessmentProcess.BudgeterAt L (firmRawTrader j) (r + 1) Q n).value P w)
      ((componentAt L Q n j).value P w) := by
  set C := tradingFirmCutoff n with hC
  set raw := ((firmRawTrader j).strat n).value P w with hraw0
  have hweights := tradingFirmWeight_tail_hasSum j C
  have hraw : HasSum (fun r : ℕ => (tradingFirmWeight j (C + 1 + r) : ℝ) * raw)
      ((tradingFirmWeight j C : ℝ) * raw) := by
    convert hweights.mul_left raw using 1 <;> first | rfl | simp [mul_comm]
  have hbudget : HasSum (fun r : ℕ =>
      (tradingFirmWeight j (C + 1 + r) : ℝ) *
        (AssessmentProcess.BudgeterAt L (firmRawTrader j) (C + 1 + r) Q n).value P w)
      ((tradingFirmWeight j C : ℝ) * raw) := by
    convert hraw using 1
    funext r
    rw [BudgeterAt_firmRaw_value_eq_of_cutoff L P hP Q n j (C + 1 + r)
      hQ hj (by omega) w]
  set f : ℕ → ℝ := fun r =>
    (tradingFirmWeight j (r + 1) : ℝ) *
      (AssessmentProcess.BudgeterAt L (firmRawTrader j) (r + 1) Q n).value P w with hf
  have htail : HasSum (fun r => f (r + C)) ((tradingFirmWeight j C : ℝ) * raw) := by
    first
      | exact hbudget
      | simpa only [hf, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbudget
  have hfull := (hasSum_nat_add_iff C).mp htail
  convert hfull using 1
  any_goals rfl
  simp only [componentAt, Strategy.join_value, budgetComponents, List.map_append,
    List.sum_append, List.map_map, Function.comp_def, Strategy.scaleConst_value,
    List.map_singleton, List.sum_cons, List.sum_nil, add_zero, hf, hraw0, hC]
  rw [add_comm]
  change (tradingFirmWeight j C : ℝ) * raw + ((List.range C).map f).sum =
    (tradingFirmWeight j C : ℝ) * raw + ∑ x ∈ Finset.range C, f x
  congr 1

lemma componentTrader_netWorth_hasSum (L : Assessment) (P : History)
    (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day φ, P day φ = (Q day φ : ℝ)) (j n : ℕ) (v : PCWorld) :
    HasSum (fun r : ℕ =>
      (tradingFirmWeight j (r + 1) : ℝ) *
        (AssessmentProcess.budgetedTrader L (firmRawTrader j) (r + 1) Q).netWorth P v n)
      ((componentTrader L Q j).netWorth P v n) := by
  have hday : ∀ d ∈ Finset.range (n + 1), HasSum (fun r : ℕ =>
      (tradingFirmWeight j (r + 1) : ℝ) *
        (AssessmentProcess.BudgeterAt L (firmRawTrader j) (r + 1) Q d).value P v.payout)
      (((componentTrader L Q j).strat d).value P v.payout) := by
    intro d _
    by_cases hjd : j ≤ d
    · simpa [componentTrader, hjd] using
        componentAt_value_hasSum L P hP Q d j (fun day _ φ => hQ day φ) hjd v.payout
    · have hdj : d < j := Nat.lt_of_not_ge hjd
      have hz : ∀ r : ℕ,
          (AssessmentProcess.BudgeterAt L (firmRawTrader j) (r + 1) Q d).value
            P v.payout = 0 := by
        intro r
        exact BudgeterAt_firmRaw_value_eq_zero_of_lt L P Q d j (r + 1)
          (by omega) hdj (fun day _ φ => hQ day φ) v.payout
      convert (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0) using 1
      · funext r
        rw [hz r]
        simp
      · simp [componentTrader, hjd, Trader.zero, Strategy.value]
  have hs := hasSum_sum hday
  convert hs using 1
  any_goals rfl
  · funext r
    unfold Trader.netWorth AssessmentProcess.budgetedTrader
    rw [Finset.mul_sum]

/-! ## Floors -/

lemma componentTrader_netWorth_floor (L : Assessment) (P : History)
    (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day φ, P day φ = (Q day φ : ℝ)) (j n : ℕ) (v : PCWorld)
    (hv : L.Live n v) :
    -((1 / 2 : ℝ) ^ j) ≤ (componentTrader L Q j).netWorth P v n := by
  have hactual := componentTrader_netWorth_hasSum L P hP Q hQ j n v
  have hcost := tradingFirmBudgetCost_hasSum j
  have hnonneg : ∀ r : ℕ, 0 ≤
      (tradingFirmWeight j (r + 1) : ℝ) *
          (AssessmentProcess.budgetedTrader L (firmRawTrader j) (r + 1) Q).netWorth
            P v n +
        (tradingFirmWeight j (r + 1) : ℝ) * (r + 1 : ℝ) := by
    intro r
    have hfloor := AssessmentProcess.budgetedTrader_netWorth_floor L
      (firmRawTrader j) (r + 1) (by omega) P Q hQ n v hv
    have hw0 : 0 ≤ (tradingFirmWeight j (r + 1) : ℝ) := by
      exact_mod_cast (tradingFirmWeight_pos j (r + 1)).le
    have hm := mul_le_mul_of_nonneg_left hfloor hw0
    push_cast at hm
    calc
      0 = (tradingFirmWeight j (r + 1) : ℝ) * (-(r + 1 : ℝ)) +
          (tradingFirmWeight j (r + 1) : ℝ) * (r + 1 : ℝ) := by ring
      _ ≤ _ := add_le_add hm le_rfl
  have hsum0 := (hactual.add hcost).nonneg hnonneg
  linarith

/-- The whole firm has the paper's uniform downside bound `-2`. -/
lemma tradingFirmTrader_netWorth_floor (L : Assessment) (P : History)
    (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day φ, P day φ = (Q day φ : ℝ)) (n : ℕ) (v : PCWorld)
    (hv : L.Live n v) :
    -2 ≤ (tradingFirmTrader L Q).netWorth P v n := by
  rw [tradingFirmTrader_netWorth_eq_component_sum]
  have hsum := finite_half_pow_sum_lt_two n
  calc
    (-2 : ℝ) ≤ -(∑ j ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ j) := by linarith
    _ = ∑ j ∈ Finset.range (n + 1), -((1 / 2 : ℝ) ^ j) := by
      rw [Finset.sum_neg_distrib]
    _ ≤ ∑ j ∈ Finset.range (n + 1), (componentTrader L Q j).netWorth P v n :=
      Finset.sum_le_sum (fun j _ => componentTrader_netWorth_floor L P hP Q hQ j n v hv)

lemma componentTrader_residual_floor (L : Assessment) (P : History)
    (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day φ, P day φ = (Q day φ : ℝ)) (j r n : ℕ) (v : PCWorld)
    (hv : L.Live n v) :
    -((1 / 2 : ℝ) ^ j) ≤ (componentTrader L Q j).netWorth P v n -
      (tradingFirmWeight j (r + 1) : ℝ) *
        (AssessmentProcess.budgetedTrader L (firmRawTrader j) (r + 1) Q).netWorth
          P v n := by
  let actual : ℕ → ℝ := fun s =>
    (tradingFirmWeight j (s + 1) : ℝ) *
      (AssessmentProcess.budgetedTrader L (firmRawTrader j) (s + 1) Q).netWorth P v n
  let cost : ℕ → ℝ := fun s => (tradingFirmWeight j (s + 1) : ℝ) * (s + 1 : ℝ)
  have ha : HasSum actual ((componentTrader L Q j).netWorth P v n) :=
    componentTrader_netWorth_hasSum L P hP Q hQ j n v
  have hc : HasSum cost ((1 / 2 : ℝ) ^ j) := tradingFirmBudgetCost_hasSum j
  have har := ha.update r 0
  have hcr := hc.update r 0
  have hnonneg : ∀ s, 0 ≤ Function.update actual r 0 s + Function.update cost r 0 s := by
    intro s
    by_cases hsr : s = r
    · subst s; simp
    · simp only [Function.update, hsr]
      have hfloor := AssessmentProcess.budgetedTrader_netWorth_floor L
        (firmRawTrader j) (s + 1) (by omega) P Q hQ n v hv
      have hw0 : 0 ≤ (tradingFirmWeight j (s + 1) : ℝ) := by
        exact_mod_cast (tradingFirmWeight_pos j (s + 1)).le
      have hm := mul_le_mul_of_nonneg_left hfloor hw0
      push_cast at hm
      dsimp only [actual, cost]
      calc
        0 = (tradingFirmWeight j (s + 1) : ℝ) * (-(s + 1 : ℝ)) +
            (tradingFirmWeight j (s + 1) : ℝ) * (s + 1 : ℝ) := by ring
        _ ≤ _ := add_le_add hm le_rfl
  have hsum0 := (har.add hcr).nonneg hnonneg
  have hcost0 : 0 ≤ cost r := by
    dsimp only [cost]
    apply mul_nonneg
    · exact_mod_cast (tradingFirmWeight_pos j (r + 1)).le
    · positivity
  dsimp only [actual, cost] at hsum0 ⊢
  linarith

lemma budgetedFirmRaw_netWorth_eq_zero_of_lt (L : Assessment) (P : History)
    (Q : ℕ → Sentence → ℚ) (hQ : ∀ day φ, P day φ = (Q day φ : ℝ))
    (j b n : ℕ) (hb : 0 < b) (hnj : n < j) (v : PCWorld) :
    (AssessmentProcess.budgetedTrader L (firmRawTrader j) b Q).netWorth P v n = 0 := by
  unfold Trader.netWorth AssessmentProcess.budgetedTrader
  apply Finset.sum_eq_zero
  intro d hd
  have hdj : d < j := by simp only [Finset.mem_range] at hd; omega
  exact BudgeterAt_firmRaw_value_eq_zero_of_lt L P Q d j b hb hdj
    (fun day _ φ => hQ day φ) v.payout

lemma tradingFirmTrader_residual_floor (L : Assessment) (P : History)
    (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day φ, P day φ = (Q day φ : ℝ)) (j r n : ℕ) (v : PCWorld)
    (hv : L.Live n v) :
    -2 ≤ (tradingFirmTrader L Q).netWorth P v n -
      (tradingFirmWeight j (r + 1) : ℝ) *
        (AssessmentProcess.budgetedTrader L (firmRawTrader j) (r + 1) Q).netWorth
          P v n := by
  by_cases hjn : j ≤ n
  · rw [tradingFirmTrader_netWorth_eq_component_sum]
    have hjS : j ∈ Finset.range (n + 1) := by simp; omega
    have htarget := componentTrader_residual_floor L P hP Q hQ j r n v hv
    have hrest : ∑ k ∈ (Finset.range (n + 1)).erase j, -((1 / 2 : ℝ) ^ k) ≤
        ∑ k ∈ (Finset.range (n + 1)).erase j,
          (componentTrader L Q k).netWorth P v n :=
      Finset.sum_le_sum (fun k _ => componentTrader_netWorth_floor L P hP Q hQ k n v hv)
    have hsplit := Finset.sum_erase_add (Finset.range (n + 1))
      (fun k => (componentTrader L Q k).netWorth P v n) hjS
    have hpowsplit := Finset.sum_erase_add (Finset.range (n + 1))
      (fun k => (1 / 2 : ℝ) ^ k) hjS
    have hsum := finite_half_pow_sum_lt_two n
    rw [← hsplit]
    rw [Finset.sum_neg_distrib] at hrest
    linarith
  · have hnj : n < j := Nat.lt_of_not_ge hjn
    rw [budgetedFirmRaw_netWorth_eq_zero_of_lt L P Q hQ j (r + 1) n (by omega) hnj v,
      mul_zero, sub_zero]
    exact tradingFirmTrader_netWorth_floor L P hP Q hQ n v hv

/-! ## Dominance -/

/-- **Trading Firm Dominance over an assessment process**, covered-index core. -/
theorem trading_firm_dominance_of_covered (L : Assessment) (P : History)
    (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day φ, P day φ = (Q day φ : ℝ)) (Tr : Trader)
    (hcov : ∃ j : ℕ, enumeratedTrader j = Tr) (hEx : L.Exploits Tr P) :
    L.Exploits (tradingFirmTrader L Q) P := by
  obtain ⟨j, hj⟩ := hcov
  have hraw : L.Exploits (firmRawTrader j) P := by
    unfold firmRawTrader
    rw [hj]
    exact exploits_gate Tr P hP hEx j
  obtain ⟨b, hb, hbudget⟩ :=
    AssessmentProcess.exists_budgetedTrader_exploits L (firmRawTrader j) P Q hQ hraw
  have hr : (b - 1) + 1 = b := by omega
  have hweight : 0 < (tradingFirmWeight j b : ℝ) := by
    exact_mod_cast tradingFirmWeight_pos j b
  refine ⟨⟨-2, ?_⟩, ?_⟩
  · rintro x ⟨n, v, hv, rfl⟩
    exact tradingFirmTrader_netWorth_floor L P hP Q hQ n v hv
  · intro hUpper
    apply hbudget.2
    rcases hUpper with ⟨U, hU⟩
    refine ⟨(U + 2) / (tradingFirmWeight j b : ℝ), ?_⟩
    rintro x ⟨n, v, hv, rfl⟩
    have hfirm := hU ⟨n, v, hv, rfl⟩
    have hres := tradingFirmTrader_residual_floor L P hP Q hQ j (b - 1) n v hv
    rw [hr] at hres
    apply (le_div_iff₀ hweight).2
    linarith

/-- **Trading Firm Dominance over an assessment process** (`lem:tfdom`
generalized): an exploiting efficiently computable trader makes the firm
exploit. -/
theorem trading_firm_dominance (L : Assessment) (P : History)
    (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day φ, P day φ = (Q day φ : ℝ)) (Tr : Trader)
    (hTr : EfficientlyComputable Tr) (hEx : L.Exploits Tr P) :
    L.Exploits (tradingFirmTrader L Q) P :=
  trading_firm_dominance_of_covered L P hP Q hQ Tr
    (exists_enumeratedTrader_eq Tr hTr) hEx

/-! ## The recursive market and `LIC_L`

The recursion is the source's, with the firm replaced.  The MarketMaker lemma is
the source's and needs no hypothesis about the assessment process: its bound
`netWorth < 1` holds at *every* propositionally consistent world. -/

/-- The recursive rational states of the assessment-process construction. -/
noncomputable def states (L : Assessment) : ℕ → RationalBeliefState
  | n =>
      let past := List.ofFn fun i : Fin n => states L i
      MarketMaker ((TradingFirm L).action n past) past
        (marketMakerError n) (marketMakerError_pos n)
termination_by n => n
decreasing_by exact i.isLt

/-- The exact rational quote table. -/
noncomputable def quote (L : Assessment) : ℕ → Sentence → ℚ :=
  fun n => (states L n).quote

/-- The real-valued market history. -/
noncomputable def history (L : Assessment) : History :=
  fun n => (states L n).toValuation

/-- The ordinary trader the recursive MarketMaker actually faces. -/
noncomputable def firmTrader (L : Assessment) : Trader where
  strat n := (TradingFirm L).action n (List.ofFn fun i : Fin n => states L i)

lemma rationalHistory_past (L : Assessment) {n day : ℕ} (hday : day < n)
    (φ : Sentence) :
    rationalHistory (List.ofFn fun i : Fin n => states L i) day φ = quote L day φ := by
  simp [rationalHistory, quote, hday]

lemma states_eq_marketMakerStates (L : Assessment) (n : ℕ) :
    states L n = marketMakerStates (firmTrader L) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hpast : (List.ofFn fun i : Fin n => states L i) =
          List.ofFn fun i : Fin n => marketMakerStates (firmTrader L) i := by
        apply List.ext_getElem
        · simp
        · intro i hi₁ hi₂
          simp only [List.getElem_ofFn]
          exact ih i (by simpa using hi₁)
      rw [states, marketMakerStates]
      change MarketMaker ((TradingFirm L).action n
            (List.ofFn fun i : Fin n => states L i))
          (List.ofFn fun i : Fin n => states L i)
          (marketMakerError n) (marketMakerError_pos n) =
        MarketMaker ((TradingFirm L).action n
            (List.ofFn fun i : Fin n => states L i))
          (List.ofFn fun i : Fin n => marketMakerStates (firmTrader L) i)
          (marketMakerError n) (marketMakerError_pos n)
      rw [hpast]

lemma history_eq_marketMakerHistory (L : Assessment) :
    history L = marketMakerHistory (firmTrader L) := by
  funext n φ
  rw [history, marketMakerHistory, states_eq_marketMakerStates]

/-- Prefix invariance identifies the adaptive realized firm with the static
complete-table firm used by dominance. -/
lemma tradingFirmTrader_quote_eq_firmTrader (L : Assessment) :
    tradingFirmTrader L (quote L) = firmTrader L := by
  unfold tradingFirmTrader firmTrader
  congr 1
  funext n
  change TradingFirmAt L (quote L) n =
    TradingFirmAt L (rationalHistory (List.ofFn fun i : Fin n => states L i)) n
  apply TradingFirmAt_eq_of_eq_prefix
  intro day hday φ
  exact (rationalHistory_past L hday φ).symm

lemma history_range (L : Assessment) (day : ℕ) (φ : Sentence) :
    0 ≤ history L day φ ∧ history L day φ ≤ 1 :=
  (states L day).toValuation_mem_Icc φ

lemma history_eq_quote_cast (L : Assessment) (day : ℕ) (φ : Sentence) :
    history L day φ = (quote L day φ : ℝ) := rfl

/-- The realized firm cannot exploit its own market: the source MarketMaker
lemma's bound is uniform over all propositionally consistent worlds, so it applies
to whatever set the assessment process names. -/
theorem firmTrader_not_exploited (L : Assessment) :
    ¬ L.Exploits (firmTrader L) (history L) := by
  intro hexploits
  apply hexploits.2
  refine ⟨1, ?_⟩
  rintro x ⟨n, v, _, rfl⟩
  rw [history_eq_marketMakerHistory]
  exact (marketMaker_netWorth_lt_one (firmTrader L) v n).le

/-- **The generalized capstone.**  No efficiently computable trader exploits the
recursive market relative to the assessment process. -/
theorem no_efficient_trader_exploits (L : Assessment) (Tr : Trader)
    (hTr : EfficientlyComputable Tr) : ¬ L.Exploits Tr (history L) := by
  intro hEx
  have hfirm := trading_firm_dominance L (history L) (history_range L) (quote L)
    (history_eq_quote_cast L) Tr hTr hEx
  rw [tradingFirmTrader_quote_eq_firmTrader] at hfirm
  exact firmTrader_not_exploited L hfirm

/-- Assembly: with an exact partial-recursive presentation of the market supplied,
the recursive market satisfies `LIC_L`.  The computability hypothesis is exactly
the source's remaining construction obligation, transported. -/
theorem isLogicalInductor_of_computableMarket (L : Assessment)
    (hmarket : ComputableMarket (history L)) :
    L.IsLogicalInductor (history L) :=
  ⟨hmarket, fun Tr hTr => no_efficient_trader_exploits L Tr hTr⟩

end Workspace.Normativity.Contrib.AssessmentFirm

#print axioms Workspace.Normativity.Contrib.AssessmentFirm.exploits_of_boundedDifference
#print axioms Workspace.Normativity.Contrib.AssessmentFirm.exploits_gate
#print axioms Workspace.Normativity.Contrib.AssessmentFirm.TradingFirmAt_eq_of_eq_prefix
#print axioms Workspace.Normativity.Contrib.AssessmentFirm.tradingFirmTrader_netWorth_eq_component_sum
#print axioms Workspace.Normativity.Contrib.AssessmentFirm.componentAt_value_hasSum
#print axioms Workspace.Normativity.Contrib.AssessmentFirm.componentTrader_netWorth_hasSum
#print axioms Workspace.Normativity.Contrib.AssessmentFirm.componentTrader_netWorth_floor
#print axioms Workspace.Normativity.Contrib.AssessmentFirm.tradingFirmTrader_netWorth_floor
#print axioms Workspace.Normativity.Contrib.AssessmentFirm.tradingFirmTrader_residual_floor
#print axioms Workspace.Normativity.Contrib.AssessmentFirm.trading_firm_dominance_of_covered
#print axioms Workspace.Normativity.Contrib.AssessmentFirm.trading_firm_dominance
#print axioms Workspace.Normativity.Contrib.AssessmentFirm.states_eq_marketMakerStates
#print axioms Workspace.Normativity.Contrib.AssessmentFirm.tradingFirmTrader_quote_eq_firmTrader
#print axioms Workspace.Normativity.Contrib.AssessmentFirm.firmTrader_not_exploited
#print axioms Workspace.Normativity.Contrib.AssessmentFirm.no_efficient_trader_exploits
#print axioms Workspace.Normativity.Contrib.AssessmentFirm.isLogicalInductor_of_computableMarket

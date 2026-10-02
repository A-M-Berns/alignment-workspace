import Cleanroom.Lit.LitDdbAccuracyMm.MM.Defs
import Cleanroom.Lit.LitDdbAccuracyMm.Accuracy

/-!
# MM's worked examples as exact computations (Targets 16–17)

* **Example 3.1.2** (`ex312_*`): the two-world frame with rows `(0.8, 0.2)`, `(0.1, 0.9)` (the
  PDF's matrix; the `.md` transcription at l. 89 is garbled), `π = (½, ½)`, options
  `O₁ = (1, −1)`, `O₂ = (−1, 1)`: the delegated strategy `S_a = O₁, S_b = O₂` is worth `1 > 0`,
  and `π` values the frame (Theorem 7.6 with explicit hull weights). It also instantiates DDB's
  fn 40 (`Value.expAccuracy_le`) with the Brier accuracy measure, strictly:
  `E_π(A(π)) = −1/2 < −1/20 = E_π(A(P))` (`ex312_brier_expAccuracy_le`, audit r1 N1).
* **§4.1, the noisy expert** (`ex41_*`): twelve equiprobable states, Bob's decisions from
  Table 2; `L(D_B) = 21/12`; the gain is `43/12` (correct-decisions) or `33/12` (printed) — the
  paper's `32/12` matches neither (it drops one accepted `+3` and one accepted `+8` from its own
  table); `S(D_π) = −2` under both; "do not delegate" survives under both.
* **§4.2, the misaligned expert** (`ex42_*`): the main text's `S(D_B) = −700/12` and
  `S(D_π) = −150/12` are exactly the fee-free, correct-decisions scores of the raw gamble
  (Table 4's decisions); Appendix B's `−400/12` uses a hybrid accounting (opened rows judged on
  the fee-adjusted payoff, unopened rows on the raw one) and its `750/12` for Alice rests on the
  slip `(1/4)·400 = 300/12`; "delegate" survives under all of them.
* **§4.3, the broader-reach expert** (`ex43_*`): printed convention, uniform over boxes and
  within boxes: Alice `L = 23/9, G = 8/3, S = −1/9`; Bob `L = 23/15, G = 31/10, S = −47/30`.
* `printed_score_not_loss`: under the printed convention `S(D_A) ≤ S(D_π)` is *not* `L(D_A) ≤
  L(D_π)` (a one-world two-gamble witness); under correct-decisions it is (`scoreCorrect_le_iff`).
-/

namespace Cleanroom.Lit.LitDdbAccuracyMm.MM

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples

noncomputable section

set_option linter.unusedSectionVars false

/-! ## Example 3.1.2 -/

/-- Example 3.1.2's frame: rows `(0.8, 0.2)` and `(0.1, 0.9)` (the PDF's matrix, read so that
`E_a(O₁) = .8 − .2 = .6` and `E_b(O₁) = .1 − .9 = −.8` as the text computes).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.1.2 l. 89
Kind: D
Fidelity: exact (PDF; the `.md` matrix is garbled — finding) -/
def ex312 : Frame (Fin 2) :=
  mk2 ![8 / 10, 2 / 10] ![1 / 10, 9 / 10] (simplex2 _ _ (by norm_num) (by norm_num) (by norm_num))
    (simplex2 _ _ (by norm_num) (by norm_num) (by norm_num))

/-- Example 3.1.2's rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ex312_P : ex312.P 0 = ![8 / 10, 2 / 10] ∧ ex312.P 1 = ![1 / 10, 9 / 10] := ⟨rfl, rfl⟩

/-- The rows are distinct.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ex312_ne : ex312.P 0 ≠ ex312.P 1 := by
  intro h
  have := congrFun h 0
  rw [ex312_P.1, ex312_P.2] at this
  norm_num at this

/-- The options `O₁ = (1, −1)`, `O₂ = (−1, 1)`.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.1.2 l. 89
Kind: D
Fidelity: exact -/
def O₁ : Fin 2 → ℝ := ![1, -1]

/-- `O₂ = (−1, 1)`.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.1.2 l. 89
Kind: D
Fidelity: exact -/
def O₂ : Fin 2 → ℝ := ![-1, 1]

/-- The expectations of Example 3.1.2: `E_a(O₁) = 0.6`, `E_b(O₁) = −0.8`, `E_a(O₂) = −0.6`,
`E_b(O₂) = 0.8`, `E_π(O₁) = E_π(O₂) = 0`.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.1.2 l. 89
Kind: L
Fidelity: exact -/
theorem ex312_E : E (ex312.P 0) O₁ = 6 / 10 ∧ E (ex312.P 1) O₁ = -8 / 10 ∧
    E (ex312.P 0) O₂ = -6 / 10 ∧ E (ex312.P 1) O₂ = 8 / 10 ∧ E half O₁ = 0 ∧ E half O₂ = 0 := by
  obtain ⟨h0, h1⟩ := ex312_P
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [E, Fin.sum_univ_two, h0, h1, O₁, O₂, half]

/-- **Example 3.1.2, delegation.** On `{O₁, O₂}` the strategy `S_a = O₁, S_b = O₂` is recommended
and worth `1 > 0 = E_π(O₁) = E_π(O₂)`.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.1.2 l. 89–91
("in this decision problem, `π` prefers to delegate the decision since `1 > 0`")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem ex312_delegation :
    ex312.Recommended {O₁, O₂} ![O₁, O₂] ∧ stratValue half ![O₁, O₂] = 1 := by
  obtain ⟨e1, e2, e3, e4, _, _⟩ := ex312_E
  refine ⟨⟨⟨fun w => ?_, fun w v hwv => ?_⟩, fun w o ho => ?_⟩, ?_⟩
  · fin_cases w <;> simp
  · fin_cases w <;> fin_cases v <;> first | rfl | exact absurd hwv ex312_ne | exact absurd hwv.symm ex312_ne
  · simp only [mem_insert, mem_singleton] at ho
    fin_cases w <;> rcases ho with rfl | rfl <;> simp [e1, e2, e3, e4] <;> norm_num
  · norm_num [stratValue, Fin.sum_univ_two, half, O₁, O₂]

/-- Example 3.1.2's self-cell masses and informed experts.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ex312_selfMass :
    ex312.selfMass (ex312.P 0) = 8 / 10 ∧ ex312.selfMass (ex312.P 1) = 9 / 10 := by
  obtain ⟨hc0, hc1⟩ := cell_of_ne ex312 ex312_ne
  constructor
  · rw [Frame.selfMass, hc0]; norm_num [mass, ex312_P.1]
  · rw [Frame.selfMass, hc1]; norm_num [mass, ex312_P.2]

/-- Example 3.1.2's informed experts are the point masses.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ex312_informed :
    ex312.informed (ex312.P 0) = ![1, 0] ∧ ex312.informed (ex312.P 1) = ![0, 1] := by
  obtain ⟨hs0, hs1⟩ := ex312_selfMass
  constructor
  · ext w
    fin_cases w
    · simp only [Frame.informed, hs0]; norm_num [ex312_P.1]
    · norm_num [Frame.informed, hs0, ex312_ne.symm]
  · ext w
    fin_cases w
    · norm_num [Frame.informed, hs1, ex312_ne]
    · simp only [Frame.informed, hs1]; norm_num [ex312_P.2]

/-- **Example 3.1.2, Value.** `π = (½, ½)` values the frame (Theorem 7.6 through the hull
condition, with `P_a = 7/9·δ_a + 2/9·P_b`, `P_b = 7/8·δ_b + 1/8·P_a`, `π = 4/7·P_a + 3/7·P_b`),
as the text claims "By theorem 3.2, `π` values `P`".
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.1.2 l. 91;
item 084
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem ex312_value : Value half ex312 ∧ TotalTrust half ex312 := by
  obtain ⟨hs0, hs1⟩ := ex312_selfMass
  obtain ⟨hi0, hi1⟩ := ex312_informed
  obtain ⟨hP0, hP1⟩ := ex312_P
  have hcands := cands_eq_pair ex312 (by norm_num [half] : (0 : ℝ) < half 0)
    (by norm_num [half] : (0 : ℝ) < half 1)
  have hcm0 : ex312.candsMinus (ex312.P 0) = {ex312.P 1} := by
    rw [candsMinus_eq ex312 ex312_ne (by norm_num [hP0]) (by norm_num [hP0])]
    ext σ
    simp only [mem_erase, mem_insert, mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact absurd h2 h1
      · exact h2
    · rintro rfl; exact ⟨ex312_ne.symm, Or.inr rfl⟩
  have hcm1 : ex312.candsMinus (ex312.P 1) = {ex312.P 0} := by
    rw [candsMinus_eq ex312 ex312_ne (by norm_num [hP1]) (by norm_num [hP1])]
    ext σ
    simp only [mem_erase, mem_insert, mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact h2
      · exact absurd h2 h1
    · rintro rfl; exact ⟨ex312_ne, Or.inl rfl⟩
  have hhull : HullAndModestlyInformed half ex312 := by
    refine ⟨?_, ?_⟩
    · rw [hcands]
      exact mem_hull_of_comb (x := ex312.P 0) (y := ex312.P 1) (by simp) (by simp)
        (by norm_num : (0 : ℝ) ≤ 4 / 7) (by norm_num : (0 : ℝ) ≤ 3 / 7) (by norm_num)
        (by ext w; fin_cases w <;> norm_num [half, hP0, hP1])
    · intro ρ hρ
      rw [hcands] at hρ
      simp only [mem_insert, mem_singleton] at hρ
      rcases hρ with rfl | rfl
      · refine ⟨by rw [hs0]; norm_num, ?_⟩
        rw [hcm0, hi0]
        exact mem_hull_of_comb (x := ![1, 0]) (y := ex312.P 1)
          (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (by simp))
          (by norm_num : (0 : ℝ) ≤ 7 / 9) (by norm_num : (0 : ℝ) ≤ 2 / 9) (by norm_num)
          (by ext w; fin_cases w <;> norm_num [hP0, hP1])
      · refine ⟨by rw [hs1]; norm_num, ?_⟩
        rw [hcm1, hi1]
        exact mem_hull_of_comb (x := ![0, 1]) (y := ex312.P 0)
          (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (by simp))
          (by norm_num : (0 : ℝ) ≤ 7 / 8) (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num)
          (by ext w; fin_cases w <;> norm_num [hP0, hP1])
  have htt := (totalTrust_iff_hullAndModestlyInformed half_mem ex312).2 hhull
  exact ⟨(value_iff_totalTrust half_mem ex312).2 htt, htt⟩

/-- **Fn 40 instantiated on Example 3.1.2 with Brier accuracy**: the full hypothesis package of
`Value.expAccuracy_le` is inhabited (grade N+: the rows differ from each other and from `π`), and
the conclusion is strict. (Adopted from the round-1 adversarial audit's probe `Vacuity.lean`.)
Source: [[Deference Done Better]] fn 40; audit r1 (adversarial) N1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem ex312_brier_expAccuracy_le :
    E half (brierAcc half) ≤ ∑ w, half w * brierAcc (ex312.P w) w :=
  Value.expAccuracy_le ex312_value.1
    (strictlyProperOn_brierAcc (credSet_sub_simplex half_mem ex312))

/-- The instance is strict: `E_π(A(π)) = −1/2 < −1/20 = E_π(A(P))`.
Source: [[Deference Done Better]] fn 40; audit r1 (adversarial) N1
Kind: L
Fidelity: exact -/
theorem ex312_brier_values :
    E half (brierAcc half) = -1 / 2 ∧ ∑ w, half w * brierAcc (ex312.P w) w = -1 / 20 := by
  obtain ⟨h0, h1⟩ := ex312_P
  constructor
  · simp [E, brierAcc, ind, Fin.sum_univ_two, half]; norm_num
  · simp [brierAcc, ind, Fin.sum_univ_two, half, h0, h1]; norm_num

/-! ## §4.1: the noisy expert -/

/-- The uniform distribution on twelve states.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §4.1 l. 131
Kind: D
Fidelity: exact -/
def unif12 : Fin 12 → ℝ := fun _ => 1 / 12

/-- §4.1's states in Table 2's order (`ω`, peek, noise): Alice's payoff `ω` at each.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] App. A Table 2
Kind: D
Fidelity: exact -/
def pay41 : Fin 1 → Fin 12 → ℝ := fun _ => ![-5, -5, -5, -5, 3, 3, 3, 3, 8, 8, 8, 8]

/-- Bob's decisions in Table 2 (`true` = Open), state by state.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] App. A Table 2
Kind: D
Fidelity: exact -/
def opens41 : Fin 12 → Bool :=
  ![true, false, true, false, true, true, true, false, true, true, true, false]

/-- Bob's state-indexed rule `D_B` for the one gamble.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §4.1 l. 131
Kind: D
Fidelity: exact (state-indexed, as Bob's decision depends on his information and noise) -/
def DB41 : Fin 12 → Finset (Fin 1) := fun w => if opens41 w then {0} else ∅

/-- Alice's rule `D_π`: always open.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §4.1 l. 131
Kind: D
Fidelity: exact -/
def Dπ41 : Fin 12 → Finset (Fin 1) := fun _ => {0}

/-- Point mass on the one gamble.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def μ1 : Fin 1 → ℝ := fun _ => 1

/-- **§4.1, exact scores.** `L(D_B) = 21/12`; `G(D_B) = 43/12` (correct-decisions) and `33/12`
(printed) — the paper's `32/12 = (3+3+8+8+5+5)/12` matches neither: Table 2 has six accepted
winners (`+3, +3, +3, +8, +8, +8`) and two correct rejections (`+5, +5`); `L(D_π) = 20/12`,
`G(D_π) = 44/12`, `S(D_π) = −2` under both conventions.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §4.1 l. 131,
App. A Table 2; items 087, 088
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem ex41_scores :
    loss unif12 pay41 μ1 DB41 = 21 / 12 ∧ gainCorrect unif12 pay41 μ1 DB41 = 43 / 12 ∧
    gainPrinted unif12 pay41 μ1 DB41 = 33 / 12 ∧
    loss unif12 pay41 μ1 Dπ41 = 20 / 12 ∧ gainCorrect unif12 pay41 μ1 Dπ41 = 44 / 12 ∧
    gainPrinted unif12 pay41 μ1 Dπ41 = 44 / 12 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [loss, gainCorrect, gainPrinted, Fin.sum_univ_succ, unif12, pay41, μ1, DB41, Dπ41,
      opens41] <;> norm_num

/-- **§4.1, the verdict survives** under both conventions: `S(D_π) < S(D_B)`, so Alice should not
delegate (`−2 < −22/12` and `−2 < −1`).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §4.1 l. 133
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem ex41_verdict :
    scoreCorrect unif12 pay41 μ1 Dπ41 < scoreCorrect unif12 pay41 μ1 DB41 ∧
    scorePrinted unif12 pay41 μ1 Dπ41 < scorePrinted unif12 pay41 μ1 DB41 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ex41_scores
  unfold scoreCorrect scorePrinted
  rw [h1, h2, h3, h4, h5, h6]
  norm_num

/-! ## §4.2: the misaligned expert -/

/-- §4.2's states in Table 4's order (`ω`, peek): Alice's raw payoff `ω`.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] App. B Table 4
Kind: D
Fidelity: exact -/
def pay42 : Fin 1 → Fin 12 → ℝ :=
  fun _ => ![-400, -400, -400, 25, 25, 25, 100, 100, 100, 225, 225, 225]

/-- Bob's decisions in Table 4 (`true` = opens).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] App. B Table 4
Kind: D
Fidelity: exact -/
def opens42 : Fin 12 → Bool :=
  ![true, false, false, true, false, false, true, true, false, true, true, false]

/-- Bob's state-indexed rule for §4.2.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §4.2 l. 135
Kind: D
Fidelity: exact -/
def DB42 : Fin 12 → Finset (Fin 1) := fun w => if opens42 w then {0} else ∅

/-- Alice's rule for §4.2: never open.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §4.2 l. 135
Kind: D
Fidelity: exact -/
def Dπ42 : Fin 12 → Finset (Fin 1) := fun _ => ∅

/-- **§4.2, the main text's numbers are the fee-free correct-decisions scores.** With the raw
gamble `ω` and Table 4's decisions: `L(D_B) = 775/12`, `G(D_B) = 1475/12`, `S(D_B) = −700/12`;
Alice never opens: `L(D_π) = 1050/12`, `G(D_π) = 1200/12`, `S(D_π) = −150/12` — exactly the
main text's `−700/12` and `−150/12`. (Appendix B's `750/12` for Alice rests on the slip
`(1/4)·400 = 300/12`; its `−400/12` for Bob is the hybrid accounting `ex42_hybrid`.)
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §4.2 l. 137,
App. B Table 4; item 088
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem ex42_scores :
    loss unif12 pay42 μ1 DB42 = 775 / 12 ∧ gainCorrect unif12 pay42 μ1 DB42 = 1475 / 12 ∧
    scoreCorrect unif12 pay42 μ1 DB42 = -700 / 12 ∧
    loss unif12 pay42 μ1 Dπ42 = 1050 / 12 ∧ gainCorrect unif12 pay42 μ1 Dπ42 = 1200 / 12 ∧
    scoreCorrect unif12 pay42 μ1 Dπ42 = -150 / 12 := by
  have h1 : loss unif12 pay42 μ1 DB42 = 775 / 12 := by
    simp [loss, Fin.sum_univ_succ, unif12, pay42, μ1, DB42, opens42]; norm_num
  have h2 : gainCorrect unif12 pay42 μ1 DB42 = 1475 / 12 := by
    simp [gainCorrect, Fin.sum_univ_succ, unif12, pay42, μ1, DB42, opens42]; norm_num
  have h3 : loss unif12 pay42 μ1 Dπ42 = 1050 / 12 := by
    simp [loss, Fin.sum_univ_succ, unif12, pay42, μ1, Dπ42]; norm_num
  have h4 : gainCorrect unif12 pay42 μ1 Dπ42 = 1200 / 12 := by
    simp [gainCorrect, Fin.sum_univ_succ, unif12, pay42, μ1, Dπ42]; norm_num
  refine ⟨h1, h2, ?_, h3, h4, ?_⟩
  · unfold scoreCorrect; rw [h1, h2]; norm_num
  · unfold scoreCorrect; rw [h3, h4]; norm_num

/-- **§4.2, the verdict survives** (`−700/12 < −150/12`): delegate.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §4.2 l. 137
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem ex42_verdict : scoreCorrect unif12 pay42 μ1 DB42 < scoreCorrect unif12 pay42 μ1 Dπ42 := by
  obtain ⟨_, _, h3, _, _, h6⟩ := ex42_scores
  rw [h3, h6]; norm_num

/-- Alice's fee-adjusted payoff when Bob opens (`ω − 50`).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] App. B l. 265
Kind: D
Fidelity: exact -/
def payFee42 : Fin 12 → ℝ :=
  ![-450, -450, -450, -25, -25, -25, 50, 50, 50, 175, 175, 175]

/-- **Appendix B's hybrid accounting**: an opened row is judged and measured by the fee-adjusted
payoff, an unopened row by the raw one. Loss `= 850/12`, gain `= 1250/12`, score `= −400/12`.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] App. B l. 353–359
Kind: D
Fidelity: variant: Appendix B's per-row rule, stated as such (not a `loss`/`gain` of the
framework) -/
def hybridLoss42 : ℝ :=
  ∑ w, (1 / 12 : ℝ) * (if opens42 w then (if payFee42 w < 0 then |payFee42 w| else 0)
    else (if 0 ≤ pay42 0 w then |pay42 0 w| else 0))

/-- Appendix B's hybrid gain.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] App. B l. 355
Kind: D
Fidelity: variant: Appendix B's per-row rule -/
def hybridGain42 : ℝ :=
  ∑ w, (1 / 12 : ℝ) * (if opens42 w then (if 0 ≤ payFee42 w then |payFee42 w| else 0)
    else (if pay42 0 w < 0 then |pay42 0 w| else 0))

/-- **Appendix B's numbers, reproduced under its hybrid rule**: `850/12`, `1250/12`, `−400/12`.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] App. B l. 353–359
Kind: N+
Fidelity: exact (for the hybrid rule)
Hyps: (a) none -/
theorem ex42_hybrid :
    hybridLoss42 = 850 / 12 ∧ hybridGain42 = 1250 / 12 ∧ hybridLoss42 - hybridGain42 = -400 / 12 := by
  have h1 : hybridLoss42 = 850 / 12 := by
    simp [hybridLoss42, Fin.sum_univ_succ, opens42, payFee42, pay42]; norm_num
  have h2 : hybridGain42 = 1250 / 12 := by
    simp [hybridGain42, Fin.sum_univ_succ, opens42, payFee42, pay42]; norm_num
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]; norm_num

/-! ## §4.3: the broader-reach expert -/

/-- The five boxes' payoffs on twelve equiprobable states (uniform within each box: three-outcome
boxes cycle with period `3`, the four-outcome box with period `4`).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §4.3 Table 1
Kind: D
Fidelity: exact -/
def boxes43 : Fin 5 → Fin 12 → ℝ :=
  ![![-6, 3, 9, -6, 3, 9, -6, 3, 9, -6, 3, 9],
    ![-8, -4, 12, -8, -4, 12, -8, -4, 12, -8, -4, 12],
    ![-10, 2, 3, -10, 2, 3, -10, 2, 3, -10, 2, 3],
    ![1, 2, 3, 4, 1, 2, 3, 4, 1, 2, 3, 4],
    fun _ => 5]

/-- Alice's reach: uniform over `A₁, A₂, A₃`.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §4.3 l. 157
Kind: D
Fidelity: exact -/
def μself43 : Fin 5 → ℝ := ![1 / 3, 1 / 3, 1 / 3, 0, 0]

/-- Bob's reach: uniform over all five boxes.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §4.3 l. 157
Kind: D
Fidelity: exact -/
def μdel43 : Fin 5 → ℝ := fun _ => 1 / 5

/-- The common decision rule (open iff `E[ω] ≥ 0`): `{A₁, A₂}` for Alice's boxes.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §4.3 Table 1
Kind: D
Fidelity: exact -/
def Dπ43 : Fin 12 → Finset (Fin 5) := fun _ => {0, 1}

/-- Bob's rule: `{A₁, A₂, A₄, A₅}`.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §4.3 Table 1
Kind: D
Fidelity: exact -/
def DB43 : Fin 12 → Finset (Fin 5) := fun _ => {0, 1, 3, 4}

/-- **§4.3, exact scores (printed convention)**: Alice `L = 23/9`, `G = 8/3`, `S = −1/9`; Bob
`L = 23/15`, `G = 31/10`, `S = −47/30` (the printed `2.56, 2.67, −0.11, 1.53, 3.1, −1.57`).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §4.3 l. 161,
App. C Table 6; item 089
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem ex43_scores :
    loss unif12 boxes43 μself43 Dπ43 = 23 / 9 ∧ gainPrinted unif12 boxes43 μself43 Dπ43 = 8 / 3 ∧
    scorePrinted unif12 boxes43 μself43 Dπ43 = -1 / 9 ∧
    loss unif12 boxes43 μdel43 DB43 = 23 / 15 ∧ gainPrinted unif12 boxes43 μdel43 DB43 = 31 / 10 ∧
    scorePrinted unif12 boxes43 μdel43 DB43 = -47 / 30 := by
  have h1 : loss unif12 boxes43 μself43 Dπ43 = 23 / 9 := by
    simp only [loss, Fin.sum_univ_five]
    simp [Fin.sum_univ_succ, unif12, boxes43, μself43, Dπ43]; norm_num
  have h2 : gainPrinted unif12 boxes43 μself43 Dπ43 = 8 / 3 := by
    simp only [gainPrinted, Fin.sum_univ_five]
    simp [Fin.sum_univ_succ, unif12, boxes43, μself43, Dπ43]; norm_num
  have h3 : loss unif12 boxes43 μdel43 DB43 = 23 / 15 := by
    simp only [loss, Fin.sum_univ_five]
    simp [Fin.sum_univ_succ, unif12, boxes43, μdel43, DB43]; norm_num
  have h4 : gainPrinted unif12 boxes43 μdel43 DB43 = 31 / 10 := by
    simp only [gainPrinted, Fin.sum_univ_five]
    simp [Fin.sum_univ_succ, unif12, boxes43, μdel43, DB43]; norm_num
  refine ⟨h1, h2, ?_, h3, h4, ?_⟩ <;> unfold scorePrinted
  · rw [h1, h2]; norm_num
  · rw [h3, h4]; norm_num

/-- **§4.3, the verdict**: `−47/30 < −1/9`, delegation is strictly rational.
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §4.3 l. 163
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem ex43_verdict :
    scorePrinted unif12 boxes43 μdel43 DB43 < scorePrinted unif12 boxes43 μself43 Dπ43 := by
  obtain ⟨_, _, h3, _, _, h6⟩ := ex43_scores
  rw [h3, h6]; norm_num

/-! ## Printed vs correct-decisions: score comparison is loss comparison only for the latter -/

/-- One world, two gambles `−1` and `+1`, uniform weight.
Source: none: infrastructure (item 087)
Kind: D
Fidelity: n/a -/
def twoGam : Fin 2 → Fin 1 → ℝ := ![fun _ => -1, fun _ => 1]

/-- **Under the printed convention, `S(D_A) ≤ S(D_π)` is not `L(D_A) ≤ L(D_π)`**: rejecting both
gambles and accepting both have equal loss `1/2`, but printed scores `1/2` and `0`. Under the
correct-decisions convention the two comparisons coincide (`scoreCorrect_le_iff`).
Source: [[herrmann-2025-a-decision-theoretic-approach-for-managing-misalignment]] §3.4 l. 119–123;
item 087
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem printed_score_not_loss :
    loss (fun _ => (1 : ℝ)) twoGam (fun _ => 1 / 2) (fun _ => ∅) ≤
      loss (fun _ => (1 : ℝ)) twoGam (fun _ => 1 / 2) (fun _ => univ) ∧
    ¬ (scorePrinted (fun _ => (1 : ℝ)) twoGam (fun _ => 1 / 2) (fun _ => ∅) ≤
      scorePrinted (fun _ => (1 : ℝ)) twoGam (fun _ => 1 / 2) (fun _ => univ)) := by
  constructor <;> simp [loss, scorePrinted, gainPrinted, Fin.sum_univ_two, twoGam] <;> norm_num

end

end Cleanroom.Lit.LitDdbAccuracyMm.MM

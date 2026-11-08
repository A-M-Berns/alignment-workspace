/-
# Where obligations bind: the score-side realization of the rebuttal run's decision

Round `projects/normativity/rounds/2026-11-07-score-side-binding/`.

The rebuttal run (`WarrantInductorRebuttal`) poses one decision question — act on the first
warrant's conclusion or refrain — at dates `4` and `9`, and its gate acts with mass at least
`24/25` before the refutation and refrains with certainty after it (`same_question`).  Every
row that run enforces is settled by the deductive process: the premise, applicability and
strength forms constrain credences in sentences the process pins, the coherence rows are
consequences, the pins are the process's own.  None is an obligation on conduct.

This module adds the smallest obligation on conduct the fixture lacks — **refrain while live**:
acting on the conclusion is a shortfall at any date at which the originating obligation's
account still carries a live leaf, assessed by that account's fate — and realizes it two ways
on the *same* market history.

* **On prices** (§2) it compiles to the row `P(X∧A∧Y) ≤ τ`.  At date `4` that row conflicts
  with the strength and applicability rows: a three-row Farkas certificate (`conductCert`)
  refutes the region (`conduct_on_prices_conflicts`), so a compiler returning it withholds the
  whole date and the epistemic rows lose their force with it.  At date `9` the row is implied
  by the pin and adds nothing (`conduct_on_prices_idle`).
* **On the score** (§3) the enforcer's bundle is the rebuttal run's at every date
  (`bundle_unchanged`), the market is the same object (`market_unchanged`; the shape of
  `DecisionComponent.noninterference`), no held row is the conduct row (`no_conduct_row`), and
  the obligation reaches the decision as a charge `ϖ` times the market's price of the
  shortfall sentence, subtracted from the acting score — the shape of
  `BRIACorrigibility.evalOf`.  After the refutation the gate refrains with certainty for every
  charge (`after`).  Before it, the gate acts with mass at least `24/25` whenever the charge is
  at most `19/240`, the room the enforced rows leave above `τ + δ` (`before`); when the charge
  reaches the acting score's room above `τ`, the acting option's weight is zero and no price
  has moved (`override`).

So the reversal obtains with no row on conduct enforced; it needs the strength row — without
it the date-4 region admits `P(X∧A∧Y) = 0` and nothing certifies acting — and the obligation on
conduct binds on the score, scaled by `ϖ` and the priced assessment, never on a belief.

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.WarrantInductorRebuttal
import Workspace.Deference.Contrib.DecisionComponent

namespace Workspace.Normativity.Contrib.WarrantInductorScoreSide

open LogicalInduction
open Workspace.Normativity.Contrib.NormativeInductorComposition
open Workspace.Normativity.Contrib.SeedStatics
open Workspace.Normativity.Contrib.WarrantEntitlement
open Workspace.Normativity.Contrib.WarrantEntitlement.Fixture2 (X XA XAY Y Z)
open Workspace.Normativity.Contrib.WarrantForce
open Workspace.Normativity.Contrib.WarrantInductor
open Workspace.Normativity.Contrib.WarrantInductorWitness (occZ grounds structural coh₁ coh₂ coh₃
  F5 tol DP wit P₁ eXAY eXA_XAY rowS4 rowA4 rowS4_a rowS4_b rowA4_a rowA4_b account_live)
open Workspace.Normativity.Contrib.WarrantInductorRebuttal
open Workspace.Normativity.Contrib.GatedChoice
open Workspace.Normativity.Contrib.OpenIntegrityEvolution.Witness (state₀)
open Workspace.Normativity.Contrib.OccurrenceIntegrity (Initial)
open Workspace.Normativity.Contrib.OccurrenceIntegrity.Witness (start)
open Workspace.Normativity.Contrib.EndToEndWitness.Run (n₁ nE cP cA cS settlementAt occP occA occS)
open Finset

/-! ## 1. The obligation on conduct -/

/-- **Refrain while live** (provisional name): the smallest obligation on conduct the fixture
lacks.  Acting on the first warrant's conclusion is a shortfall at any date at which the
originating obligation's account — occurrence `0` of `state₀`, the origin of the first
warrant's occurrences in `WarrantInductorWitness.entitlement` — carries a live leaf; the
obligation is assessed by that account's fate.  `shortfall` is the sentence the market prices
for the event "acting at this date will be assessed a shortfall": the application's, as the
shortfall and taint events are in `DecisionComponent`. -/
structure RefrainWhileLive where
  shortfall : Sentence

/-- **The assessment**: acting at date `n` is a shortfall iff the originating account is live.
An evaluation settles this, not the deductive process. -/
def ShortfallAt (_n : ℕ) : Prop :=
  OccurrenceIntegrity.Fate.live ∈
    (state₀.account 0 (by simp [state₀, Initial.state, start])).fates

/-- In `state₀` the originating account is live at every date, so acting is a shortfall
throughout: the obligation binds at date `4` as much as at date `9`. -/
theorem shortfall_assessed (n : ℕ) : ShortfallAt n := account_live 0 _

/-! ## 2. The obligation compiled onto prices: a row that conflicts or idles -/

/-- What *refrain* compiles to on prices: the acting score `P(X∧A∧Y)` held at or below the
threshold `τ = 1/3`, so that the gate refrains. -/
def conductRow : Row 5 := ⟨eXAY, 1/3⟩

lemma memS4 : (⟨Cite.sub 3, rowS4⟩ : CitedRow (Cite 5) 5) ∈ (NB 4).bundle :=
  ((NB 4).mem_bundle_iff _).2
    (Or.inl ⟨occS, by rw [survivors_eq]; simp [show (4 : ℕ) < nE from by decide], rfl⟩)

lemma memA4 : (⟨Cite.sub 2, rowA4⟩ : CitedRow (Cite 5) 5) ∈ (NB 4).bundle :=
  ((NB 4).mem_bundle_iff _).2 (Or.inl ⟨occA, by rw [survivors_eq]; simp, rfl⟩)

/-- **The Farkas certificate against the date-4 bundle with the conduct row**: the specialized
strength row, two thirds of the specialized applicability row and the conduct row sum to
`0 ≤ −1/6`. -/
def conductCert : FarkasCert 5 3 where
  mult := ![1, 2/3, 1]
  row := ![rowS4, rowA4, conductRow]
  mult_nonneg := fun i => by fin_cases i <;> norm_num
  coeff_sum := fun j => by
    fin_cases j <;> simp [Fin.sum_univ_three, rowS4_a, rowA4_a, conductRow, eXAY] <;> norm_num
  const_sum := by
    simp [Fin.sum_univ_three, rowS4_b, rowA4_b, conductRow]; norm_num

/-- **On prices the obligation conflicts.**  The date-4 bundle with the conduct row has no
admissible price vector (`conductCert` through `conflict_sound`); a compiler returning this
certificate withholds the whole date (`WarrantInductor.conflict_withheld`), the strength and
applicability rows included.  Placed on prices, the obligation on conduct costs the epistemic
rows their force. -/
theorem conduct_on_prices_conflicts :
    ¬ ∃ x, ((NB 4).bundle ++ [(⟨Cite.str 99, conductRow⟩ : CitedRow (Cite 5) 5)]).Region x := by
  refine conflict_sound _ conductCert ?_
  intro i
  fin_cases i
  · exact Or.inl ⟨⟨Cite.sub 3, rowS4⟩, List.mem_append_left _ memS4, rfl⟩
  · exact Or.inl ⟨⟨Cite.sub 2, rowA4⟩, List.mem_append_left _ memA4, rfl⟩
  · exact Or.inl ⟨⟨Cite.str 99, conductRow⟩,
      List.mem_append_right _ (List.mem_singleton_self _), rfl⟩

/-- **At date 9 the conduct row idles**: every region point satisfies it, because the pin holds
`P(X∧A∧Y) = 0`.  On prices the obligation either collapses the date or adds nothing. -/
theorem conduct_on_prices_idle (x : Fin 5 → ℚ) (hx : (NB 9).region x) : conductRow.Sat x := by
  have h := (((region_iff 9 x).1 hx).2.2.1 (by decide)).1
  simp [conductRow, Row.Sat, eXAY, Fin.sum_univ_five, Fixture2.XAY] at h ⊢
  rw [h]; norm_num

/-! ## 3. The score-side realization -/

/-- **The score-side realization** (provisional name): a schedule, the obligation on conduct,
and the charge `ϖ` per unit price of its shortfall event. -/
structure ScoreSide where
  schedule : WarrantSchedule 5
  obligation : RefrainWhileLive
  ϖ : ℝ

/-- The realization this module runs: the rebuttal run's own schedule, untouched. -/
def scoreSide (σ : Sentence) (ϖ : ℝ) : ScoreSide := ⟨WB, ⟨σ⟩, ϖ⟩

/-- **The enforcer's bundle is the rebuttal run's at every date.** -/
theorem bundle_unchanged (σ : Sentence) (ϖ : ℝ) (n : ℕ) :
    (scoreSide σ ϖ).schedule.bundle n = (NB n).bundle := bundle_eq n

/-- **Non-interference, on the market object.**  The score-side realization's market is the
rebuttal run's: one `History`, the same price at every date and sentence.  The charge reads
prices and adds no trader (`DecisionComponent.noninterference` is the shape). -/
theorem market_unchanged (σ : Sentence) (ϖ : ℝ) :
    (scoreSide σ ϖ).schedule.market DP = WB.market DP := rfl

/-- The constant of a pin row is `0`, `1` or `−1`. -/
lemma pinRow_b {d : ℕ} (F : Settlement d) (i : Fin d) {r : Row d} (hr : r ∈ F.pinRowsAt i) :
    r.b = 0 ∨ r.b = 1 ∨ r.b = -1 := by
  unfold Settlement.pinRowsAt at hr
  cases h : F.val i with
  | none => simp [h] at hr
  | some b =>
    simp [h] at hr
    rcases hr with rfl | rfl <;> cases b <;> simp [truth]

/-- **No held row has the conduct row's constant.**  The sub rows' constants are `−4/5`, `1/5`,
`0`, `−3/4`; the coherence rows' are `0`; the pins' are `0`, `1`, `−1`.  The conduct row's is
`1/3`. -/
theorem bundle_row_b_ne (n : ℕ) {c : CitedRow (Cite 5) 5} (hc : c ∈ WB.bundle n) :
    c.row.b ≠ 1/3 := by
  rw [bundle_eq] at hc
  rcases ((NB n).mem_bundle_iff c).1 hc with ⟨o, ho, rfl⟩ | ⟨it, hit, rfl⟩ | ⟨i, r, hr, rfl⟩
  · simp only [NB_settlement]
    rw [survivors_eq] at ho
    by_cases hE : n < nE
    · simp only [hE, if_true, List.singleton_append, List.mem_cons, List.not_mem_nil,
        or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;>
        by_cases h1 : n₁ ≤ n <;> by_cases h8 : nE ≤ n <;>
        simp [specialize, settledTerm, settlementAt, h1, h8, occP, occA, occS, occZ,
          Fixture2.occP, Fixture2.occA, Fixture2.occS, Fixture2.occZ, Form.row,
          Fin.sum_univ_five, truth, cP, cA, cS, Workspace.Normativity.Contrib.WarrantInductorWitness.cZ,
          Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z] <;> norm_num
    · simp only [hE, if_false, List.nil_append, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl <;>
        by_cases h1 : n₁ ≤ n <;> by_cases h8 : nE ≤ n <;>
        simp [specialize, settledTerm, settlementAt, h1, h8, occP, occA, occZ,
          Fixture2.occP, Fixture2.occA, Fixture2.occZ, Form.row,
          Fin.sum_univ_five, truth, cP, cA, Workspace.Normativity.Contrib.WarrantInductorWitness.cZ,
          Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z] <;> norm_num
  · simp only [NB_settlement]
    rw [liveStr_eq] at hit
    simp only [structural, List.mem_cons, List.not_mem_nil, or_false] at hit
    rcases hit with rfl | rfl | rfl <;>
      by_cases h1 : n₁ ≤ n <;> by_cases h8 : nE ≤ n <;>
      simp [specialize, settledTerm, settlementAt, h1, h8, coh₁, coh₂, coh₃, Fin.sum_univ_five,
        truth] <;> norm_num
  · simp only [NB_settlement] at hr
    rcases pinRow_b _ _ hr with h | h | h <;> simp only [h] <;> norm_num

/-- **No conduct row is enforced**: no row the score-side realization's enforcer holds is the
conduct row, at any date. -/
theorem no_conduct_row (σ : Sentence) (ϖ : ℝ) (n : ℕ) :
    ∀ c ∈ (scoreSide σ ϖ).schedule.bundle n, c.row ≠ conductRow := by
  intro c hc heq
  exact bundle_row_b_ne n hc (by rw [heq]; rfl)

/-- The price of the shortfall event at date `n`: the realization's market, on the shortfall
sentence. -/
noncomputable def shortfallPrice (R : ScoreSide) (n : ℕ) : ℝ :=
  R.schedule.market DP n R.obligation.shortfall

/-- The priced shortfall over the menu: acting may be assessed a shortfall; refraining never
is, since the obligation is to refrain. -/
noncomputable def pS (R : ScoreSide) (n : ℕ) : Fin 2 → ℝ := ![shortfallPrice R n, 0]

/-- **The charged score**: the rebuttal run's score less `ϖ` times the priced shortfall — the
shape of `BRIACorrigibility.evalOf` (a bid less `ϖ` per priced event), with no structurally
recognized violation. -/
noncomputable def chargedScore (R : ScoreSide) (n : ℕ) (q : Fin 2) : ℝ :=
  P₁.scoreR (Problem.priceR R.schedule DP n) q - R.ϖ * pS R n q

/-- **The score-side gate**: the soft gate on the charged scores, with the problem's
preference, threshold and ramp. -/
noncomputable def scoreGate (R : ScoreSide) (n : ℕ) : Fin 2 → ℝ :=
  softGate (chargedScore R n) P₁.pref P₁.τ P₁.δ

/-- At charge zero the score-side gate is the rebuttal run's gate at the same market. -/
theorem scoreGate_zero (σ : Sentence) (n : ℕ) :
    scoreGate (scoreSide σ 0) n = P₁.gate (fun j => WB.market DP n (F5.ι j)) := by
  have hb : (fun j => WB.market DP n (F5.ι j)) = Problem.priceR WB DP n := rfl
  rw [hb]
  unfold scoreGate Problem.gate
  congr 1
  funext q
  simp [chargedScore, scoreSide]

lemma shortfallPrice_nonneg (σ : Sentence) (ϖ : ℝ) (n : ℕ) :
    0 ≤ shortfallPrice (scoreSide σ ϖ) n := by
  show 0 ≤ WB.market DP n σ
  rw [WarrantSchedule.market_eq_quote_cast]
  exact_mod_cast (WB.quoteAt_mem_Icc DP n σ).1

lemma priceVec_le_one (n : ℕ) (j : Fin 5) : WB.priceVec DP n j ≤ 1 :=
  (WB.quoteAt_mem_Icc DP n _).2

lemma scoreR_act (n : ℕ) :
    P₁.scoreR (Problem.priceR WB DP n) 0 = ((WB.priceVec DP n XAY : ℚ) : ℝ) := by
  simp [Problem.scoreR, P₁, eXAY, Problem.priceR, Fin.sum_univ_five, Fixture2.X, Fixture2.XA,
    Fixture2.XAY, Fixture2.Y, Fixture2.Z]

lemma scoreR_refrain (n : ℕ) :
    P₁.scoreR (Problem.priceR WB DP n) 1 =
      ((WB.priceVec DP n XA : ℚ) : ℝ) - ((WB.priceVec DP n XAY : ℚ) : ℝ) := by
  simp [Problem.scoreR, P₁, eXA_XAY, Problem.priceR, Fin.sum_univ_five, Fixture2.X, Fixture2.XA,
    Fixture2.XAY, Fixture2.Y, Fixture2.Z]
  ring

lemma charged_act (σ : Sentence) (ϖ : ℝ) (n : ℕ) :
    chargedScore (scoreSide σ ϖ) n 0 =
      ((WB.priceVec DP n XAY : ℚ) : ℝ) - ϖ * shortfallPrice (scoreSide σ ϖ) n := by
  simp [chargedScore, pS, scoreR_act, scoreSide]

lemma charged_refrain (σ : Sentence) (ϖ : ℝ) (n : ℕ) :
    chargedScore (scoreSide σ ϖ) n 1 =
      ((WB.priceVec DP n XA : ℚ) : ℝ) - ((WB.priceVec DP n XAY : ℚ) : ℝ) := by
  simp [chargedScore, pS, scoreR_refrain, scoreSide]

lemma ramp_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : ramp x = 0 := by
  unfold ramp
  exact max_eq_left ((min_le_right _ _).trans hx)

lemma excess_rowS4 (p : Fin 5 → ℚ) : excess rowS4 p = 2/3 * p XA - p XAY := by
  simp [excess, rowS4_a, rowS4_b, Fin.sum_univ_five, Fixture2.XA, Fixture2.XAY]
  ring

lemma excess_rowA4 (p : Fin 5 → ℚ) : excess rowA4 p = -(p XA) + 3/4 := by
  simp [excess, rowA4_a, rowA4_b, Fin.sum_univ_five, Fixture2.XA]
  ring

/-- **After the refutation, for every charge and every shortfall sentence, the score-side gate
refrains with certainty.**  The charge can only lower the acting score, already pinned below
`τ` by the enforced pin; refraining is uncharged and its score clears `τ + δ` by the enforced
applicability row. -/
theorem after (σ : Sentence) (ϖ : ℝ) (hϖ : 0 ≤ ϖ) :
    scoreGate (scoreSide σ ϖ) 9 0 = 0 ∧ scoreGate (scoreSide σ ϖ) 9 1 = 1 := by
  obtain ⟨-, hconf, -, -, -⟩ := inductor
  have hex := hconf 9 (enforced 9)
  have hA9 := hex _ memA9
  have hP9 := hex _ memPin9
  simp only at hA9 hP9
  rw [excess_rowA9] at hA9
  rw [excess_rowPinXAY] at hP9
  have ht : tol 9 = 1/400 := rfl
  rw [ht] at hA9 hP9
  have hXA : (3/4 - 1/400 : ℝ) ≤ ((WB.priceVec DP 9 XA : ℚ) : ℝ) := by
    have hq : (3/4 - 1/400 : ℚ) ≤ WB.priceVec DP 9 XA := by linarith
    have := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at this
    exact this
  have hXAY : ((WB.priceVec DP 9 XAY : ℚ) : ℝ) ≤ 1/400 := by
    have := (Rat.cast_le (K := ℝ)).mpr hP9
    push_cast at this
    exact this
  have hπ := shortfallPrice_nonneg σ ϖ 9
  have hτ : P₁.τ = 1/3 := rfl
  have hδ : P₁.δ = 1/12 := rfl
  have hpref : ∀ q, P₁.pref q = 1 := fun _ => rfl
  have hw0 : weight (chargedScore (scoreSide σ ϖ) 9) P₁.pref P₁.τ P₁.δ 0 = 0 := by
    unfold weight
    rw [charged_act, hτ, hδ, hpref, mul_one]
    apply ramp_eq_zero_of_nonpos
    apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num)
    nlinarith [mul_nonneg hϖ hπ]
  have hw1 : weight (chargedScore (scoreSide σ ϖ) 9) P₁.pref P₁.τ P₁.δ 1 = 1 := by
    unfold weight
    rw [charged_refrain, hτ, hδ, hpref, mul_one, ramp_eq_one]
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have htot : total (chargedScore (scoreSide σ ϖ) 9) P₁.pref P₁.τ P₁.δ = 1 := by
    unfold total
    rw [Fin.sum_univ_two, hw0, hw1, zero_add]
  constructor
  · show weight (chargedScore (scoreSide σ ϖ) 9) P₁.pref P₁.τ P₁.δ 0 /
      total (chargedScore (scoreSide σ ϖ) 9) P₁.pref P₁.τ P₁.δ = 0
    rw [hw0, zero_div]
  · show weight (chargedScore (scoreSide σ ϖ) 9) P₁.pref P₁.τ P₁.δ 1 /
      total (chargedScore (scoreSide σ ϖ) 9) P₁.pref P₁.τ P₁.δ = 1
    rw [hw1, htot, div_one]

/-- **Before the refutation, with the charge at most `19/240`, the score-side gate acts with
mass at least `24/25`.**  The enforced strength and applicability rows hold
`P(X∧A∧Y) ≥ 1/2 − 1/240` at the displayed price, which leaves exactly `19/240` above
`τ + δ = 5/12`; the refraining score is at most `1/3 + 1/400`, so its weight is at most
`3/100`.  The rebuttal run's reversal obtains on the same market with no row on conduct
enforced. -/
theorem before (σ : Sentence) (ϖ : ℝ) (_hϖ : 0 ≤ ϖ)
    (hsmall : ϖ * shortfallPrice (scoreSide σ ϖ) 4 ≤ 19/240) :
    (24/25 : ℝ) ≤ scoreGate (scoreSide σ ϖ) 4 0 := by
  obtain ⟨-, hconf, -, -, -⟩ := inductor
  have hex := hconf 4 (enforced 4)
  have hS4 := hex _ memS4
  have hA4 := hex _ memA4
  simp only at hS4 hA4
  rw [excess_rowS4] at hS4
  rw [excess_rowA4] at hA4
  have ht : tol 4 = 1/400 := rfl
  rw [ht] at hS4 hA4
  have hle := priceVec_le_one 4 XA
  have hXAY : (1/2 - 1/240 : ℝ) ≤ ((WB.priceVec DP 4 XAY : ℚ) : ℝ) := by
    have hq : (1/2 - 1/240 : ℚ) ≤ WB.priceVec DP 4 XAY := by linarith
    have := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at this
    exact this
  have href : ((WB.priceVec DP 4 XA : ℚ) : ℝ) - ((WB.priceVec DP 4 XAY : ℚ) : ℝ) ≤
      1/3 + 1/400 := by
    have hq : WB.priceVec DP 4 XA - WB.priceVec DP 4 XAY ≤ 1/3 + 1/400 := by linarith
    have := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at this
    exact this
  have hτ : P₁.τ = 1/3 := rfl
  have hδ : P₁.δ = 1/12 := rfl
  have hpref : ∀ q, P₁.pref q = 1 := fun _ => rfl
  have hw0 : weight (chargedScore (scoreSide σ ϖ) 4) P₁.pref P₁.τ P₁.δ 0 = 1 := by
    unfold weight
    rw [charged_act, hτ, hδ, hpref, mul_one, ramp_eq_one]
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hw1 : weight (chargedScore (scoreSide σ ϖ) 4) P₁.pref P₁.τ P₁.δ 1 ≤ 3/100 := by
    unfold weight
    rw [charged_refrain, hτ, hδ, hpref, mul_one]
    refine (ramp_le _).trans ?_
    apply max_le (by norm_num)
    rw [div_le_iff₀ (by norm_num)]
    linarith
  have hw1' : 0 ≤ weight (chargedScore (scoreSide σ ϖ) 4) P₁.pref P₁.τ P₁.δ 1 :=
    weight_nonneg P₁.pref_nonneg 1
  have htot : total (chargedScore (scoreSide σ ϖ) 4) P₁.pref P₁.τ P₁.δ =
      1 + weight (chargedScore (scoreSide σ ϖ) 4) P₁.pref P₁.τ P₁.δ 1 := by
    unfold total
    rw [Fin.sum_univ_two, hw0]
  show (24/25 : ℝ) ≤ weight (chargedScore (scoreSide σ ϖ) 4) P₁.pref P₁.τ P₁.δ 0 /
    total (chargedScore (scoreSide σ ϖ) 4) P₁.pref P₁.τ P₁.δ
  rw [hw0, htot, le_div_iff₀ (by linarith)]
  linarith

/-- **The charge can override the act without touching a price.**  When `ϖ` times the shortfall
price reaches the acting score's room above `τ`, the acting option's weight is zero.  Nothing
about `P(X∧A∧Y)` changed; the obligation bound on the score. -/
theorem override (σ : Sentence) (ϖ : ℝ)
    (hbig : P₁.scoreR (Problem.priceR WB DP 4) 0 - P₁.τ ≤ ϖ * shortfallPrice (scoreSide σ ϖ) 4) :
    scoreGate (scoreSide σ ϖ) 4 0 = 0 := by
  have h0 : chargedScore (scoreSide σ ϖ) 4 0 - P₁.τ ≤ 0 := by
    rw [charged_act, ← scoreR_act]; linarith
  have hr : ramp ((chargedScore (scoreSide σ ϖ) 4 0 - P₁.τ) / P₁.δ) = 0 :=
    ramp_eq_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg h0 P₁.δ_pos.le)
  show weight (chargedScore (scoreSide σ ϖ) 4) P₁.pref P₁.τ P₁.δ 0 /
    total (chargedScore (scoreSide σ ϖ) 4) P₁.pref P₁.τ P₁.δ = 0
  unfold weight
  rw [hr, zero_mul, zero_div]

/-- **The same question, in the two realizations.**  On prices with no obligation on conduct:
the rebuttal run's `same_question`.  On the score with the obligation charged: acting with mass
at least `24/25` at date `4` while the charge is at most `19/240`, and refraining with
certainty at date `9` for every charge. -/
theorem same_question_two_realizations (σ : Sentence) (ϖ : ℝ) (hϖ : 0 ≤ ϖ)
    (hsmall : ϖ * shortfallPrice (scoreSide σ ϖ) 4 ≤ 19/240) :
    ((24/25 : ℝ) ≤ P₁.gate (fun j => WB.market DP 4 (F5.ι j)) 0 ∧
      P₁.gate (fun j => WB.market DP 9 (F5.ι j)) 0 = 0 ∧
      P₁.gate (fun j => WB.market DP 9 (F5.ι j)) 1 = 1) ∧
    ((24/25 : ℝ) ≤ scoreGate (scoreSide σ ϖ) 4 0 ∧
      scoreGate (scoreSide σ ϖ) 9 0 = 0 ∧ scoreGate (scoreSide σ ϖ) 9 1 = 1) :=
  ⟨same_question, before σ ϖ hϖ hsmall, after σ ϖ hϖ⟩

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.ShortfallAt
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.shortfall_assessed
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.conductRow
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.memS4
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.memA4
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.conductCert
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.conduct_on_prices_conflicts
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.conduct_on_prices_idle
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.scoreSide
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.bundle_unchanged
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.market_unchanged
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.pinRow_b
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.bundle_row_b_ne
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.no_conduct_row
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.shortfallPrice
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.pS
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.chargedScore
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.scoreGate
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.scoreGate_zero
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.shortfallPrice_nonneg
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.priceVec_le_one
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.scoreR_act
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.scoreR_refrain
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.charged_act
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.charged_refrain
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.ramp_eq_zero_of_nonpos
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.excess_rowS4
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.excess_rowA4
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.after
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.before
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.override
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.same_question_two_realizations

end Workspace.Normativity.Contrib.WarrantInductorScoreSide

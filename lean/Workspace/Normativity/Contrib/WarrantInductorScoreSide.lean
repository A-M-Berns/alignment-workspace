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
account carries a live leaf (`ShortfallAt`, read off the state accounted at that date; the run's
state is `state₀` at every date) — with one shortfall sentence per date and the named hypothesis
`Assessed`: the valuation that settles those sentences makes the date-`n` sentence true iff
`ShortfallAt n`.  The obligation is realized two ways on the *same* market history.

* **On prices** (§2) it compiles to the row `P(X∧A∧Y) ≤ τ`.  At date `4` that row conflicts
  with the strength and applicability rows: a three-row Farkas certificate (`conductCert`)
  refutes the region (`conduct_on_prices_conflicts`), so a compiler returning it withholds the
  whole date and the epistemic rows lose their force with it.  At date `9` the row is implied
  by the pin and adds nothing (`conduct_on_prices_idle`).
* **On the score** (§3) the realization stores the run's schedule, so its bundle and market are
  the run's by construction (`bundle_unchanged`; `market_unchanged` is `rfl` — a design fact,
  since the charge adds no trader, and not a result), the row *refrain* was compiled to is
  held at no date (`no_conduct_row`), and the obligation reaches the decision as a charge `ϖ`
  times the market's price of the date's shortfall sentence, subtracted from the acting score
  — the shape of `BRIACorrigibility.evalOf`, gated by `GatedChoice.softGate` with the run's
  problem parameters.  Under `Assessed`: after the refutation the gate refrains with certainty
  for every nonnegative charge, acting being a shortfall there (`after`); before it, the gate
  acts with mass at least `24/25` whenever `ϖ` times the shortfall price is at most `19/240`,
  the room the enforced rows leave above `τ + δ`, although acting is a shortfall there too
  (`before`) — the obligation binds through the charge and nothing else; when the charge
  reaches the acting score's room above `τ`, the acting option's weight is zero and no price
  has moved (`override`).
* **The strength row is necessary** (§4).  At the price vector `p₀ = (1, 3/4, 0, 0, 3/4)`, in
  the cube and satisfying every date-4 row except the specialized strength row, the charged
  gate puts mass `0` on acting and `1` on refraining for every nonnegative charge
  (`strength_row_necessary`): `before` rests on that row, and this is the witness that it
  cannot be dropped.

So the reversal obtains with no row on conduct enforced and needs the strength row, and the
obligation on conduct binds on the score, scaled by `ϖ` and the priced sentence an assessment
settles.  Not shown: that the market prices the shortfall sentences well, or that they are
generable; `Assessed` is a hypothesis.

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
open Workspace.Normativity.Contrib.OpenIntegrityEvolution (ObligationState)
open Workspace.Normativity.Contrib.OpenIntegrityEvolution.Witness (state₀ wAnchor)
open Workspace.Normativity.Contrib.OccurrenceIntegrity (Initial)
open Workspace.Normativity.Contrib.OccurrenceIntegrity.Witness (start protocol)
open Workspace.Normativity.Contrib.EndToEndWitness.Run (n₁ nE cP cA cS settlementAt occP occA occS)
open Finset

/-! ## 1. The obligation on conduct -/

/-- The state accounted at date `n` of the rebuttal run.  It is `state₀` at every date — the
run's entitlement `entitlementB n` is over `state₀` throughout — so the argument records which
date the obligation is read at and nothing else. -/
def stateAt (_n : ℕ) : ObligationState protocol wAnchor := state₀

lemma stateAt_exposed (n : ℕ) : (0 : Fin 2) ∈ (stateAt n).boundary.exposed := by
  simp [stateAt, state₀, Initial.state, start]

/-- **What the assessment settles**: acting at date `n` is a shortfall iff the originating
account — occurrence `0`, the origin of the first warrant's occurrences in
`WarrantInductorWitness.entitlement` — carries a live leaf in the state accounted at `n`.  An
evaluation settles this, not the deductive process. -/
def ShortfallAt (n : ℕ) : Prop :=
  OccurrenceIntegrity.Fate.live ∈ ((stateAt n).account 0 (stateAt_exposed n)).fates

/-- In `state₀` the originating account is live at every date, so acting is a shortfall
throughout: the obligation binds at date `4` as much as at date `9`. -/
theorem shortfall_assessed (n : ℕ) : ShortfallAt n := account_live 0 _

/-- **Refrain while live** (provisional name): the smallest obligation on conduct the fixture
lacks.  `shortfall n` is the sentence the market prices for the event "acting at date `n` will
be assessed a shortfall": the application's, as the shortfall and taint events are in
`DecisionComponent`.  What ties it to the assessment is `Assessed`. -/
structure RefrainWhileLive where
  shortfall : ℕ → Sentence

/-- **`Assessed`** (provisional name): the hypothesis tying the shortfall sentences to the
assessment.  The valuation `v` — the world in which the assessment settles the sentences —
makes `O.shortfall n` true iff `ShortfallAt n`.  Named, not derived: nothing here says that
the market prices these sentences well, or that they are generable. -/
def Assessed (O : RefrainWhileLive) (v : PCWorld) : Prop :=
  ∀ n, v.Holds (O.shortfall n) ↔ ShortfallAt n

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
rows their force.  This is the chosen compilation of *refrain*; nothing is shown about other
rows the obligation might compile to. -/
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
and the charge `ϖ` per unit price of the date's shortfall sentence. -/
structure ScoreSide where
  schedule : WarrantSchedule 5
  obligation : RefrainWhileLive
  ϖ : ℝ

/-- The realization this module runs: the rebuttal run's own schedule, stored. -/
def scoreSide (O : RefrainWhileLive) (ϖ : ℝ) : ScoreSide := ⟨WB, O, ϖ⟩

/-- **The enforcer's bundle is the rebuttal run's at every date** — by construction, since
`scoreSide` stores `WB`. -/
theorem bundle_unchanged (O : RefrainWhileLive) (ϖ : ℝ) (n : ℕ) :
    (scoreSide O ϖ).schedule.bundle n = (NB n).bundle := bundle_eq n

/-- **The market is the rebuttal run's, by construction.**  `scoreSide` stores `WB`, so this is
`rfl`: a design fact — the charge reads prices and adds no trader, the shape of
`DecisionComponent.noninterference` — and not a result.  It does not show that two
independently built markets coincide. -/
theorem market_unchanged (O : RefrainWhileLive) (ϖ : ℝ) :
    (scoreSide O ϖ).schedule.market DP = WB.market DP := rfl

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

/-- **The row *refrain* was compiled to is held at no date**: no row the score-side
realization's enforcer holds is `conductRow`.  This is about that one row; it is not a
classification of every row on conduct, of which the forms have no constructor. -/
theorem no_conduct_row (O : RefrainWhileLive) (ϖ : ℝ) (n : ℕ) :
    ∀ c ∈ (scoreSide O ϖ).schedule.bundle n, c.row ≠ conductRow := by
  intro c hc heq
  exact bundle_row_b_ne n hc (by rw [heq]; rfl)

/-- The price of the date-`n` shortfall sentence at date `n`: the realization's market, on the
obligation's sentence for that date. -/
noncomputable def shortfallPrice (R : ScoreSide) (n : ℕ) : ℝ :=
  R.schedule.market DP n (R.obligation.shortfall n)

/-- The priced shortfall over the menu: acting may be assessed a shortfall; refraining never
is, since the obligation is to refrain. -/
noncomputable def pS (R : ScoreSide) (n : ℕ) : Fin 2 → ℝ := ![shortfallPrice R n, 0]

/-- **The charged score**: the rebuttal run's score less `ϖ` times the priced shortfall — the
shape of `BRIACorrigibility.evalOf` (a bid less `ϖ` per priced event), with no structurally
recognized violation. -/
noncomputable def chargedScore (R : ScoreSide) (n : ℕ) (q : Fin 2) : ℝ :=
  P₁.scoreR (Problem.priceR R.schedule DP n) q - R.ϖ * pS R n q

/-- **The score-side gate**: `GatedChoice.softGate` on the charged scores, with the problem's
preference, threshold and ramp. -/
noncomputable def scoreGate (R : ScoreSide) (n : ℕ) : Fin 2 → ℝ :=
  softGate (chargedScore R n) P₁.pref P₁.τ P₁.δ

/-- At charge zero the score-side gate is the rebuttal run's gate at the same market. -/
theorem scoreGate_zero (O : RefrainWhileLive) (n : ℕ) :
    scoreGate (scoreSide O 0) n = P₁.gate (fun j => WB.market DP n (F5.ι j)) := by
  have hb : (fun j => WB.market DP n (F5.ι j)) = Problem.priceR WB DP n := rfl
  rw [hb]
  unfold scoreGate Problem.gate
  congr 1
  funext q
  simp [chargedScore, scoreSide]

lemma shortfallPrice_nonneg (O : RefrainWhileLive) (ϖ : ℝ) (n : ℕ) :
    0 ≤ shortfallPrice (scoreSide O ϖ) n := by
  show 0 ≤ WB.market DP n (O.shortfall n)
  rw [WarrantSchedule.market_eq_quote_cast]
  exact_mod_cast (WB.quoteAt_mem_Icc DP n _).1

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

lemma charged_act (O : RefrainWhileLive) (ϖ : ℝ) (n : ℕ) :
    chargedScore (scoreSide O ϖ) n 0 =
      ((WB.priceVec DP n XAY : ℚ) : ℝ) - ϖ * shortfallPrice (scoreSide O ϖ) n := by
  simp [chargedScore, pS, scoreR_act, scoreSide]

lemma charged_refrain (O : RefrainWhileLive) (ϖ : ℝ) (n : ℕ) :
    chargedScore (scoreSide O ϖ) n 1 =
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

/-- **After the refutation, for every nonnegative charge, the score-side gate refrains with
certainty, and acting is assessed a shortfall there.**  The charge can only lower the acting
score, already pinned below `τ` by the enforced pin; refraining is uncharged and its score
clears `τ + δ` by the enforced applicability row.  `Assessed` supplies the first conjunct. -/
theorem after (O : RefrainWhileLive) (v : PCWorld) (hA : Assessed O v) (ϖ : ℝ) (hϖ : 0 ≤ ϖ) :
    v.Holds (O.shortfall 9) ∧
      scoreGate (scoreSide O ϖ) 9 0 = 0 ∧ scoreGate (scoreSide O ϖ) 9 1 = 1 := by
  refine ⟨(hA 9).2 (shortfall_assessed 9), ?_⟩
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
  have hπ := shortfallPrice_nonneg O ϖ 9
  have hτ : P₁.τ = 1/3 := rfl
  have hδ : P₁.δ = 1/12 := rfl
  have hpref : ∀ q, P₁.pref q = 1 := fun _ => rfl
  have hw0 : weight (chargedScore (scoreSide O ϖ) 9) P₁.pref P₁.τ P₁.δ 0 = 0 := by
    unfold weight
    rw [charged_act, hτ, hδ, hpref, mul_one]
    apply ramp_eq_zero_of_nonpos
    apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num)
    nlinarith [mul_nonneg hϖ hπ]
  have hw1 : weight (chargedScore (scoreSide O ϖ) 9) P₁.pref P₁.τ P₁.δ 1 = 1 := by
    unfold weight
    rw [charged_refrain, hτ, hδ, hpref, mul_one, ramp_eq_one]
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have htot : total (chargedScore (scoreSide O ϖ) 9) P₁.pref P₁.τ P₁.δ = 1 := by
    unfold total
    rw [Fin.sum_univ_two, hw0, hw1, zero_add]
  constructor
  · show weight (chargedScore (scoreSide O ϖ) 9) P₁.pref P₁.τ P₁.δ 0 /
      total (chargedScore (scoreSide O ϖ) 9) P₁.pref P₁.τ P₁.δ = 0
    rw [hw0, zero_div]
  · show weight (chargedScore (scoreSide O ϖ) 9) P₁.pref P₁.τ P₁.δ 1 /
      total (chargedScore (scoreSide O ϖ) 9) P₁.pref P₁.τ P₁.δ = 1
    rw [hw1, htot, div_one]

/-- **Before the refutation, with `ϖ` times the shortfall price at most `19/240`, the
score-side gate acts with mass at least `24/25`, although acting is assessed a shortfall
there.**  The enforced strength and applicability rows hold `P(X∧A∧Y) ≥ 1/2 − 1/240` at the
displayed price, which leaves exactly `19/240` above `τ + δ = 5/12`; the refraining score is at
most `1/3 + 1/400`, so its weight is at most `3/100`.  The obligation binds through the charge
and nothing else: under this bound the reversal obtains on the same market with no row on
conduct enforced. -/
theorem before (O : RefrainWhileLive) (v : PCWorld) (hA : Assessed O v) (ϖ : ℝ)
    (hsmall : ϖ * shortfallPrice (scoreSide O ϖ) 4 ≤ 19/240) :
    v.Holds (O.shortfall 4) ∧ (24/25 : ℝ) ≤ scoreGate (scoreSide O ϖ) 4 0 := by
  refine ⟨(hA 4).2 (shortfall_assessed 4), ?_⟩
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
  have hw0 : weight (chargedScore (scoreSide O ϖ) 4) P₁.pref P₁.τ P₁.δ 0 = 1 := by
    unfold weight
    rw [charged_act, hτ, hδ, hpref, mul_one, ramp_eq_one]
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hw1 : weight (chargedScore (scoreSide O ϖ) 4) P₁.pref P₁.τ P₁.δ 1 ≤ 3/100 := by
    unfold weight
    rw [charged_refrain, hτ, hδ, hpref, mul_one]
    refine (ramp_le _).trans ?_
    apply max_le (by norm_num)
    rw [div_le_iff₀ (by norm_num)]
    linarith
  have hw1' : 0 ≤ weight (chargedScore (scoreSide O ϖ) 4) P₁.pref P₁.τ P₁.δ 1 :=
    weight_nonneg P₁.pref_nonneg 1
  have htot : total (chargedScore (scoreSide O ϖ) 4) P₁.pref P₁.τ P₁.δ =
      1 + weight (chargedScore (scoreSide O ϖ) 4) P₁.pref P₁.τ P₁.δ 1 := by
    unfold total
    rw [Fin.sum_univ_two, hw0]
  show (24/25 : ℝ) ≤ weight (chargedScore (scoreSide O ϖ) 4) P₁.pref P₁.τ P₁.δ 0 /
    total (chargedScore (scoreSide O ϖ) 4) P₁.pref P₁.τ P₁.δ
  rw [hw0, htot, le_div_iff₀ (by linarith)]
  linarith

/-- **The charge can override the act without touching a price.**  When `ϖ` times the shortfall
price reaches the acting score's room above `τ`, the acting option's weight is zero.  Nothing
about `P(X∧A∧Y)` changed; the obligation bound on the score. -/
theorem override (O : RefrainWhileLive) (ϖ : ℝ)
    (hbig : P₁.scoreR (Problem.priceR WB DP 4) 0 - P₁.τ ≤ ϖ * shortfallPrice (scoreSide O ϖ) 4) :
    scoreGate (scoreSide O ϖ) 4 0 = 0 := by
  have h0 : chargedScore (scoreSide O ϖ) 4 0 - P₁.τ ≤ 0 := by
    rw [charged_act, ← scoreR_act]; linarith
  have hr : ramp ((chargedScore (scoreSide O ϖ) 4 0 - P₁.τ) / P₁.δ) = 0 :=
    ramp_eq_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg h0 P₁.δ_pos.le)
  show weight (chargedScore (scoreSide O ϖ) 4) P₁.pref P₁.τ P₁.δ 0 /
    total (chargedScore (scoreSide O ϖ) 4) P₁.pref P₁.τ P₁.δ = 0
  unfold weight
  rw [hr, zero_mul, zero_div]

/-- **The same question, in the two realizations.**  On prices with no obligation on conduct:
the rebuttal run's `same_question`.  On the score with the obligation charged, under
`Assessed` and with `ϖ` times the date-4 shortfall price at most `19/240`: acting with mass at
least `24/25` at date `4` and refraining with certainty at date `9`, acting being assessed a
shortfall at both dates.  A conditional sufficiency result: the charge bound is a hypothesis,
and `strength_row_necessary` is the witness that the strength row cannot be dropped from the
rows it rests on. -/
theorem same_question_two_realizations (O : RefrainWhileLive) (v : PCWorld) (hA : Assessed O v)
    (ϖ : ℝ) (hϖ : 0 ≤ ϖ) (hsmall : ϖ * shortfallPrice (scoreSide O ϖ) 4 ≤ 19/240) :
    ((24/25 : ℝ) ≤ P₁.gate (fun j => WB.market DP 4 (F5.ι j)) 0 ∧
      P₁.gate (fun j => WB.market DP 9 (F5.ι j)) 0 = 0 ∧
      P₁.gate (fun j => WB.market DP 9 (F5.ι j)) 1 = 1) ∧
    ((24/25 : ℝ) ≤ scoreGate (scoreSide O ϖ) 4 0 ∧
      scoreGate (scoreSide O ϖ) 9 0 = 0 ∧ scoreGate (scoreSide O ϖ) 9 1 = 1) ∧
    (v.Holds (O.shortfall 4) ∧ v.Holds (O.shortfall 9)) :=
  ⟨same_question, ⟨(before O v hA ϖ hsmall).2, (after O v hA ϖ hϖ).2⟩,
    (before O v hA ϖ hsmall).1, (after O v hA ϖ hϖ).1⟩

/-! ## 4. The strength row is necessary -/

/-- The charged gate at a displayed price vector `p` with charge `κ` on acting: the soft gate
on the problem's scores less `κ` on the acting option. -/
noncomputable def gateAt (p : Fin 5 → ℚ) (κ : ℝ) : Fin 2 → ℝ :=
  softGate (fun q => P₁.scoreR (fun j => ((p j : ℚ) : ℝ)) q - κ * ![1, 0] q) P₁.pref P₁.τ P₁.δ

/-- The realized score-side gate at date `n` is `gateAt` at the displayed price vector, with
the charge `ϖ` times the shortfall price. -/
theorem scoreGate_eq_gateAt (O : RefrainWhileLive) (ϖ : ℝ) (n : ℕ) :
    scoreGate (scoreSide O ϖ) n =
      gateAt (WB.priceVec DP n) (ϖ * shortfallPrice (scoreSide O ϖ) n) := by
  unfold scoreGate gateAt
  congr 1
  funext q
  have hp : Problem.priceR WB DP n = fun j => ((WB.priceVec DP n j : ℚ) : ℝ) := rfl
  simp only [chargedScore, scoreSide, pS]
  rw [hp]
  fin_cases q <;> simp <;> ring

/-- The date-4 price vector with the acting credence at zero: `X = 1`, `X∧A = 3/4`,
`X∧A∧Y = 0`, `Y = 0`, `Z = 3/4`. -/
def p₀ : Fin 5 → ℚ := ![1, 3/4, 0, 0, 3/4]

theorem p₀_inCube : InCube p₀ := by
  intro i; fin_cases i <;> simp [p₀] <;> norm_num

/-- `p₀` satisfies every row of the date-4 bundle other than the specialized strength row. -/
theorem p₀_sat_without_strength : ∀ c ∈ (NB 4).bundle, c.row ≠ rowS4 → c.row.Sat p₀ := by
  intro c hc hne
  rcases ((NB 4).mem_bundle_iff c).1 hc with ⟨o, ho, rfl⟩ | ⟨it, hit, rfl⟩ | ⟨i, r, hr, rfl⟩
  · simp only [NB_settlement] at hne ⊢
    rw [survivors_eq] at ho
    simp only [show (4 : ℕ) < nE from by decide, if_true, List.singleton_append, List.mem_cons,
      List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · norm_num [specialize, settledTerm, settlementAt, occP, Fixture2.occP, Form.row, Row.Sat,
        Fin.sum_univ_five, truth, cP, p₀, show n₁ ≤ 4 from by decide,
        show ¬ nE ≤ 4 from by decide, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y,
        Fixture2.Z] <;> simp +decide <;> norm_num
    · norm_num [specialize, settledTerm, settlementAt, occA, Fixture2.occA, Form.row, Row.Sat,
        Fin.sum_univ_five, truth, cA, p₀, show n₁ ≤ 4 from by decide,
        show ¬ nE ≤ 4 from by decide, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y,
        Fixture2.Z] <;> simp +decide <;> norm_num
    · exact absurd rfl hne
    · norm_num [specialize, settledTerm, settlementAt, occZ, Fixture2.occZ, Form.row, Row.Sat,
        Fin.sum_univ_five, truth, Workspace.Normativity.Contrib.WarrantInductorWitness.cZ, p₀,
        show n₁ ≤ 4 from by decide, show ¬ nE ≤ 4 from by decide, Fixture2.X, Fixture2.XA,
        Fixture2.XAY, Fixture2.Y, Fixture2.Z] <;> simp +decide <;> norm_num
  · simp only [NB_settlement]
    rw [liveStr_eq] at hit
    simp only [structural, List.mem_cons, List.not_mem_nil, or_false] at hit
    rcases hit with rfl | rfl | rfl <;>
      norm_num [specialize, settledTerm, settlementAt, coh₁, coh₂, coh₃, Row.Sat,
        Fin.sum_univ_five, truth, p₀, show n₁ ≤ 4 from by decide, show ¬ nE ≤ 4 from by decide]
  · simp only [NB_settlement] at hr ⊢
    refine (Settlement.pinRowsAt_sat_iff _ i p₀).2 ?_ r hr
    intro b hb
    fin_cases i <;> simp [settlementAt, show n₁ ≤ 4 from by decide,
      show ¬ nE ≤ 4 from by decide] at hb <;> subst hb <;> simp [p₀, truth]

/-- `p₀` violates the specialized strength row: `2/3 · 3/4 ≤ 0` fails. -/
theorem p₀_violates_strength : ¬ rowS4.Sat p₀ := by
  norm_num [Row.Sat, rowS4_a, rowS4_b, Fin.sum_univ_five, p₀]

/-- **Without the strength row the reversal is lost.**  `p₀` lies in the cube, satisfies every
date-4 row but the specialized strength row, and violates that one; at `p₀` the charged gate
puts mass `0` on acting and `1` on refraining for every nonnegative charge.  The realized
decision differs, whatever the charge: `before` rests on the strength row through the enforced
conformance of `rowS4`, and this is the witness that the row cannot be dropped.  The bundle
without the strength row is a weaker hypothesis package, and this point satisfies it. -/
theorem strength_row_necessary :
    InCube p₀ ∧ (∀ c ∈ (NB 4).bundle, c.row ≠ rowS4 → c.row.Sat p₀) ∧ ¬ rowS4.Sat p₀ ∧
    ∀ κ : ℝ, 0 ≤ κ → gateAt p₀ κ 0 = 0 ∧ gateAt p₀ κ 1 = 1 := by
  refine ⟨p₀_inCube, p₀_sat_without_strength, p₀_violates_strength, fun κ hκ => ?_⟩
  have hs0 : P₁.scoreR (fun j => ((p₀ j : ℚ) : ℝ)) 0 = 0 := by
    simp [Problem.scoreR, P₁, eXAY, Fin.sum_univ_five, p₀]
  have hs1 : P₁.scoreR (fun j => ((p₀ j : ℚ) : ℝ)) 1 = 3/4 := by
    norm_num [Problem.scoreR, P₁, eXA_XAY, Fin.sum_univ_five, p₀]
  have hτ : P₁.τ = 1/3 := rfl
  have hδ : P₁.δ = 1/12 := rfl
  have hpref : ∀ q, P₁.pref q = 1 := fun _ => rfl
  set b : Fin 2 → ℝ := fun q => P₁.scoreR (fun j => ((p₀ j : ℚ) : ℝ)) q - κ * ![1, 0] q with hb
  have hb0 : b 0 = -κ := by simp [hb, hs0]
  have hb1 : b 1 = 3/4 := by simp [hb, hs1]
  have hw0 : weight b P₁.pref P₁.τ P₁.δ 0 = 0 := by
    unfold weight
    rw [hb0, hτ, hδ, hpref, mul_one]
    apply ramp_eq_zero_of_nonpos
    apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num)
    linarith
  have hw1 : weight b P₁.pref P₁.τ P₁.δ 1 = 1 := by
    unfold weight
    rw [hb1, hτ, hδ, hpref, mul_one, ramp_eq_one]
    rw [le_div_iff₀ (by norm_num)]
    norm_num
  have htot : total b P₁.pref P₁.τ P₁.δ = 1 := by
    unfold total
    rw [Fin.sum_univ_two, hw0, hw1, zero_add]
  constructor
  · show weight b P₁.pref P₁.τ P₁.δ 0 / total b P₁.pref P₁.τ P₁.δ = 0
    rw [hw0, zero_div]
  · show weight b P₁.pref P₁.τ P₁.δ 1 / total b P₁.pref P₁.τ P₁.δ = 1
    rw [hw1, htot, div_one]

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.stateAt
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.stateAt_exposed
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.ShortfallAt
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.shortfall_assessed
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.Assessed
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
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.gateAt
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.scoreGate_eq_gateAt
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.p₀
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.p₀_inCube
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.p₀_sat_without_strength
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.p₀_violates_strength
#print axioms Workspace.Normativity.Contrib.WarrantInductorScoreSide.strength_row_necessary

end Workspace.Normativity.Contrib.WarrantInductorScoreSide

/-
# The enforcement trader is a legal trading strategy

`Contrib.TraderizedEnforcement` proves the force algebra over an abstract pairing.
This file exhibits the term that algebra is about: for a finite presentation of a
price region by exact rational rows, a `LogicalInduction.Strategy n` whose exact
rational value against a payout table is *the same number* the abstract
inequalities bound.

Three facts make the term legal rather than merely definable.

* **Rank.** Every coefficient is built from `price φ n` and rational constants, so
  its `EF.rank` is at most `n`: the strategy sees the day-`n` prices and nothing
  later.  This is the framework's information-time discipline, and it is what
  forbids the intensities from reacting to the violation the market maker will go
  on to realize — the intensities are `EF.const` leaves of a term that is a
  function of the presentation and the date alone, with no market history among
  its arguments.
* **Finiteness.** The traded support is the presentation's coordinate list.
* **Continuity.** Coefficients denote continuous functions of the history, which is
  the hypothesis Brouwer is applied to in the fixed-point lemma.

There is no rational-approximation gap to quantify: the market maker's displayed
prices are exactly rational (`RationalBeliefState.quote`) and world payouts are
exactly `{0,1}`, so `Strategy.marketValueRat` *is* the value and the `ℚ`-valued
algebra applies on the nose.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.TraderizedEnforcement
import LogicalInduction.Construction.TradingFirm

namespace Workspace.Normativity.Contrib.EnforcementStrategy

open LogicalInduction
open Workspace.Normativity.Contrib.TraderizedEnforcement

/-! ## Presentations -/

/-- One exact rational row `⟪coeff, ·⟫ ≥ rhs` of a price region, carried with the
intensity the compiler enforces it at. -/
structure Row where
  /-- The row normal. -/
  coeff : Sentence → ℚ
  /-- The row's right-hand side. -/
  rhs : ℚ
  /-- The intensity the row is enforced at. -/
  intensity : ℚ
  /-- Intensities are nonnegative. -/
  intensity_nonneg : 0 ≤ intensity

/-- A **presentation**: a duplicate-free list of priced sentences and a list of
rows over them.  The rows are a list rather than a set because the presentation
identity is the multiset of exact rational rows — duplicating a row changes the
emitted force. -/
structure Presentation where
  /-- The priced sentences the presentation constrains. -/
  coordList : List Sentence
  /-- Each priced sentence is listed once. -/
  coord_nodup : coordList.Nodup
  /-- The rows. -/
  rows : List Row

namespace Presentation

/-- The coordinate set the abstract algebra sums over. -/
def coords (pres : Presentation) : Finset Sentence := pres.coordList.toFinset

/-- A sum over the coordinate set is the sum over the coordinate list. -/
lemma sum_coords (pres : Presentation) (f : Sentence → ℚ) :
    ∑ φ ∈ pres.coords, f φ = (pres.coordList.map f).sum :=
  List.sum_toFinset f pres.coord_nodup

/-- The row at an index. -/
def rowAt (pres : Presentation) (i : Fin pres.rows.length) : Row := pres.rows.get i

/-- The indexed normal family. -/
def normals (pres : Presentation) : Fin pres.rows.length → Sentence → ℚ :=
  fun i => (pres.rowAt i).coeff

/-- The indexed right-hand sides. -/
def rhss (pres : Presentation) : Fin pres.rows.length → ℚ := fun i => (pres.rowAt i).rhs

/-- The indexed intensities. -/
def intensities (pres : Presentation) : Fin pres.rows.length → ℚ :=
  fun i => (pres.rowAt i).intensity

lemma intensities_nonneg (pres : Presentation) :
    ∀ i ∈ (Finset.univ : Finset (Fin pres.rows.length)), 0 ≤ pres.intensities i :=
  fun i _ => (pres.rowAt i).intensity_nonneg

/-- The row index set the abstract algebra sums over. -/
abbrev rowIndex (pres : Presentation) : Finset (Fin pres.rows.length) := Finset.univ

/-- The compiled position: the abstract `ζ_E` at the presentation's data. -/
def compiledPosition (pres : Presentation) (p : Sentence → ℚ) : Sentence → ℚ :=
  position pres.rowIndex pres.coords pres.normals pres.rhss pres.intensities p

/-- The row violation the abstract algebra reads. -/
def rowViolation (pres : Presentation) (i : Fin pres.rows.length) (p : Sentence → ℚ) : ℚ :=
  violation pres.coords (pres.normals i) (pres.rhss i) p

end Presentation

/-! ## The compiled features -/

/-- Rational-semantics recursion, packaged for rewriting. -/
private lemma denoteRat_const (q : ℚ) (V : ℕ → Sentence → ℚ) :
    (EF.const q).denoteRat V = q := rfl

private lemma denoteRat_price (φ : Sentence) (n : ℕ) (V : ℕ → Sentence → ℚ) :
    (EF.price φ n).denoteRat V = V n φ := rfl

private lemma denoteRat_mul (a b : EF) (V : ℕ → Sentence → ℚ) :
    (a.mul b).denoteRat V = a.denoteRat V * b.denoteRat V := rfl

private lemma denoteRat_add (a b : EF) (V : ℕ → Sentence → ℚ) :
    (a.add b).denoteRat V = a.denoteRat V + b.denoteRat V := rfl

private lemma denoteRat_max (a b : EF) (V : ℕ → Sentence → ℚ) :
    (a.max b).denoteRat V = Max.max (a.denoteRat V) (b.denoteRat V) := rfl

private lemma denoteRat_neg (e : EF) (V : ℕ → Sentence → ℚ) :
    (EF.neg e).denoteRat V = -e.denoteRat V := by
  rw [EF.neg, denoteRat_mul, denoteRat_const]
  ring

private lemma sumFeatures_denoteRat (es : List EF) (V : ℕ → Sentence → ℚ) :
    (ROIBudget.sumFeatures es).denoteRat V = (es.map fun e => e.denoteRat V).sum := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      change e.denoteRat V + (ROIBudget.sumFeatures es).denoteRat V =
        e.denoteRat V + (es.map fun e => e.denoteRat V).sum
      rw [ih]

/-- The row's pairing against the day-`n` prices, as a feature. -/
def priceCombo (pres : Presentation) (row : Row) (n : ℕ) : EF :=
  ROIBudget.sumFeatures (pres.coordList.map fun φ =>
    .mul (.const (row.coeff φ)) (.price φ n))

/-- The row's violation at the day-`n` prices, as a feature. -/
def violationFeature (pres : Presentation) (row : Row) (n : ℕ) : EF :=
  .max (.const 0) (.add (.const row.rhs) (EF.neg (priceCombo pres row n)))

/-- The coefficient the compiled trader puts on `φ`: the intensity-weighted,
violation-weighted sum of the rows' `φ`-components. -/
def coefficientFeature (pres : Presentation) (n : ℕ) (φ : Sentence) : EF :=
  ROIBudget.sumFeatures (List.ofFn fun i : Fin pres.rows.length =>
    .mul (.const (pres.intensities i * pres.normals i φ))
      (violationFeature pres (pres.rowAt i) n))

/-! ### Rank: the strategy sees no price later than its own day -/

lemma priceCombo_rank_le (pres : Presentation) (row : Row) (n : ℕ) :
    (priceCombo pres row n).rank ≤ n := by
  apply ROIBudget.sumFeatures_rank_le
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨φ, _, rfl⟩ := he
  simp [EF.rank]

lemma violationFeature_rank_le (pres : Presentation) (row : Row) (n : ℕ) :
    (violationFeature pres row n).rank ≤ n := by
  simp only [violationFeature, EF.neg, EF.rank_max, EF.rank_add, EF.rank_const,
    EF.rank_mul, Nat.zero_max]
  exact priceCombo_rank_le pres row n

lemma coefficientFeature_rank_le (pres : Presentation) (n : ℕ) (φ : Sentence) :
    (coefficientFeature pres n φ).rank ≤ n := by
  apply ROIBudget.sumFeatures_rank_le
  intro e he
  simp only [List.mem_ofFn] at he
  obtain ⟨i, rfl⟩ := he
  simp only [EF.rank_mul, EF.rank_const, Nat.zero_max]
  exact violationFeature_rank_le pres (pres.rowAt i) n

/-! ## The strategy -/

/-- **The enforcement strategy.**  One trade per priced sentence, at the
violation-weighted coefficient.  A `def`, not a `noncomputable def`: the term is
finite data computed from the presentation and the date. -/
def enforcementStrategy (pres : Presentation) (n : ℕ) : Strategy n where
  trades := pres.coordList.map fun φ => (coefficientFeature pres n φ, φ)
  rank_le := by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨φ, _, rfl⟩ := hp
    exact coefficientFeature_rank_le pres n φ

/-- The traded support is the presentation's coordinate set. -/
theorem enforcementStrategy_support (pres : Presentation) (n : ℕ) :
    (enforcementStrategy pres n).support = pres.coords := by
  ext φ
  simp only [enforcementStrategy, Strategy.support, Presentation.coords,
    Finset.mem_image, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨ψ, hψ, rfl⟩ := hp
    exact hψ
  · intro hφ
    exact ⟨(coefficientFeature pres n φ, φ), ⟨φ, hφ, rfl⟩, rfl⟩

/-- Coefficients denote continuous functions of the market history — the property
the fixed-point lemma applies Brouwer to. -/
theorem coefficientFeature_continuous (pres : Presentation) (n : ℕ) (φ : Sentence) :
    Continuous (coefficientFeature pres n φ).denote :=
  EF.continuous_denote _

/-! ## The value identity

The bridge to `Contrib.TraderizedEnforcement`: the strategy's exact rational value
against a payout table is the abstract pairing of the compiled position with the
displacement from the displayed price. -/

lemma priceCombo_denoteRat (pres : Presentation) (row : Row) (n : ℕ)
    (Q : ℕ → Sentence → ℚ) :
    (priceCombo pres row n).denoteRat Q = pair pres.coords row.coeff (Q n) := by
  rw [priceCombo, sumFeatures_denoteRat, List.map_map, pair, pres.sum_coords]
  apply congrArg List.sum
  apply List.map_congr_left
  intro φ _
  simp only [Function.comp_apply]
  rw [denoteRat_mul, denoteRat_const, denoteRat_price]

lemma violationFeature_denoteRat (pres : Presentation) (row : Row) (n : ℕ)
    (Q : ℕ → Sentence → ℚ) :
    (violationFeature pres row n).denoteRat Q =
      violation pres.coords row.coeff row.rhs (Q n) := by
  rw [violationFeature, denoteRat_max, denoteRat_const, denoteRat_add,
    denoteRat_const, denoteRat_neg, priceCombo_denoteRat, violation]
  congr 1
  ring

lemma coefficientFeature_denoteRat (pres : Presentation) (n : ℕ)
    (Q : ℕ → Sentence → ℚ) (φ : Sentence) :
    (coefficientFeature pres n φ).denoteRat Q = pres.compiledPosition (Q n) φ := by
  rw [coefficientFeature, sumFeatures_denoteRat, List.map_ofFn, List.sum_ofFn,
    Presentation.compiledPosition, position]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply]
  rw [denoteRat_mul, denoteRat_const,
    violationFeature_denoteRat pres (pres.rowAt i) n Q]
  simp only [Presentation.normals, Presentation.rhss, Presentation.intensities]
  ring

/-- **The compiled trader really is the compiled position.**  Its exact rational
value against a payout table `w` is the abstract pairing of `ζ_E` with `w − P_n`,
so every inequality in `Contrib.TraderizedEnforcement` is an inequality about this
`Strategy n`. -/
theorem marketValueRat_enforcementStrategy (pres : Presentation) (n : ℕ)
    (Q : ℕ → Sentence → ℚ) (w : Sentence → ℚ) :
    (enforcementStrategy pres n).marketValueRat Q w =
      pair pres.coords (pres.compiledPosition (Q n)) (fun φ => w φ - Q n φ) := by
  rw [Strategy.marketValueRat, enforcementStrategy, List.map_map, pair,
    pres.sum_coords]
  apply congrArg List.sum
  apply List.map_congr_left
  intro φ _
  simp only [Function.comp_apply]
  rw [coefficientFeature_denoteRat]

/-- The real-valued form: what the market maker's contract and the exploitation
criterion actually read. -/
theorem value_enforcementStrategy (pres : Presentation) (n : ℕ) (P : History)
    (Q : ℕ → Sentence → ℚ) (hQ : ∀ day φ, P day φ = (Q day φ : ℝ))
    (w : Sentence → ℚ) :
    (enforcementStrategy pres n).value P (fun φ => (w φ : ℝ)) =
      ((pair pres.coords (pres.compiledPosition (Q n)) (fun φ => w φ - Q n φ) : ℚ) : ℝ) := by
  rw [← marketValueRat_enforcementStrategy]
  exact (enforcementStrategy pres n).value_eq_marketRatCast P Q hQ
    (fun φ => (w φ : ℝ)) w (fun _ => rfl)

/-! ## Conformance at the real contract

The value identity plus the abstract master inequality.  `M` is the *ordinary
aggregate's* volume bound; the semantic credal set does not appear. -/

/-- **Finite-time row conformance.** -/
theorem weighted_square_le_slack_add_volume_at_strategy (pres : Presentation)
    (n : ℕ) (Q : ℕ → Sentence → ℚ) (x τ : Sentence → ℚ) (ε M : ℚ)
    (hx : ∀ i ∈ pres.rowIndex, pres.rhss i ≤ pair pres.coords (pres.normals i) x)
    (hcontract : pair pres.coords
      (fun φ => pres.compiledPosition (Q n) φ + τ φ) (fun φ => x φ - Q n φ) ≤ ε)
    (hτ : -M ≤ pair pres.coords τ (fun φ => x φ - Q n φ)) :
    ∑ i ∈ pres.rowIndex, pres.intensities i * pres.rowViolation i (Q n) ^ 2 ≤ ε + M :=
  weighted_square_le_slack_add_volume pres.intensities_nonneg hx hcontract hτ

/-- **Per-row tolerance.**  Choosing the intensity at least `(ε + M)/δ²` on a row
forces that row's violation below `δ` at the displayed price.

The hypothesis `0 < ε + M` is load-bearing and is not decoration: at `ε + M = 0`
the intensity condition is satisfied by `β = 0`, which enforces nothing.  In the
source market it is automatic — the market maker's slack `ε_n = 2^{-(n+1)}` is
strictly positive at every date. -/
theorem rowViolation_le_of_intensity_ge (pres : Presentation) (n : ℕ)
    (Q : ℕ → Sentence → ℚ) (ε M δ : ℚ) (hδ : 0 < δ) (hEM : 0 < ε + M)
    (hbound : ∑ i ∈ pres.rowIndex,
      pres.intensities i * pres.rowViolation i (Q n) ^ 2 ≤ ε + M)
    (i : Fin pres.rows.length) (hβ : (ε + M) / δ ^ 2 ≤ pres.intensities i) :
    pres.rowViolation i (Q n) ≤ δ := by
  have hgnn : 0 ≤ pres.rowViolation i (Q n) :=
    violation_nonneg _ _ _ _
  have hδ2 : (0 : ℚ) < δ ^ 2 := by positivity
  have hβpos : 0 < pres.intensities i :=
    lt_of_lt_of_le (div_pos hEM hδ2) hβ
  have hterm : pres.intensities i * pres.rowViolation i (Q n) ^ 2 ≤ ε + M := by
    refine le_trans (Finset.single_le_sum
      (f := fun j : Fin pres.rows.length =>
        pres.intensities j * pres.rowViolation j (Q n) ^ 2)
      (fun j _ => mul_nonneg (pres.rowAt j).intensity_nonneg (sq_nonneg _))
      (Finset.mem_univ i)) hbound
  have hβδ : ε + M ≤ pres.intensities i * δ ^ 2 := (div_le_iff₀ hδ2).mp hβ
  have hsq : pres.rowViolation i (Q n) ^ 2 ≤ δ ^ 2 := by
    have h := hterm.trans hβδ
    exact le_of_mul_le_mul_left (by linarith [h]) hβpos
  nlinarith [hgnn, hδ.le, hsq]

/-! ## Inhabitation

One priced sentence, one row `P(φ) ≥ 1/2` at intensity `4`, displayed price `1/4`.
The violation is `1/4`, the compiled position is `1` share, and the value at the
world where `φ` is true is `3/4`. -/

/-- A witness presentation. -/
def witnessPresentation (φ : Sentence) : Presentation where
  coordList := [φ]
  coord_nodup := List.nodup_singleton φ
  rows := [{ coeff := fun ψ => if ψ = φ then 1 else 0
             rhs := 1 / 2
             intensity := 4
             intensity_nonneg := by norm_num }]

theorem enforcementStrategy_is_nonvacuous (φ : Sentence) :
    ((enforcementStrategy (witnessPresentation φ) 0).trades.length = 1) ∧
    (enforcementStrategy (witnessPresentation φ) 0).marketValueRat
        (fun _ _ => 1 / 4) (fun _ => 1) = 3 / 4 ∧
    (witnessPresentation φ).rowViolation ⟨0, by simp [witnessPresentation]⟩
        (fun _ => 1 / 4) = 1 / 4 := by
  refine ⟨by simp [enforcementStrategy, witnessPresentation], ?_, ?_⟩
  · rw [marketValueRat_enforcementStrategy]
    simp [pair, Presentation.coords, Presentation.compiledPosition, position,
      violation, witnessPresentation, Presentation.normals, Presentation.rhss,
      Presentation.intensities, Presentation.rowAt]
    norm_num
  · simp [Presentation.rowViolation, violation, pair, Presentation.coords,
      witnessPresentation, Presentation.normals, Presentation.rhss,
      Presentation.rowAt]
    norm_num

end Workspace.Normativity.Contrib.EnforcementStrategy

#print axioms Workspace.Normativity.Contrib.EnforcementStrategy.Presentation.sum_coords
#print axioms Workspace.Normativity.Contrib.EnforcementStrategy.coefficientFeature_rank_le
#print axioms Workspace.Normativity.Contrib.EnforcementStrategy.enforcementStrategy
#print axioms Workspace.Normativity.Contrib.EnforcementStrategy.enforcementStrategy_support
#print axioms Workspace.Normativity.Contrib.EnforcementStrategy.coefficientFeature_continuous
#print axioms Workspace.Normativity.Contrib.EnforcementStrategy.priceCombo_denoteRat
#print axioms Workspace.Normativity.Contrib.EnforcementStrategy.violationFeature_denoteRat
#print axioms Workspace.Normativity.Contrib.EnforcementStrategy.coefficientFeature_denoteRat
#print axioms Workspace.Normativity.Contrib.EnforcementStrategy.marketValueRat_enforcementStrategy
#print axioms Workspace.Normativity.Contrib.EnforcementStrategy.value_enforcementStrategy
#print axioms Workspace.Normativity.Contrib.EnforcementStrategy.weighted_square_le_slack_add_volume_at_strategy
#print axioms Workspace.Normativity.Contrib.EnforcementStrategy.rowViolation_le_of_intensity_ge
#print axioms Workspace.Normativity.Contrib.EnforcementStrategy.enforcementStrategy_is_nonvacuous

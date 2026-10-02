import Cleanroom.Corrigibility.CorrLandscape.Trichotomy
import Cleanroom.Corrigibility.CorrLandscape.Regret
import Cleanroom.Corrigibility.CorrTrajectory.Corruption
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# `corr-landscape` — `Erosion`: the erosion inequality, the stock, (H-decay), the switch, the `β_t` law (T16)

`landscape-final.md` Statement 5(c), D5, D6′, P5, E2 ([[corr-wf14b-inventory]] 065) and the dialogue:

* (a) D6′'s resist set is non-increasing in `k̂` (`Map.erodes_antitone`); check C's two cells: at
  `p_push = 1/10`, `π̂ = 1/10`, `c = 1`, `h = 4` the push-time rule resists iff `k̂ < 1/2`, the anticipatory
  rule iff `k̂ < 1/20` (the source's "for all `k̂ ≤ 0.5`" / "stops at `0.05`" are these strict bounds).
* (b) E2's stock instances: the objective per-class stock `7/4` (two classes `7/2`); the agent with
  `λ̂ = 1/50` on both has `k̂ = 0` (its conditioned rule equals *none* on both signals, `π̂(1) = 9/58 < 1/5`)
  and erodes at believed gain `1/4`; `λ̂ = (1/50, 1/2)` gives `k̂ = 7/4`, no erosion; one future class
  with `h = 100` gives `k̂ = 851/500` at `λ̂ = 1/50`, no erosion.
* (c) **(H-decay) as an exact characterization**: every stock term is `≥ 0` because the conditioned rule is
  the Bayes rule under the agent's own law (T13), so for positive `p_j` the stock is `0` iff on every
  future class every positive-mass signal has `π̂ ≤ q` — resist or tie everywhere (`stock_zero_iff`,
  `none_eq_bayes_iff`); the `h = 100` cell is the contrapositive.
* (d) **The switch condition**: the sufficient direction
  `ℓ*(Bayes) + (c+h)δ + |k̂ − k| < (1 − λ)c ⟹ ℓ*(cond) < ℓ*(absolute)` (`switch_sufficient`, C over T15
  and T13), and the **refutation** of the dialogue's "iff `δ < (1−λ)c/(c+h)`" (wentworth-judge l. 101,
  `judge_checks.py`): Toy T pause stakes at `λ = 7/10` has `π*(0) = 7/34 > q`, so the Bayes rule *is*
  absolute acceptance and no rule at all — in particular no conditioned rule at any `δ`, covered or
  not — is strictly better, while `(1−λ)c/(c+h) = 3/50 > 0` (`switch_iff_refuted`).
* (e) **The `β_t` law of motion** under the fresh-draw kernel (wentworth-respondent item 2,
  `selection_drift.py`): the mass `∝ 1/(εv)` is stationary and its `β_stat = 27/55 < 3/5` (`fresh_stationary`);
  the compliance inequality survives the drift at `h/c = 4` (`compliance_survives_drift`); the
  no-replacement cohort's `β_t` is antitone with limit `min v = 3/10` (`cohortBeta_antitone`,
  `cohortBeta_tendsto`); the lineage-preserving kernel leaves `β` constant (`lineage_const`, T).
-/

namespace Cleanroom.Corrigibility.CorrLandscape

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrTrajectory
open Corruption (oddsIneq)
open Finset hiding expect
open Filter Topology

set_option linter.unusedSectionVars false

namespace Erosion

open Map Trichotomy Regret

/-! ## (a) check C -/

/-- **Check C**: at `p_push = 1/10`, `π̂ = 1/10`, `c = 1`, `h = 4` the push-time rule resists iff `k̂ < 1/2`
and the anticipatory rule iff `k̂ < 1/20`.
Source: [[corr-wf14b-inventory]] 065 / landscape-final.md D6′ (check C)
Kind: N+
Fidelity: exact (strict bounds; the source's "for all `k̂ ≤ 0.5`" is the grid reading of `k̂ < 1/2`)
Hyps: (a) only -/
theorem checkC (kh : ℝ) :
    (erodes 1 (1 / 10) 1 4 kh ↔ kh < 1 / 2) ∧ (erodes (1 / 10) (1 / 10) 1 4 kh ↔ kh < 1 / 20) := by
  unfold erodes; constructor <;> constructor <;> intro H <;> linarith

/-! ## (b) E2's stock instances -/

/-- The agent's believed law at `λ̂ = 1/50`, detector `(1/10, 9/10)`.
Source: landscape-final.md E2 ("Agent with `λ̂ = 0.02`")
Kind: D
Fidelity: n/a (witness) -/
noncomputable def toyLow : Distr (Bool × Bool) :=
  detectorLaw (1 / 50) (1 / 10) (9 / 10) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩

/-- `toyLow` masses. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toyLow_mass : legMass toyLow true = 9 / 500 ∧ legMass toyLow false = 1 / 500 ∧
    nonlegMass toyLow true = 49 / 500 ∧ nonlegMass toyLow false = 441 / 500 := by
  simp [toyLow, detectorLaw, legMass, nonlegMass]; norm_num

/-- **E2's per-class losses**: at `λ̂ = 1/50` the believed Bayes rule equals *none* on both signals
(`π̂(1) = 9/58 < 1/5`), so `ℓ̂(none) = ℓ̂(cond) = 2/25` at `h = 4`; at `h = 100` the believed Bayes rule
accepts `s = 1` and `ℓ̂(none) = 2`, `ℓ̂(cond) = 149/500`.
Source: [[corr-wf14b-inventory]] 065 / landscape-final.md E2 ("its conditioned rule equals *none* on
both signals, since `π̂(1) = 0.155 < 0.2`"; "`k̂ = 1.70` at `λ̂ = 0.02`")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem toyLow_losses :
    piStar toyLow true = 9 / 58 ∧
      loss toyLow noneRule 1 4 0 = 2 / 25 ∧ loss toyLow (bayesRule toyLow 1 4 0) 1 4 0 = 2 / 25 ∧
      loss toyLow noneRule 1 100 0 = 2 ∧ loss toyLow (bayesRule toyLow 1 100 0) 1 100 0 = 149 / 500 := by
  obtain ⟨h1, h2, h3, h4⟩ := toyLow_mass
  have b4t : bayesRule toyLow 1 4 0 true = true := by simp [bayesRule, qk, sigMass, h1, h3]; norm_num
  have b4f : bayesRule toyLow 1 4 0 false = true := by simp [bayesRule, qk, sigMass, h2, h4]; norm_num
  have b100t : bayesRule toyLow 1 100 0 true = false := by simp [bayesRule, qk, sigMass, h1, h3]; norm_num
  have b100f : bayesRule toyLow 1 100 0 false = true := by simp [bayesRule, qk, sigMass, h2, h4]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [piStar, sigMass, h1, h3]; norm_num
  · rw [loss_none]; simp [lam, Fintype.sum_bool, h1, h2]; norm_num
  · simp [loss, Fintype.sum_bool, b4t, b4f, cost, sigMass, h1, h2, h3, h4]; norm_num
  · rw [loss_none]; simp [lam, Fintype.sum_bool, h1, h2]; norm_num
  · simp [loss, Fintype.sum_bool, b100t, b100f, cost, sigMass, h1, h2, h3, h4]; norm_num

/-- **E2's stocks and erosion decisions**: objective `k = 7/4` per class (`7/2` for two); `k̂ = 0` at
`λ̂ = 1/50` on both and the agent erodes (believed gain `1/4 > 0`); `k̂ = 7/4` at `λ̂ = (1/50, 1/2)`, no
erosion; `k̂ = 851/500` for one `h = 100` class at `λ̂ = 1/50`, no erosion.
Source: [[corr-wf14b-inventory]] 065 / landscape-final.md E2, R3
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem e2_stocks :
    loss toyMixed noneRule 1 4 0 - loss toyMixed (bayesRule toyMixed 1 4 0) 1 4 0 = 7 / 4 ∧
      stock ![1, 1] ![2, 2] ![1 / 4, 1 / 4] = 7 / 2 ∧
      stock ![1, 1] ![2 / 25, 2 / 25] ![2 / 25, 2 / 25] = 0 ∧ erodes (1 / 2) (1 / 10) 1 4 0 ∧
      stock ![1, 1] ![2 / 25, 2] ![2 / 25, 1 / 4] = 7 / 4 ∧ ¬ erodes (1 / 2) (1 / 10) 1 4 (7 / 4) ∧
      stock ![1] ![2] ![149 / 500] = 851 / 500 ∧ ¬ erodes (1 / 2) (1 / 10) 1 4 (851 / 500) := by
  obtain ⟨a, n, b, -, -⟩ := toyMixed_cells
  refine ⟨by rw [n, b]; norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [stock, erodes, Fin.sum_univ_two, Fin.sum_univ_one] <;> norm_num

/-! ## (c) (H-decay) as an exact characterization -/

/-- **`ℓ*(none) = ℓ*(Bayes)` iff resist-or-tie everywhere**: on every positive-mass signal,
`μ(s, L) ≤ q_k P*(s)` (the tie accepts at equal cost, so the iff is `≤`, not `<`).
Source: [[corr-wf14b-inventory]] 065 / landscape-final.md Statement 5(c) (H-decay); mandate T16(c)
Kind: P
Fidelity: exact
Hyps: (a) `0 < c + h` -/
theorem none_eq_bayes_iff {S : Type} [Fintype S] [DecidableEq S] (μ : Distr (S × Bool)) {c h : ℝ} (k : ℝ)
    (hch : 0 < c + h) :
    loss μ noneRule c h k = loss μ (bayesRule μ c h k) c h k ↔
      ∀ s, 0 < sigMass μ s → legMass μ s ≤ qk c h k * sigMass μ s := by
  constructor
  · intro heq s hpos
    by_contra hcon
    rw [not_le] at hcon
    have := loss_bayes_lt_none μ k hch ⟨s, hcon⟩
    linarith
  · intro hle
    unfold loss
    refine sum_congr rfl fun s _ => ?_
    rcases (sigMass_nonneg μ s).lt_or_eq with hpos | hzero
    · by_cases hlt : legMass μ s < qk c h k * sigMass μ s
      · simp [bayesRule, hlt, noneRule]
      · have key := cost_true_sub_false μ k hch s
        have heq : legMass μ s = qk c h k * sigMass μ s := le_antisymm (hle s hpos) (not_lt.1 hlt)
        simp only [bayesRule, hlt, decide_false, noneRule]
        rw [heq] at key
        linarith
    · rw [cost_eq_zero_of_sigMass_eq_zero μ c h k _ hzero.symm,
        cost_eq_zero_of_sigMass_eq_zero μ c h k _ hzero.symm]

/-- Every stock term is nonnegative when the per-class rule is the believed Bayes rule.
Source: [[corr-wf14b-inventory]] 065 / landscape-final.md Statement 5(c); mandate T16(c)
Kind: L
Fidelity: exact -/
theorem stock_nonneg {n : ℕ} (p lnone lcond : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hle : ∀ j, lcond j ≤ lnone j) : 0 ≤ stock p lnone lcond :=
  sum_nonneg fun j _ => mul_nonneg (hp j) (sub_nonneg.2 (hle j))

/-- **(H-decay), the stock half**: with positive push probabilities and `ℓ̂_j(cond) ≤ ℓ̂_j(none)`, the stock
is `0` iff every term is.
Source: [[corr-wf14b-inventory]] 065 / landscape-final.md Statement 5(c) ("`k̂ ≈ 0` requires …")
Kind: P
Fidelity: exact (the source's "≈ 0" made exact at `= 0`)
Hyps: (a) only -/
theorem stock_zero_iff {n : ℕ} (p lnone lcond : Fin n → ℝ) (hp : ∀ j, 0 < p j)
    (hle : ∀ j, lcond j ≤ lnone j) : stock p lnone lcond = 0 ↔ ∀ j, lnone j = lcond j := by
  constructor
  · intro h0 j
    have hterms : ∀ i ∈ (univ : Finset (Fin n)), 0 ≤ p i * (lnone i - lcond i) :=
      fun i _ => mul_nonneg (hp i).le (sub_nonneg.2 (hle i))
    have := (sum_eq_zero_iff_of_nonneg hterms).1 h0 j (mem_univ _)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hp j).ne'
    · linarith
  · intro h
    unfold stock
    exact sum_eq_zero fun j _ => by rw [h j, sub_self, mul_zero]

/-- **(H-decay), composed**: for believed laws `μ̂_j` with positive push probabilities, the stock of
believed Bayes losses is `0` iff on every future class every positive-mass signal has
`μ̂_j(s, L) ≤ q P̂_j(s)` — resist or tie on every signal of every class. "Confidence alone does not empty
the channel when future stakes are large" is the contrapositive at `h = 100` (`toyLow_losses`).
Source: [[corr-wf14b-inventory]] 065 / landscape-final.md Statement 5(c); mandate T16(c)
Kind: C (`stock_zero_iff` over `none_eq_bayes_iff` with `loss_bayes_le`)
Fidelity: exact
Hyps: (a) only -/
theorem hdecay_iff {n : ℕ} {S : Type} [Fintype S] [DecidableEq S] (μh : Fin n → Distr (S × Bool))
    (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) {c h : ℝ} (k : ℝ) (hch : 0 < c + h) :
    stock p (fun j => loss (μh j) noneRule c h k) (fun j => loss (μh j) (bayesRule (μh j) c h k) c h k) = 0 ↔
      ∀ j s, 0 < sigMass (μh j) s → legMass (μh j) s ≤ qk c h k * sigMass (μh j) s := by
  rw [stock_zero_iff _ _ _ hp (fun j => loss_bayes_le (μh j) k hch _)]
  exact forall_congr' fun j => none_eq_bayes_iff (μh j) k hch

/-! ## (d) the switch condition -/

/-- **The sufficient direction of the switch**: covered at tolerance `δ` with
`ℓ*(Bayes) + (c+h)δ + |k̂ − k| < (1 − λ)c`, the conditioned row beats the absolute row.
Source: [[corr-wf14b-inventory]] 065; [[corr-wf14b-2-inventory]] 2-005 / wentworth-judge.md l. 101
("D1's crossover … belongs in Statement 6's neighbourhood")
Kind: C (`Regret.regret_le` with `Map.loss_absolute`)
Fidelity: exact
Hyps: (a) only -/
theorem switch_sufficient {S : Type} [Fintype S] [DecidableEq S] (μ : Distr (S × Bool)) (πh : S → ℝ)
    {c h : ℝ} (k kh δ : ℝ) (hch : 0 < c + h) (hδ : 0 ≤ δ) (hcov : covered πh μ δ)
    (hlt : loss μ (bayesRule μ c h k) c h k + (c + h) * δ + |kh - k| < (1 - lam μ) * c) :
    loss μ (conditionedRule πh kh c h) c h k < loss μ absoluteRule c h k := by
  rw [loss_absolute]
  linarith [regret_le μ πh k kh δ hch hδ hcov]

/-- Toy T pause stakes at `λ = 7/10`.
Source: landscape-final.md Toy T; mandate T16(d)
Kind: D
Fidelity: n/a (witness) -/
noncomputable def toySeven : Distr (Bool × Bool) :=
  detectorLaw (7 / 10) (1 / 10) (9 / 10) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩

/-- `toySeven` masses. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma toySeven_mass : legMass toySeven true = 63 / 100 ∧ legMass toySeven false = 7 / 100 ∧
    nonlegMass toySeven true = 3 / 100 ∧ nonlegMass toySeven false = 27 / 100 := by
  simp [toySeven, detectorLaw, legMass, nonlegMass]; norm_num

/-- **Refutation of the switch "iff"** — wentworth-judge l. 101 / `judge_checks.py`: "C-row wins iff
`δ < (1−λ)c/(c+h)`". At Toy T pause stakes, `λ = 7/10`: `π*(0) = 7/34 > q = 1/5`, so the Bayes rule is
absolute acceptance (`bayesRule = absoluteRule`), and **every rule whatsoever** — in particular every
conditioned rule at every `δ`, covered or not — has `ℓ*(r) ≥ ℓ*(absolute)`: no `δ` makes the conditioned
row strictly better, while the claimed bound `(1−λ)c/(c+h) = 3/50 > 0`. (The universal clause does not
need coverage: it is Statement 2 after `bayesRule = absoluteRule` — audit r1, N7/N9.) Reading
(ATTRIBUTION-UNVETTED, the judge's one-line formula with `ℓ*(Bayes)` dropped): "beats" as strict
improvement. Surviving neighbour: `switch_sufficient` and `Switch.two_signal_rule`.
Source: [[corr-wf14b-inventory]] 065 / wentworth-judge.md l. 101; `judge_checks.py` (3)
Kind: N+ (refutation row)
Fidelity: exact (stronger than the first version: no coverage hypothesis)
Hyps: (a) only -/
theorem switch_iff_refuted :
    piStar toySeven false = 7 / 34 ∧ (1 / 5 : ℝ) < 7 / 34 ∧
      bayesRule toySeven 1 4 0 = absoluteRule ∧
      (∀ r : Bool → Bool, loss toySeven absoluteRule 1 4 0 ≤ loss toySeven r 1 4 0) ∧
      (∀ (πh : Bool → ℝ) (δ : ℝ), 0 ≤ δ →
        loss toySeven absoluteRule 1 4 0 ≤ loss toySeven (conditionedRule πh 0 1 4) 1 4 0) ∧
      (1 - 7 / 10 : ℝ) * 1 / (1 + 4) = 3 / 50 := by
  obtain ⟨h1, h2, h3, h4⟩ := toySeven_mass
  have hb : bayesRule toySeven 1 4 0 = absoluteRule := by
    funext s
    cases s
    · simp [bayesRule, absoluteRule, qk, sigMass, h2, h4]; norm_num
    · simp [bayesRule, absoluteRule, qk, sigMass, h1, h3]; norm_num
  have hall : ∀ r : Bool → Bool, loss toySeven absoluteRule 1 4 0 ≤ loss toySeven r 1 4 0 := by
    intro r
    rw [← hb]
    exact loss_bayes_le toySeven 0 (by norm_num) r
  refine ⟨by simp [piStar, sigMass, h2, h4]; norm_num, by norm_num, hb, hall, ?_, by norm_num⟩
  intro πh _ _
  exact hall _

/-! ## (e) the `β_t` law of motion -/

/-- The three visibility classes `v ∈ {3/10, 3/5, 9/10}`.
Source: [[corr-wf14b-inventory]] 065 / wentworth-voice-scratch/selection_drift.py
Kind: D
Fidelity: exact -/
noncomputable def vis : Fin 3 → ℝ := ![3 / 10, 3 / 5, 9 / 10]

/-- **The fresh-draw kernel**: each class retires at rate `ε v` and the retired mass is redrawn uniformly
from the prior.
Source: [[corr-wf14b-inventory]] 065 / `selection_drift.py` (`step`); wentworth-respondent.md item 2
(kernel (A))
Kind: D
Fidelity: exact -/
noncomputable def freshStep (ε : ℝ) (m : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun v => m v * (1 - ε * vis v) + (∑ u, m u * ε * vis u) / 3

/-- The population mean visibility `β = ∑ v m_v`. Source: `selection_drift.py`. Kind: D. Fidelity: exact -/
noncomputable def popBeta (m : Fin 3 → ℝ) : ℝ := ∑ v, m v * vis v

/-- The stationary mass `∝ 1/v`: `(6/11, 3/11, 2/11)`.
Source: `selection_drift.py` ("mass `m_v ∝ 1/(eps*v)`")
Kind: D
Fidelity: exact -/
noncomputable def mstat : Fin 3 → ℝ := ![6 / 11, 3 / 11, 2 / 11]

/-- **The fresh-draw fixed point**: `mstat` is a probability vector, stationary under `freshStep (1/10)`,
with `β_stat = 27/55 < 3/5` (the prior mean) — `β` falls below the prior mean under replacement from the
prior.
Source: [[corr-wf14b-inventory]] 065 / wentworth-respondent.md B2 ("stationary `β = 0.491` from `0.600`");
`selection_drift.py` ("stationary beta: 0.4909 prior beta: 0.6")
Kind: P (small)
Fidelity: exact
Hyps: (a) only -/
theorem fresh_stationary :
    (∑ v, mstat v) = 1 ∧ freshStep (1 / 10) mstat = mstat ∧ popBeta mstat = 27 / 55 ∧
      (27 / 55 : ℝ) < 3 / 5 ∧ popBeta ![1 / 3, 1 / 3, 1 / 3] = 3 / 5 := by
  refine ⟨?_, ?_, ?_, by norm_num, ?_⟩
  · simp [mstat, Fin.sum_univ_three]; norm_num
  · funext v
    fin_cases v <;> simp [freshStep, mstat, vis, Fin.sum_univ_three] <;> norm_num
  · simp [popBeta, mstat, vis, Fin.sum_univ_three]; norm_num
  · simp [popBeta, vis, Fin.sum_univ_three]; norm_num

/-- **The compliance inequality survives the fresh-draw drift** at `h/c = 4`, `ε = 1/10`, `α = 1/20`,
`β = β_stat = 27/55`.
Source: [[corr-wf14b-inventory]] 065 / wentworth-respondent.md B2 ("the compliance inequality survives it
at `h/c = 4`")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem compliance_survives_drift : oddsIneq (1 / 20) (27 / 55) 4 1 (1 / 10) := by
  unfold oddsIneq; norm_num

/-- **The lineage-preserving kernel leaves `β` unchanged**: a successor with its line's visibility returns
the retired mass to its bin.
Source: [[corr-wf14b-inventory]] 065 / wentworth-respondent.md B2 (kernel (B))
Kind: T
Fidelity: exact -/
theorem lineage_const (m : Fin 3 → ℝ) (ε : ℝ) :
    popBeta (fun v => m v * (1 - ε * vis v) + m v * ε * vis v) = popBeta m := by
  unfold popBeta; refine sum_congr rfl fun v _ => by ring

/-- **The no-replacement cohort's `β_t`**: survivors only, `m_v(t) = m_v(0)(1 − εv)^t`, `β_t` the
normalized mean.
Source: [[corr-wf14b-inventory]] 065 / `selection_drift.py` ("no-replacement cohort")
Kind: D
Fidelity: exact -/
noncomputable def cohortBeta (t : ℕ) : ℝ :=
  (3 / 10 * (97 / 100 : ℝ) ^ t + 3 / 5 * (94 / 100 : ℝ) ^ t + 9 / 10 * (91 / 100 : ℝ) ^ t) /
    ((97 / 100 : ℝ) ^ t + (94 / 100 : ℝ) ^ t + (91 / 100 : ℝ) ^ t)

/-- The cohort's `β_t` is antitone: weight shifts to the less visible classes.
Source: [[corr-wf14b-inventory]] 065 / wentworth-judge.md B2 ("bounded below by the least visible class")
Kind: P (small)
Fidelity: exact
Hyps: (a) only -/
theorem cohortBeta_antitone : Antitone cohortBeta := by
  refine antitone_nat_of_succ_le fun t => ?_
  unfold cohortBeta
  have hx : 0 < (97 / 100 : ℝ) ^ t := by positivity
  have hy : 0 < (94 / 100 : ℝ) ^ t := by positivity
  have hz : 0 < (91 / 100 : ℝ) ^ t := by positivity
  simp only [pow_succ]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]

/-- **The cohort's `β_t → 3/10 = min v`**.
Source: [[corr-wf14b-inventory]] 065 / wentworth-judge.md B2 ("`β → 0.300`"); `judge_checks.py` (2)
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem cohortBeta_tendsto : Tendsto cohortBeta atTop (𝓝 (3 / 10)) := by
  have e : ∀ t, cohortBeta t =
      (3 / 10 + 3 / 5 * (94 / 97 : ℝ) ^ t + 9 / 10 * (91 / 97 : ℝ) ^ t) /
        (1 + (94 / 97 : ℝ) ^ t + (91 / 97 : ℝ) ^ t) := by
    intro t
    unfold cohortBeta
    have hx : 0 < (97 / 100 : ℝ) ^ t := by positivity
    have h1 : (94 / 100 : ℝ) ^ t = (94 / 97) ^ t * (97 / 100) ^ t := by rw [← mul_pow]; norm_num
    have h2 : (91 / 100 : ℝ) ^ t = (91 / 97) ^ t * (97 / 100) ^ t := by rw [← mul_pow]; norm_num
    rw [h1, h2]
    field_simp
  have hr1 : Tendsto (fun t : ℕ => (94 / 97 : ℝ) ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hr2 : Tendsto (fun t : ℕ => (91 / 97 : ℝ) ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hnum : Tendsto (fun t : ℕ => 3 / 10 + 3 / 5 * (94 / 97 : ℝ) ^ t + 9 / 10 * (91 / 97 : ℝ) ^ t) atTop
      (𝓝 (3 / 10 + 3 / 5 * 0 + 9 / 10 * 0)) :=
    (tendsto_const_nhds.add (hr1.const_mul _)).add (hr2.const_mul _)
  have hden : Tendsto (fun t : ℕ => 1 + (94 / 97 : ℝ) ^ t + (91 / 97 : ℝ) ^ t) atTop (𝓝 (1 + 0 + 0)) :=
    (tendsto_const_nhds.add hr1).add hr2
  have h := hnum.div hden (by norm_num)
  have h0 : (3 / 10 + 3 / 5 * (0 : ℝ) + 9 / 10 * 0) / (1 + 0 + 0) = 3 / 10 := by norm_num
  have h' : Tendsto cohortBeta atTop (𝓝 ((3 / 10 + 3 / 5 * (0 : ℝ) + 9 / 10 * 0) / (1 + 0 + 0))) :=
    h.congr fun t => (e t).symm
  rwa [h0] at h'

end Erosion

end Cleanroom.Corrigibility.CorrLandscape

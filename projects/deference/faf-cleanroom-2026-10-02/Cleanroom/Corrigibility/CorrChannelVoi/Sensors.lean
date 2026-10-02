import Cleanroom.Found.CorrThreeStep.Identities
import Cleanroom.Trust.TtFiniteFrames.Sensors
import Mathlib.Data.Fin.VecNotation

/-!
# `corr-channel-voi` — Sensors: channels as experiments, their value, and the bridge

Definitions of record D1–D3 of [[corr-channel-voi-mandate]]: the button as a finite experiment
(`buttonExperiment`), the trivial and perfect experiments, the conditionally independent product
of two experiments (`Experiment.prod`, an API request to `lit-ddb-frames`), the two-option
sensor value `sensorValue` *through* `lit-ddb-frames`'s `bayesValue` (so Blackwell monotonicity
is `tt-finite-frames`'s theorem, T8(a)), the value of information `voiSensor` and the value of
adding a channel `voiGiven`. General theorems: the sum-of-maxima form (`sensorValue_eq_sum_max`),
the perfect-information bound (T3, general `W`), Good's equality clause
(`voiSensor_eq_zero_iff`), and the bridge `voiButton2 = voiSensor button` under A1.

Everything is over FAF's `Distr` (the prior) and `lit-ddb-frames`'s `Experiment`; the two-state
closed forms are in `TwoStateForms`.
-/

namespace Cleanroom.Corrigibility.CorrChannelVoi

open Finset hiding expect
open FactoredSpaces
open Cleanroom.Found.LitDdbFrames.Blackwell
open Cleanroom.Trust.TtFiniteFrames
open Cleanroom.Found.CorrThreeStep

noncomputable section

set_option linter.unusedSectionVars false

variable {W W' S T : Type} [Fintype W] [Fintype W'] [Fintype S] [Fintype T]

/-! ## The simplex bridge and experiment plumbing -/

/-- The mass function of a FAF `Distr` lies in Mathlib's standard simplex (the prior format of
`bayesValue`).
Source: none: infrastructure ([[corr-channel-voi-mandate]] §Dependencies, "Bridge")
Kind: L
Fidelity: n/a -/
theorem distr_mem_stdSimplex (μ : Distr W) : μ.mass ∈ stdSimplex ℝ W :=
  ⟨μ.nonneg, μ.sum_eq_one⟩

/-- Two experiments with the same kernel are equal (the membership proof is a `Prop`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem experiment_ext {k₁ k₂ : Experiment W S} (h : k₁.k = k₂.k) : k₁ = k₂ := by
  cases k₁; cases k₂; simp only at h; subst h; rfl

/-- **The trivial experiment** ("no channel"): one signal, always sent.
Source: [[corr-channel-voi-mandate]] D1 (`trivialExp`)
Kind: D
Fidelity: exact -/
def trivialExp : Experiment W Unit where
  k := fun _ _ => 1
  k_mem := fun _ => ⟨fun _ => zero_le_one, by simp⟩

/-- **The perfect experiment**: the world revealed, `ofMap id`.
Source: [[corr-channel-voi-mandate]] D1 (`ofMap id` is the perfect experiment)
Kind: D
Fidelity: exact -/
abbrev perfectExp [DecidableEq W] : Experiment W W := ofMap id

/-- **Relabelling the states** of an experiment along `f : W' → W` (the kernel read through `f`).
Used to read `tt-finite-frames`'s `binarySensor` (states `Fin 2`) on `World`.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def expComap (f : W' → W) (k : Experiment W S) : Experiment W' S where
  k := fun w' => k.k (f w')
  k_mem := fun w' => k.k_mem (f w')

/-- Kernel of a relabelled experiment. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem expComap_k (f : W' → W) (k : Experiment W S) (w' : W') (s : S) :
    (expComap f k).k w' s = k.k (f w') s := rfl

/-- The Blackwell order is preserved by relabelling the states: the same garbling matrix works.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem blackwellLE_comap (f : W' → W) {k₁ : Experiment W S} {k₂ : Experiment W T}
    (h : BlackwellLE k₂ k₁) : BlackwellLE (expComap f k₂) (expComap f k₁) := by
  obtain ⟨g, hg, hgar⟩ := h
  exact ⟨g, hg, fun w' t => hgar (f w') t⟩

/-- **D2. The product of two experiments** (conditionally independent given the world):
`k w (s, t) = k₁ w s · k₂ w t`. API request to `lit-ddb-frames`.
Source: [[corr-channel-voi-mandate]] D2
Kind: D
Fidelity: exact -/
def expProd (k₁ : Experiment W S) (k₂ : Experiment W T) : Experiment W (S × T) where
  k := fun w p => k₁.k w p.1 * k₂.k w p.2
  k_mem := fun w => ⟨fun p => mul_nonneg ((k₁.k_mem w).1 p.1) ((k₂.k_mem w).1 p.2), by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, (k₂.k_mem w).2, mul_one]
    exact (k₁.k_mem w).2⟩

/-- Kernel of a product experiment. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem expProd_k (k₁ : Experiment W S) (k₂ : Experiment W T) (w : W)
    (p : S × T) : (expProd k₁ k₂).k w p = k₁.k w p.1 * k₂.k w p.2 := rfl

/-- Every experiment is a garbling of the trivial one's *refinement*: `trivialExp ≤ k` in the
Blackwell order (the garbling sends every signal to the one signal).
Source: none: infrastructure (Good's theorem's hypothesis-free half)
Kind: L
Fidelity: n/a -/
theorem blackwellLE_trivial (k : Experiment W S) : BlackwellLE trivialExp k :=
  ⟨fun _ _ => 1, fun _ => ⟨fun _ => zero_le_one, by simp⟩, fun w _ => by
    simp [trivialExp, (k.k_mem w).2]⟩

/-- Every experiment is Blackwell-below the perfect experiment (garble the revealed world through
the experiment's own kernel).
Source: [[corr-channel-voi-mandate]] T4(a) (general form: `BlackwellLE k (ofMap id)` for every `k`)
Kind: L
Fidelity: n/a -/
theorem blackwellLE_perfect [DecidableEq W] (k : Experiment W S) : BlackwellLE k perfectExp :=
  ⟨fun w s => k.k w s, fun w => k.k_mem w, fun w s => by
    simp [ofMap, Finset.sum_ite_eq]⟩

/-- The first factor is Blackwell-below the product: `k₁ ≤ prod k₁ k₂`.
Source: [[corr-channel-voi-mandate]] D2 (`BlackwellLE k₁ (prod k₁ k₂)`)
Kind: L
Fidelity: n/a -/
theorem blackwellLE_left_prod [DecidableEq S] (k₁ : Experiment W S) (k₂ : Experiment W T) :
    BlackwellLE k₁ (expProd k₁ k₂) := by
  refine ⟨fun p s => if p.1 = s then 1 else 0, fun p => ⟨fun s => by dsimp only; split_ifs <;> norm_num,
    by simp⟩, fun w s => ?_⟩
  simp only [expProd_k]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single s]
  · simp [← Finset.mul_sum, (k₂.k_mem w).2]
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (mem_univ _) h

/-- The second factor is Blackwell-below the product: `k₂ ≤ prod k₁ k₂`.
Source: [[corr-channel-voi-mandate]] D2
Kind: L
Fidelity: n/a -/
theorem blackwellLE_right_prod [DecidableEq T] (k₁ : Experiment W S) (k₂ : Experiment W T) :
    BlackwellLE k₂ (expProd k₁ k₂) := by
  refine ⟨fun p t => if p.2 = t then 1 else 0, fun p => ⟨fun t => by dsimp only; split_ifs <;> norm_num,
    by simp⟩, fun w t => ?_⟩
  simp only [expProd_k]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_eq_single t]
  · simp [← Finset.sum_mul, (k₁.k_mem w).2]
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (mem_univ _) h

/-- Adding the trivial channel adds nothing: `prod k₁ trivialExp ≤ k₁` (with `k₁ ≤ prod k₁ trivialExp`
from `blackwellLE_left_prod`, the two are Blackwell-equivalent).
Source: [[corr-channel-voi-mandate]] D2 (`prod k₁ trivialExp` is Blackwell-equivalent to `k₁`)
Kind: L
Fidelity: n/a -/
theorem blackwellLE_prod_trivial [DecidableEq S] (k₁ : Experiment W S) :
    BlackwellLE (expProd k₁ trivialExp) k₁ := by
  refine ⟨fun s p => if s = p.1 then 1 else 0, fun s => ⟨fun p => by dsimp only; split_ifs <;> norm_num,
    ?_⟩, fun w p => ?_⟩
  · rw [Fintype.sum_prod_type]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rw [Finset.sum_ite_eq]
    simp
  · simp [trivialExp, Finset.sum_ite_eq']

/-- **`prod k perfect` is Blackwell-equivalent to `perfect`**: the product is below perfect by
`blackwellLE_perfect`, and perfect is below the product by `blackwellLE_right_prod`. Packaged as
the pair, since the mandate names it as one fact.
Source: [[corr-channel-voi-mandate]] D2 (needed for "`VOI(button | perfect scan) = 0`")
Kind: L
Fidelity: n/a -/
theorem prod_perfect_equiv [DecidableEq W] (k : Experiment W S) :
    BlackwellLE (expProd k perfectExp) perfectExp ∧ BlackwellLE perfectExp (expProd k perfectExp) :=
  ⟨blackwellLE_perfect _, blackwellLE_right_prod k perfectExp⟩

/-! ## D1. The button as an experiment -/

/-- **D1. The button as an experiment**: signal `0 = press` with likelihood `press a ω`, signal
`1 = silence` with likelihood `1 − press a ω`.
Source: [[corr-channel-voi-mandate]] D1
Kind: D
Fidelity: exact -/
def buttonExperiment {Ω A₁ A₂ : Type} [Fintype Ω] [Fintype A₂] [DecidableEq A₂]
    (S : ThreeStep Ω A₁ A₂) (a : A₁) : Experiment Ω (Fin 2) where
  k := fun ω => ![S.press a ω, 1 - S.press a ω]
  k_mem := fun ω => ⟨fun s => by
      fin_cases s <;> simp <;> linarith [S.press_nonneg a ω, S.press_le_one a ω],
    by simp [Fin.sum_univ_two]⟩

/-- Kernel of the button at the press signal. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem buttonExperiment_k_zero {Ω A₁ A₂ : Type} [Fintype Ω] [Fintype A₂] [DecidableEq A₂]
    (S : ThreeStep Ω A₁ A₂) (a : A₁) (ω : Ω) : (buttonExperiment S a).k ω 0 = S.press a ω := rfl

/-- Kernel of the button at the silence signal. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem buttonExperiment_k_one {Ω A₁ A₂ : Type} [Fintype Ω] [Fintype A₂] [DecidableEq A₂]
    (S : ThreeStep Ω A₁ A₂) (a : A₁) (ω : Ω) : (buttonExperiment S a).k ω 1 = 1 - S.press a ω := rfl

/-! ## D3. Sensor value and value of information on the two-option menu -/

/-- The two-option menu `{continue, stop}` as a `bayesValue` menu: option `0` pays the stakes
`X`, option `1` pays `0`.
Source: [[corr-channel-voi-mandate]] D3
Kind: D
Fidelity: exact -/
def twoMenu (X : W → ℝ) : Fin 2 → W → ℝ := ![X, fun _ => 0]

/-- **D3. The sensor value** of an experiment for prior `μ` and stakes `X` (continue minus stop)
on the two-option menu, *through* `bayesValue`: `𝒱(k) = max_δ E[u(δ(s), w)]`. Blackwell
monotonicity is therefore `tt-finite-frames`'s theorem, not a property of a local formula.
Source: [[corr-channel-voi-mandate]] D3; substitution.md l. 27 (`𝒱(S)`)
Kind: D
Fidelity: exact (the sources' sum-of-maxima form is the theorem `sensorValue_eq_sum_max`) -/
def sensorValue [DecidableEq S] (μ : Distr W) (k : Experiment W S) (X : W → ℝ) : ℝ :=
  bayesValue μ.mass k (twoMenu X)

/-- The **signal gain** `∑ w, μ w · k w s · X w`: the product-form expectation of the stakes on
the event "signal `s`" (no division).
Source: [[corr-channel-voi-mandate]] D3 (the summand of `𝒱(S)`)
Kind: D
Fidelity: exact -/
def signalGain (μ : Distr W) (k : Experiment W S) (X : W → ℝ) (s : S) : ℝ :=
  ∑ w, μ.mass w * k.k w s * X w

/-- The signal gains sum to the prior expectation of the stakes (rows of `k` sum to one).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_signalGain (μ : Distr W) (k : Experiment W S) (X : W → ℝ) :
    ∑ s, signalGain μ k X s = expect μ X := by
  unfold signalGain expect
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [show ∑ s, μ.mass w * k.k w s * X w = μ.mass w * X w * ∑ s, k.k w s by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring]
  rw [(k.k_mem w).2, mul_one]

/-- The value of a two-option decision rule, signal by signal: the gain where the rule continues,
`0` where it stops.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ruleValue_twoMenu [DecidableEq S] (μ : Distr W) (k : Experiment W S) (X : W → ℝ)
    (δ : S → Fin 2) :
    ruleValue μ.mass k (twoMenu X) δ = ∑ s, if δ s = 0 then signalGain μ k X s else 0 := by
  rw [ruleValue_eq_sum_signals]
  refine Finset.sum_congr rfl fun s _ => ?_
  generalize hj : δ s = j
  fin_cases j
  · simp [twoMenu, signalGain]
  · simp [twoMenu]

/-- **The sum-of-maxima form**: `𝒱(k) = ∑ s, max(∑ w, μ w · k w s · X w, 0)` — the sources'
`𝒱(S) = ∑_s max(P(s) E[X | s], 0)` in product form, derived from `bayesValue` (the best rule
continues exactly on the signals of positive gain).
Source: [[corr-channel-voi-mandate]] D3 (`sensorValue_eq_sum_max`); substitution.md l. 27
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem sensorValue_eq_sum_max [DecidableEq S] (μ : Distr W) (k : Experiment W S) (X : W → ℝ) :
    sensorValue μ k X = ∑ s, max (signalGain μ k X s) 0 := by
  apply le_antisymm
  · apply bayesValue_le
    intro δ
    rw [ruleValue_twoMenu]
    apply Finset.sum_le_sum
    intro s _
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
  · have h := ruleValue_le_bayesValue μ.mass k (twoMenu X)
      (fun s => if 0 ≤ signalGain μ k X s then 0 else 1)
    rw [ruleValue_twoMenu] at h
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hs : 0 ≤ signalGain μ k X s
    · rw [if_pos hs, if_pos rfl, max_eq_left hs]
    · rw [if_neg hs, if_neg (by decide), max_eq_right (le_of_lt (not_le.mp hs))]

/-- **The value of information of a sensor** `VOI(k) = 𝒱(k) − max(E_μ[X], 0)`, on the two-option
menu.
Source: [[corr-channel-voi-mandate]] D3; substitution.md R2 item 5
Kind: D
Fidelity: exact -/
def voiSensor [DecidableEq S] (μ : Distr W) (k : Experiment W S) (X : W → ℝ) : ℝ :=
  sensorValue μ k X - max (expect μ X) 0

/-- **The value of adding a channel** `VOI(k₂ | k₁) = 𝒱(prod k₁ k₂) − 𝒱(k₁)`.
Source: [[corr-channel-voi-mandate]] D3; substitution.md R2 item 6 (`VOI(scan | button)`)
Kind: D
Fidelity: exact -/
def voiGiven [DecidableEq S] [DecidableEq T] (μ : Distr W) (k₁ : Experiment W S)
    (k₂ : Experiment W T) (X : W → ℝ) : ℝ :=
  sensorValue μ (expProd k₁ k₂) X - sensorValue μ k₁ X

/-- The trivial experiment is worth the best constant act: `𝒱(trivialExp) = max(E_μ[X], 0)`.
Source: [[corr-channel-voi-mandate]] T1 (`sensorValue trivialExp`)
Kind: L
Fidelity: exact -/
theorem sensorValue_trivial (μ : Distr W) (X : W → ℝ) :
    sensorValue μ trivialExp X = max (expect μ X) 0 := by
  rw [sensorValue_eq_sum_max]
  simp [signalGain, trivialExp, expect]

/-- `VOI(k) = 𝒱(k) − 𝒱(trivialExp)`: the value of information is the value of the channel over
no channel.
Source: [[corr-channel-voi-mandate]] D3
Kind: L
Fidelity: exact -/
theorem voiSensor_eq_sub_trivial [DecidableEq S] (μ : Distr W) (k : Experiment W S) (X : W → ℝ) :
    voiSensor μ k X = sensorValue μ k X - sensorValue μ trivialExp X := by
  rw [voiSensor, sensorValue_trivial]

/-- The perfect experiment is worth `E_μ[max(X, 0)]` (continue exactly in the worlds where the
stakes are positive).
Source: [[corr-channel-voi-mandate]] T1 (`sensorValue (ofMap id)`)
Kind: L
Fidelity: exact -/
theorem sensorValue_perfect [DecidableEq W] (μ : Distr W) (X : W → ℝ) :
    sensorValue μ perfectExp X = expect μ (fun w => max (X w) 0) := by
  rw [sensorValue_eq_sum_max]
  unfold expect
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : signalGain μ perfectExp X w = μ.mass w * X w := by
    simp [signalGain, ofMap, Finset.sum_ite_eq']
  rw [h, mul_max_of_nonneg _ _ (μ.nonneg w), mul_zero]

/-! ## T8(a). Blackwell monotonicity, through `tt-finite-frames` -/

/-- **T8(a). Blackwell monotonicity of the sensor value**: a garbling is worth no more,
`BlackwellLE k₂ k₁ → 𝒱(k₂) ≤ 𝒱(k₁)`, for every prior and stakes. This is
`tt-finite-frames`'s `moreValuable_of_blackwellLE` at the two-option menu.
Source: [[corr-core-inventory]] 012/013; [[corr-wf13-2-inventory]] 2-078 (1); miri.md I11.2(a) (Theorem 6.2)
Kind: C (Blackwell's easy direction from `tt-finite-frames`, plus the simplex bridge)
Fidelity: exact
Hyps: (a) none beyond the Blackwell hypothesis -/
theorem sensorValue_mono [DecidableEq S] [DecidableEq T] {k₁ : Experiment W S} {k₂ : Experiment W T}
    (h : BlackwellLE k₂ k₁) (μ : Distr W) (X : W → ℝ) :
    sensorValue μ k₂ X ≤ sensorValue μ k₁ X :=
  moreValuable_of_blackwellLE h μ.mass (distr_mem_stdSimplex μ) 1 (twoMenu X)

/-- **T8(a) for `VOI`**: `BlackwellLE k₂ k₁ → VOI(k₂) ≤ VOI(k₁)`.
Source: [[corr-core-inventory]] 012/013; miri.md I11.2(a)
Kind: L
Fidelity: exact -/
theorem voiSensor_mono [DecidableEq S] [DecidableEq T] {k₁ : Experiment W S} {k₂ : Experiment W T}
    (h : BlackwellLE k₂ k₁) (μ : Distr W) (X : W → ℝ) :
    voiSensor μ k₂ X ≤ voiSensor μ k₁ X := by
  unfold voiSensor; linarith [sensorValue_mono h μ X]

/-- **Good's theorem, free channel** (T10, first half): the value of information is nonnegative,
`𝒱(trivialExp) ≤ 𝒱(k)` — T8(a) with `BlackwellLE trivialExp k`.
Source: [[corr-wf13-inventory]] 012 / radical.md I11 (Good's theorem, the inequality); [[corr-channel-voi-mandate]] T10
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem voiSensor_nonneg [DecidableEq S] (μ : Distr W) (k : Experiment W S) (X : W → ℝ) :
    0 ≤ voiSensor μ k X := by
  rw [voiSensor_eq_sub_trivial, sub_nonneg]
  exact sensorValue_mono (blackwellLE_trivial k) μ X

/-- Adding a channel never lowers value: `0 ≤ VOI(k₂ | k₁)`.
Source: [[corr-channel-voi-mandate]] D2/D3
Kind: L
Fidelity: exact -/
theorem voiGiven_nonneg [DecidableEq S] [DecidableEq T] (μ : Distr W) (k₁ : Experiment W S)
    (k₂ : Experiment W T) (X : W → ℝ) : 0 ≤ voiGiven μ k₁ k₂ X := by
  rw [voiGiven, sub_nonneg]
  exact sensorValue_mono (blackwellLE_left_prod k₁ k₂) μ X

/-- **T8(b). The ceteris-paribus lemma** (corr-core-012): replacing the channel by no channel,
all else equal — the prior, the stakes, the menu unchanged, only `k ↦ trivialExp` — weakly
lowers value. "All else equal" is the whole content: the statement varies nothing but `k`.
Source: [[corr-core-inventory]] 012 / corrigibility-discussion-outline.md l. 7 ("information is valuable")
Kind: L (an instance of T8(a))
Fidelity: exact -/
theorem sensorValue_trivial_le [DecidableEq S] (μ : Distr W) (k : Experiment W S) (X : W → ℝ) :
    sensorValue μ trivialExp X ≤ sensorValue μ k X :=
  sensorValue_mono (blackwellLE_trivial k) μ X

/-- The product with the perfect experiment is worth exactly the perfect experiment
(Blackwell-equivalent both ways, T8(a) twice).
Source: [[corr-channel-voi-mandate]] D2, T4(b) ("after the scan `voiGiven … = 0`")
Kind: L
Fidelity: exact -/
theorem sensorValue_prod_perfect [DecidableEq W] [DecidableEq S] (μ : Distr W) (k : Experiment W S)
    (X : W → ℝ) : sensorValue μ (expProd k perfectExp) X = sensorValue μ perfectExp X :=
  le_antisymm (sensorValue_mono (prod_perfect_equiv k).1 μ X)
    (sensorValue_mono (prod_perfect_equiv k).2 μ X)

/-- **T4(f) in channel form**: holding the perfect channel, the button adds nothing,
`VOI(k | perfect) = 0` for every `k` (`prod perfect k` is Blackwell-equivalent to `perfect`).
Source: [[corr-core-inventory]] 025 / imported chat l. 52 ("the agent preserves the button only while it's the cheapest channel"); miri.md I10.8 (`VOI(button | y) = 0`)
Kind: L
Fidelity: exact -/
theorem voiGiven_perfect_left [DecidableEq W] [DecidableEq S] (μ : Distr W) (k : Experiment W S)
    (X : W → ℝ) : voiGiven μ perfectExp k X = 0 := by
  rw [voiGiven, sub_eq_zero]
  exact le_antisymm (sensorValue_mono (blackwellLE_perfect _) μ X)
    (sensorValue_mono (blackwellLE_left_prod perfectExp k) μ X)

/-- After a perfect scan the button is worth nothing more: `VOI(button | ⟨button, perfect⟩) = 0`,
the mandate's exact form (the agent already holds `prod button perfect`).
Source: [[corr-channel-voi-mandate]] T4(b); miri.md I10.8
Kind: L
Fidelity: exact -/
theorem voiGiven_button_after_perfect [DecidableEq W] [DecidableEq S] (μ : Distr W)
    (k : Experiment W S) (X : W → ℝ) : voiGiven μ (expProd k perfectExp) k X = 0 := by
  rw [voiGiven, sub_eq_zero]
  refine le_antisymm ?_ (sensorValue_mono (blackwellLE_left_prod _ k) μ X)
  calc sensorValue μ (expProd (expProd k perfectExp) k) X ≤ sensorValue μ perfectExp X :=
        sensorValue_mono (blackwellLE_perfect _) μ X
    _ ≤ sensorValue μ (expProd k perfectExp) X := sensorValue_mono (prod_perfect_equiv k).2 μ X

/-! ## T3. Every channel is worth at most the value of perfect information (general `W`) -/

/-- Per signal, the gain is at most the positive-part gain: `max(∑ μ k X, 0) ≤ ∑ μ k max(X, 0)`.
Source: none: infrastructure (T3's per-signal step)
Kind: L
Fidelity: n/a -/
theorem max_signalGain_le (μ : Distr W) (k : Experiment W S) (X : W → ℝ) (s : S) :
    max (signalGain μ k X s) 0 ≤ ∑ w, μ.mass w * k.k w s * max (X w) 0 := by
  have hnn : ∀ w, 0 ≤ μ.mass w * k.k w s := fun w => mul_nonneg (μ.nonneg w) ((k.k_mem w).1 s)
  refine max_le ?_ (Finset.sum_nonneg fun w _ => mul_nonneg (hnn w) (le_max_right _ _))
  exact Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hnn w)

/-- **T3, general form: the perfect-information bound.** For every prior, stakes and experiment,
`𝒱(k) ≤ E_μ[max(X, 0)]` — the value with the world revealed; hence
`VOI(k) ≤ E_μ[max(X, 0)] − max(E_μ[X], 0)` for **every** finite experiment, not only the button.
The general form of `corr-three-step`'s `voiButton2_le_vopi`.
Source: [[corr-wf14-inventory]] 037 item 9; [[corr-wf13-2-inventory]] 2-011(a); wentworth.md §2.4 ("applies to every competing channel")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem sensorValue_le_perfect_general [DecidableEq S] (μ : Distr W) (k : Experiment W S)
    (X : W → ℝ) : sensorValue μ k X ≤ expect μ (fun w => max (X w) 0) := by
  rw [sensorValue_eq_sum_max]
  calc ∑ s, max (signalGain μ k X s) 0 ≤ ∑ s, ∑ w, μ.mass w * k.k w s * max (X w) 0 :=
        Finset.sum_le_sum fun s _ => max_signalGain_le μ k X s
    _ = expect μ (fun w => max (X w) 0) := by
        unfold expect
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [show ∑ s, μ.mass w * k.k w s * max (X w) 0 = μ.mass w * max (X w) 0 * ∑ s, k.k w s by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring]
        rw [(k.k_mem w).2, mul_one]

/-- **T3 for `VOI`**: `VOI(k) ≤ E_μ[max(X, 0)] − max(E_μ[X], 0)` for every experiment.
Source: [[corr-wf14-inventory]] 037 item 9; wentworth.md §2.4
Kind: L
Fidelity: exact -/
theorem voiSensor_le_vopi [DecidableEq S] (μ : Distr W) (k : Experiment W S) (X : W → ℝ) :
    voiSensor μ k X ≤ expect μ (fun w => max (X w) 0) - max (expect μ X) 0 := by
  unfold voiSensor; linarith [sensorValue_le_perfect_general μ k X]

/-- The perfect experiment attains the bound: `VOI(perfect) = E_μ[max(X, 0)] − max(E_μ[X], 0)`.
Source: [[corr-channel-voi-mandate]] T3 (N+: the perfect scan attains it)
Kind: L
Fidelity: exact -/
theorem voiSensor_perfect [DecidableEq W] (μ : Distr W) (X : W → ℝ) :
    voiSensor μ perfectExp X = expect μ (fun w => max (X w) 0) - max (expect μ X) 0 := by
  rw [voiSensor, sensorValue_perfect]

/-! ## Good's theorem: the equality clause -/

/-- **Sum of positive parts versus positive part of the sum**: `∑ max(A s, 0) = max(∑ A s, 0)`
iff all the `A s` are nonnegative or all are nonpositive.
Source: none: infrastructure (Good's equality clause, abstract form)
Kind: P
Fidelity: n/a -/
theorem sum_max_eq_max_sum_iff (A : S → ℝ) :
    ∑ s, max (A s) 0 = max (∑ s, A s) 0 ↔ (∀ s, 0 ≤ A s) ∨ (∀ s, A s ≤ 0) := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := hne
    have h1 : A t ≤ ∑ s, max (A s) 0 :=
      (le_max_left _ _).trans (Finset.single_le_sum (fun s _ => le_max_right (A s) 0) (mem_univ t))
    have h2 : -A s ≤ ∑ s, max (A s) 0 - ∑ s, A s := by
      rw [← Finset.sum_sub_distrib]
      refine le_trans ?_ (Finset.single_le_sum (fun s _ => ?_) (mem_univ s))
      · exact by rw [max_eq_right hs.le]; linarith
      · exact by linarith [le_max_left (A s) 0]
    rcases le_total 0 (∑ s, A s) with hsum | hsum
    · rw [max_eq_left hsum] at h; linarith
    · rw [max_eq_right hsum] at h; linarith
  · rintro (h | h)
    · rw [max_eq_left (Finset.sum_nonneg fun s _ => h s)]
      exact Finset.sum_congr rfl fun s _ => max_eq_left (h s)
    · rw [max_eq_right (Finset.sum_nonpos fun s _ => h s)]
      exact Finset.sum_eq_zero fun s _ => max_eq_right (h s)

/-- **Good's theorem, the equality clause** (T10, second half): `VOI(k) = 0` iff one act is optimal
on every signal — continuing on every signal (`0 ≤ gain s` for all `s`) or stopping on every
signal (`gain s ≤ 0` for all `s`). A null signal has gain `0`, so "every positive-mass signal"
is automatic. `corr-three-step` has only the button case.
Source: [[corr-wf13-inventory]] 012 / radical.md I11 (Good's theorem, "with equality iff one act is optimal for `P`-almost every value of `S`")
Kind: P
Fidelity: exact (finite form; "almost every" is "every", null signals having zero gain)
Hyps: (a) none -/
theorem voiSensor_eq_zero_iff [DecidableEq S] (μ : Distr W) (k : Experiment W S) (X : W → ℝ) :
    voiSensor μ k X = 0 ↔ (∀ s, 0 ≤ signalGain μ k X s) ∨ (∀ s, signalGain μ k X s ≤ 0) := by
  rw [voiSensor, sensorValue_eq_sum_max, sub_eq_zero, ← sum_signalGain μ k X]
  exact sum_max_eq_max_sum_iff _

/-- Good's equality clause, positive form: `0 < VOI(k)` iff some signal favours continuing and
some signal favours stopping.
Source: [[corr-wf13-inventory]] 012 / radical.md I11; miri.md Prop. 10.5 (general clause)
Kind: L
Fidelity: exact -/
theorem voiSensor_pos_iff [DecidableEq S] (μ : Distr W) (k : Experiment W S) (X : W → ℝ) :
    0 < voiSensor μ k X ↔ (∃ s, 0 < signalGain μ k X s) ∧ (∃ s, signalGain μ k X s < 0) := by
  rw [lt_iff_le_and_ne, ne_comm, ne_eq, voiSensor_eq_zero_iff]
  constructor
  · rintro ⟨-, h⟩
    push Not at h
    obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := h
    exact ⟨⟨t, ht⟩, ⟨s, hs⟩⟩
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    refine ⟨voiSensor_nonneg μ k X, ?_⟩
    push Not
    exact ⟨⟨t, ht⟩, ⟨s, hs⟩⟩

/-! ## The bridge to `corr-three-step`'s value objects -/

section Bridge

variable {Ω A₁ A₂ : Type} [Fintype Ω] [Fintype A₂] [DecidableEq A₂] (S : ThreeStep Ω A₁ A₂)

/-- The press signal's gain is `corr-three-step`'s product-form press expectation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem signalGain_button_zero (a : A₁) (X : Ω → ℝ) :
    signalGain (S.μ a) (buttonExperiment S a) X 0 = S.obsExpect a .press X := rfl

/-- The silence signal's gain is the product-form silence expectation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem signalGain_button_one (a : A₁) (X : Ω → ℝ) :
    signalGain (S.μ a) (buttonExperiment S a) X 1 = S.obsExpect a .silent X := rfl

/-- The sensor value of the button is the sum of the two positive-part halves,
`max(E[X 1_Pr], 0) + max(E[X 1_¬Pr], 0)`.
Source: [[corr-channel-voi-mandate]] D3 (bridge)
Kind: L
Fidelity: exact -/
theorem sensorValue_button (a : A₁) (X : Ω → ℝ) :
    sensorValue (S.μ a) (buttonExperiment S a) X =
      max (S.obsExpect a .press X) 0 + max (S.obsExpect a .silent X) 0 := by
  rw [sensorValue_eq_sum_max, Fin.sum_univ_two, signalGain_button_zero, signalGain_button_one]

/-- **The bridge, informed value** (A1): `twoOptionValue a c s = 𝒱(button)(X_o) + E_μ[V(s)]` —
the two-option value is the sensor value of the button on the stakes `X_o = V(c) − V(s)` plus
the (signal-independent) stop payoff.
Source: [[corr-channel-voi-mandate]] D3 (bridge)
Kind: L
Fidelity: exact
Hyps: (a) A1 named -/
theorem twoOptionValue_eq_sensorValue_add (hA1 : S.A1) (a : A₁) (o₀ : Obs) (c s : A₂) :
    S.twoOptionValue a c s =
      sensorValue (S.μ a) (buttonExperiment S a) (S.Xo a o₀ c s) + expect (S.μ a) (S.V a o₀ s) := by
  rw [sensorValue_button]
  have hpc : S.V a .press c = S.V a o₀ c := funext (hA1 a .press o₀ c)
  have hps : S.V a .press s = S.V a o₀ s := funext (hA1 a .press o₀ s)
  have hsc : S.V a .silent c = S.V a o₀ c := funext (hA1 a .silent o₀ c)
  have hss : S.V a .silent s = S.V a o₀ s := funext (hA1 a .silent o₀ s)
  unfold ThreeStep.twoOptionValue
  rw [hpc, hps, hsc, hss, ← S.obsExpect_press_add_silent a (S.V a o₀ s)]
  have e1 : S.obsExpect a .press (S.Xo a o₀ c s) =
      S.obsExpect a .press (S.V a o₀ c) - S.obsExpect a .press (S.V a o₀ s) :=
    S.obsExpect_sub a .press (S.V a o₀ c) (S.V a o₀ s)
  have e2 : S.obsExpect a .silent (S.Xo a o₀ c s) =
      S.obsExpect a .silent (S.V a o₀ c) - S.obsExpect a .silent (S.V a o₀ s) :=
    S.obsExpect_sub a .silent (S.V a o₀ c) (S.V a o₀ s)
  rw [e1, e2, ThreeStep.max_eq_add_max_sub (S.obsExpect a .press (S.V a o₀ c)),
    ThreeStep.max_eq_add_max_sub (S.obsExpect a .silent (S.V a o₀ c))]
  ring

/-- **The bridge, value of information** (A1): `voiButton2 a o₀ c s = VOI(button)(X_o)` — on
every `ThreeStep` with A1, not only `twoState` (the stop payoff cancels between the informed and
the prior value).
Source: [[corr-channel-voi-mandate]] D3 (bridge), T1 (`voiSensor button = voiButton2`)
Kind: L
Fidelity: stronger: the mandate states it on `twoState`; it holds under A1 in general
Hyps: (a) A1 named -/
theorem voiButton2_eq_voiSensor (hA1 : S.A1) (a : A₁) (o₀ : Obs) (c s : A₂) :
    S.voiButton2 a o₀ c s = voiSensor (S.μ a) (buttonExperiment S a) (S.Xo a o₀ c s) := by
  rw [voiSensor, ThreeStep.voiButton2, twoOptionValue_eq_sensorValue_add S hA1 a o₀ c s]
  unfold ThreeStep.twoOptionPriorValue ThreeStep.priorValue
  rw [S.expect_Xo a o₀ c s, ThreeStep.max_eq_add_max_sub (expect (S.μ a) (S.V a o₀ c))]
  ring

end Bridge

end

end Cleanroom.Corrigibility.CorrChannelVoi

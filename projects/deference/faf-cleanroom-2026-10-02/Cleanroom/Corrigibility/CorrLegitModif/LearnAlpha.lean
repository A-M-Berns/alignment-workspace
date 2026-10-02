import Cleanroom.Corrigibility.CorrThreeStepFacts.Identification
import Cleanroom.Corrigibility.CorrThreeStepFacts.Basic
import Cleanroom.Found.CorrThreeStep.TwoState
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# corr-legit-modif — T5: learning `α` under reflection

[[christiano]] T2 l. 153: "let the agent *learn* `α` from a history of presses and outcomes …
Show whether, under the thesis's own reflection condition on `P`, the agent's estimate `α̂_t`
tracks the true `α` as its own `ε_t → 0`. If it does — as conservation of expected evidence says
it must for a reflective agent …". [[anthropic-davis]] 18 ll. 105: the dichotomy — if presses
carry information only about `X`, `α` is learnable from the agent's own judgment and Total Trust
toward the button fails after finitely many self-assessed false presses.

Model: the two-state sensor with `α` unknown — a two-point prior `α ∈ {α₀, α₁}`, `0 < α₀ < α₁`,
weights `(ν, 1 − ν)`; `β`, `ε`, `c`, `h` known. A round observes press/silence (branch (i)) and, on
branch (ii), the outcome `ω`. **The update rule is Bayes over the run's objects** (repair round 1,
adversarial B1): the per-round likelihood of an observation `(o, ω)` under `α` is
`likeRound ε α β (o, ω) = P(ω) · P(o | ω; α)` with `P(press | ω; α) = twoPress α β ω` (the
`obsWeight` of `twoState`), a history's likelihood is the i.i.d. product `likeHist`, and the
posterior weights `w0`/`w1` are prior × likelihood. The one-round objects `num1`/`den1` sum the same
`likeRound` over the outcome (`pObs_eq_sum_likeRound`).

(a) `alphaHat_martingale`: over one round `∑_o num(o) = E[α]` and `∑_o den(o) = 1` — conservation
of expected evidence, the agent's reflection toward its own future estimate (`tower_level_set`'s
"automatic" identity). (b) Branch (ii), outcomes observed: `rates_identified` — `(α, β) ↦
(P(Pr | R), P(Pr | W))` is the identity on `twoPress` (definitional; supporting);
`posterior_odds_geometric` — after `n` rounds of `(press, R)` the odds of `α₁` against `α₀` are
`(α₁/α₀)ⁿ (1 − ν)/ν` (the `(1 − ε)ⁿ` of the likelihoods cancels); `Crosses` — the below-threshold
inequality of `twoState ε α̂ₙ β c h` fails at the estimate, in products, bridged to the run's object
by `crosses_iff_not_belowThreshold`; `alphaHat_crossing` — the least such `n` exists when the sharp
sensor crosses, with the converse `crosses_imp_sharp` (so `exists_crosses_iff`), and a witness
`alphaHat_crossing_witness` whose least index is `4`. Branch (i), compliance record only:
`record_nonidentification` / `record_undecides_d1` (cited) — `α` is not identified from the record;
`fibre_same_likelihood`: two sensors on one fibre of `record` assign every press/silence history the
same likelihood, so the posterior over them from the record alone is the prior.

Finding (imprecision, Known issues 6): "`α̂_t` tracks the true `α`" is a consistency claim needing
identifiability (branch (ii)); reflection buys only (a). Turner C6: `D1At` is stated in the agent's
`μ`; the true-`ε` and self-estimate verdicts differ — `corr-landscape`'s `Crossing.cells_witness`,
cited. The a.s. convergence under identifiability (the stretch) is not stated here: a precise
statement needs a product probability space, and the run's `def-dose-response` Coin.lean is the
place that has one; recorded in the report, not listed as OPEN.
-/

namespace Cleanroom.Corrigibility.CorrLegitModif

open Finset Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrThreeStepFacts

noncomputable section

/-- The world prior of the two-state sensor: `P(R) = 1 − ε`, `P(W) = ε` (the masses of `twoPoint`).
Source: [[corr-three-step]] `twoPoint`; mandate T5
Kind: D
Fidelity: exact -/
def worldMass (ε : ℝ) : World → ℝ
  | .right => 1 - ε
  | .wrong => ε

/-- **The per-round likelihood of an observation `(o, ω)` under false-press rate `α`**, from the
run's objects: `P(ω) · P(o | ω; α)` with `P(press | ω; α) = twoPress α β ω` and
`P(silent | ω; α) = 1 − twoPress α β ω` — the `obsWeight` of `twoState ε α β c h`.
Source: [[corr-three-step]] `twoState` (`press := twoPress α β`, `obsWeight`); mandate T5
Kind: D
Fidelity: exact -/
def likeRound (ε α β : ℝ) : Obs × World → ℝ
  | (.press, ω) => worldMass ε ω * twoPress α β ω
  | (.silent, ω) => worldMass ε ω * (1 - twoPress α β ω)

/-- The observation likelihood of the two-state sensor with false-press rate `α`:
`P(press) = (1 − ε) α + ε β`, `P(silent) = (1 − ε)(1 − α) + ε (1 − β)`.
Source: [[corr-three-step]] `twoState` (`pressMass`); mandate T5
Kind: D
Fidelity: exact -/
def pObs (ε α β : ℝ) : Obs → ℝ
  | .press => (1 - ε) * α + ε * β
  | .silent => (1 - ε) * (1 - α) + ε * (1 - β)

/-- The press/silence likelihood is the per-round likelihood summed over the outcome: the
one-round objects `num1`/`den1` and the `n`-round weights are built from the same `likeRound`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pObs_eq_sum_likeRound (ε α β : ℝ) (o : Obs) :
    pObs ε α β o = ∑ ω, likeRound ε α β (o, ω) := by
  rw [World.sum_eq]
  cases o <;> simp [pObs, likeRound, worldMass, twoPress]

/-- The two observation likelihoods sum to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pObs_sum (ε α β : ℝ) : pObs ε α β .press + pObs ε α β .silent = 1 := by
  simp [pObs]; ring

/-- The posterior-mean numerator of `α` after one observation:
`ν α₀ P(o | α₀) + (1 − ν) α₁ P(o | α₁)`.
Source: mandate T5 (`alphaHat`, numerator)
Kind: D
Fidelity: exact -/
def num1 (ε β ν α₀ α₁ : ℝ) (o : Obs) : ℝ := ν * α₀ * pObs ε α₀ β o + (1 - ν) * α₁ * pObs ε α₁ β o

/-- The posterior denominator after one observation: `ν P(o | α₀) + (1 − ν) P(o | α₁)`.
Source: mandate T5 (`alphaHat`, denominator)
Kind: D
Fidelity: exact -/
def den1 (ε β ν α₀ α₁ : ℝ) (o : Obs) : ℝ := ν * pObs ε α₀ β o + (1 - ν) * pObs ε α₁ β o

/-- **`alphaHat_martingale`** (conservation of expected evidence, the anchor): over **one round**
the observation-weighted posterior numerators sum to the prior mean `ν α₀ + (1 − ν) α₁` and the
denominators to `1` — what reflection toward one's own future estimate buys. A one-round identity;
no general posterior process is modelled.
Source: [[christiano]] T2 l. 153 ("as conservation of expected evidence says it must for a
reflective agent"); `tower_level_set`
Kind: T
Fidelity: exact (one round)
Hyps: (a) none -/
theorem alphaHat_martingale (ε β ν α₀ α₁ : ℝ) :
    ∑ o, num1 ε β ν α₀ α₁ o = ν * α₀ + (1 - ν) * α₁ ∧ ∑ o, den1 ε β ν α₀ α₁ o = 1 := by
  constructor <;> rw [Obs.sum_eq] <;> simp [num1, den1, pObs] <;> ring

/-- **`rates_identified`** (branch (ii), supporting): with outcomes observed,
`(α, β) ↦ (P(Pr | R), P(Pr | W))` is the identity on the two-state press — a definitional
unfolding of `twoPress` (`rfl`), recorded so the ledger can point at it; not a headline.
Source: [[anthropic-davis]] 18 l. 105 ("presses carry information only about `X`, in which case
`α` is learnable"); `twoPress`
Kind: T
Fidelity: exact
Hyps: (a) none -/
theorem rates_identified (α β : ℝ) : twoPress α β .right = α ∧ twoPress α β .wrong = β :=
  ⟨rfl, rfl⟩

/-! ## Histories, likelihoods and the posterior weights -/

/-- **The likelihood of a history** of `(o, ω)` observations under `α`: the i.i.d. product of the
per-round likelihoods (the model: rounds are independent given `α`).
Source: mandate T5 ("a history of presses and outcomes")
Kind: D
Fidelity: exact (i.i.d. rounds) -/
def likeHist (ε α β : ℝ) (hs : List (Obs × World)) : ℝ := (hs.map (likeRound ε α β)).prod

/-- The posterior weight of `α₀` after a history: prior × likelihood, `ν · L(hs | α₀)`.
Source: mandate T5(b)
Kind: D
Fidelity: exact (Bayes, unnormalized) -/
def w0 (ν ε α₀ β : ℝ) (hs : List (Obs × World)) : ℝ := ν * likeHist ε α₀ β hs

/-- The posterior weight of `α₁` after a history: `(1 − ν) · L(hs | α₁)`.
Source: mandate T5(b)
Kind: D
Fidelity: exact (Bayes, unnormalized) -/
def w1 (ν ε α₁ β : ℝ) (hs : List (Obs × World)) : ℝ := (1 - ν) * likeHist ε α₁ β hs

/-- `n` rounds of `(press, R)` — `n` self-assessed false presses.
Source: [[anthropic-davis]] 18 l. 105; mandate T5(b)
Kind: D
Fidelity: exact -/
def pressR (n : ℕ) : List (Obs × World) := List.replicate n (.press, .right)

/-- The likelihood of `n` rounds of `(press, R)` under `α` is `((1 − ε) α)ⁿ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem likeHist_pressR (ε α β : ℝ) (n : ℕ) :
    likeHist ε α β (pressR n) = ((1 - ε) * α) ^ n := by
  simp [likeHist, pressR, List.map_replicate, List.prod_replicate, likeRound, worldMass, twoPress]

/-- The posterior-mean numerator of `α` after a history, `w₀ α₀ + w₁ α₁`.
Source: mandate T5 (`alphaHat`, numerator)
Kind: D
Fidelity: exact -/
def alphaHatNum (ν ε β α₀ α₁ : ℝ) (hs : List (Obs × World)) : ℝ :=
  w0 ν ε α₀ β hs * α₀ + w1 ν ε α₁ β hs * α₁

/-- The posterior denominator after a history, `w₀ + w₁`.
Source: mandate T5 (`alphaHat`, denominator)
Kind: D
Fidelity: exact -/
def alphaHatDen (ν ε β α₀ α₁ : ℝ) (hs : List (Obs × World)) : ℝ :=
  w0 ν ε α₀ β hs + w1 ν ε α₁ β hs

/-- The posterior mean `α̂` after a history (the ratio; meaningful under `0 < alphaHatDen`).
Source: mandate T5 (`alphaHat`: "the ratio only in headlines, under positivity")
Kind: D
Fidelity: exact -/
def alphaHat (ν ε β α₀ α₁ : ℝ) (hs : List (Obs × World)) : ℝ :=
  alphaHatNum ν ε β α₀ α₁ hs / alphaHatDen ν ε β α₀ α₁ hs

/-- **`posterior_odds_geometric`**: after `n` rounds of `(press, R)` the posterior odds of `α₁`
against `α₀` are `(α₁/α₀)ⁿ · (1 − ν)/ν` — prior odds times the likelihood ratio, the `(1 − ε)ⁿ`
factor of the per-round likelihoods cancelling. The Bayesian content is in `likeRound` (taken from
`twoPress`) and the i.i.d. product `likeHist`; this row is the algebra (regraded L at audit round
1, adversarial B1: the weights were previously stipulated as `ν α₀ⁿ`, `(1 − ν) α₁ⁿ`).
Source: [[anthropic-davis]] 18 l. 105; mandate T5(b)
Kind: L
Fidelity: exact
Hyps: (a) `0 < ν`, `ε < 1`, `0 < α₀` -/
theorem posterior_odds_geometric {ν ε α₀ : ℝ} (hν : 0 < ν) (hε : ε < 1) (hα₀ : 0 < α₀)
    (α₁ β : ℝ) (n : ℕ) :
    w1 ν ε α₁ β (pressR n) / w0 ν ε α₀ β (pressR n) = (α₁ / α₀) ^ n * ((1 - ν) / ν) := by
  unfold w0 w1
  rw [likeHist_pressR, likeHist_pressR]
  have h1 : (0 : ℝ) < 1 - ε := by linarith
  rw [mul_pow, mul_pow, div_pow]
  field_simp

/-- The denominator is positive under the standing hypotheses.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem alphaHatDen_pos {ν ε β α₀ α₁ : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hε : ε < 1)
    (hα₀ : 0 < α₀) (hα₁ : 0 < α₁) (n : ℕ) : 0 < alphaHatDen ν ε β α₀ α₁ (pressR n) := by
  unfold alphaHatDen w0 w1
  rw [likeHist_pressR, likeHist_pressR]
  have h1 : (0 : ℝ) < 1 - ε := by linarith
  exact add_pos (mul_pos hν0 (pow_pos (mul_pos h1 hα₀) n))
    (mul_pos (by linarith) (pow_pos (mul_pos h1 hα₁) n))

/-- The estimate lies in `[0, 1]` when the prior weights and both rates do (so `twoState` at the
estimate exists).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem alphaHat_mem_Icc {ν ε β α₀ α₁ : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (hε : ε ≤ 1)
    (hα₀ : α₀ ∈ Set.Icc (0 : ℝ) 1) (hα₁ : α₁ ∈ Set.Icc (0 : ℝ) 1) (n : ℕ)
    (hden : 0 < alphaHatDen ν ε β α₀ α₁ (pressR n)) :
    alphaHat ν ε β α₀ α₁ (pressR n) ∈ Set.Icc (0 : ℝ) 1 := by
  have hw0 : 0 ≤ w0 ν ε α₀ β (pressR n) := by
    unfold w0; rw [likeHist_pressR]
    exact mul_nonneg hν0 (pow_nonneg (mul_nonneg (by linarith) hα₀.1) n)
  have hw1 : 0 ≤ w1 ν ε α₁ β (pressR n) := by
    unfold w1; rw [likeHist_pressR]
    exact mul_nonneg (by linarith) (pow_nonneg (mul_nonneg (by linarith) hα₁.1) n)
  unfold alphaHat
  constructor
  · apply div_nonneg _ hden.le
    unfold alphaHatNum
    exact add_nonneg (mul_nonneg hw0 hα₀.1) (mul_nonneg hw1 hα₁.1)
  · rw [div_le_one hden]
    unfold alphaHatNum alphaHatDen
    have h0 := mul_le_mul_of_nonneg_left hα₀.2 hw0
    have h1 := mul_le_mul_of_nonneg_left hα₁.2 hw1
    linarith

/-! ## The crossing -/

/-- **The crossing inequality**: the below-threshold inequality of `twoState ε α̂ₙ β c h` fails at
the estimate `α̂ₙ` after `n` self-assessed false presses — `β ε h · (w₀ + w₁) < (w₀ α₀ + w₁ α₁) · (1 − ε) · c`,
the product form of `β ε h < α̂ₙ (1 − ε) c`; `crosses_iff_not_belowThreshold` is the bridge to the
run's object.
Source: [[anthropic-davis]] 18 l. 105 ("the inequality in claim 5 is violated once `α/β` exceeds
`ε h/((1 − ε) c)`"); `twoState_deltaMinus_nonneg_iff` (the two-state threshold)
Kind: D
Fidelity: exact (product form; bridged to `twoState` by `crosses_iff_not_belowThreshold`) -/
def Crosses (ε β c h ν α₀ α₁ : ℝ) (n : ℕ) : Prop :=
  β * ε * h * alphaHatDen ν ε β α₀ α₁ (pressR n) <
    alphaHatNum ν ε β α₀ α₁ (pressR n) * (1 - ε) * c

/-- `Crosses` with the common factor `(1 − ε)ⁿ` of the weights cancelled.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem crosses_iff_core {ε β c h ν α₀ α₁ : ℝ} (hε : ε < 1) (n : ℕ) :
    Crosses ε β c h ν α₀ α₁ n ↔
      β * ε * h * (ν * α₀ ^ n + (1 - ν) * α₁ ^ n) <
        (ν * α₀ ^ n * α₀ + (1 - ν) * α₁ ^ n * α₁) * (1 - ε) * c := by
  have hp : 0 < (1 - ε) ^ n := pow_pos (by linarith) n
  unfold Crosses alphaHatNum alphaHatDen w0 w1
  simp only [likeHist_pressR, mul_pow]
  constructor
  · intro H
    refine lt_of_mul_lt_mul_left (a := (1 - ε) ^ n) ?_ hp.le
    linarith [H]
  · intro H
    have := mul_lt_mul_of_pos_left H hp
    linarith [this]

/-- **The bridge to the run's object**: `Crosses n` is exactly the failure of the below-threshold
inequality of `twoState ε α̂ₙ β c h` on the two-option variable `X_Pr` (continue over stop), through
`twoState_deltaMinus_nonneg_iff`.
Source: [[corr-three-step]] `belowThresholdIneq`, `twoState_deltaMinus_nonneg_iff`; mandate T5(b)
("`belowThresholdIneq` on `twoState ε (alphaHat n) β c h`")
Kind: L
Fidelity: exact
Hyps: (a) `0 < alphaHatDen`, and the `Icc` bounds `twoState` needs to exist
(`alphaHat_mem_Icc`) -/
theorem crosses_iff_not_belowThreshold {ε β c h ν α₀ α₁ : ℝ} (n : ℕ)
    (hden : 0 < alphaHatDen ν ε β α₀ α₁ (pressR n)) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : alphaHat ν ε β α₀ α₁ (pressR n) ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    Crosses ε β c h ν α₀ α₁ n ↔
      ¬ (twoState ε (alphaHat ν ε β α₀ α₁ (pressR n)) β c h hε hα hβ).belowThresholdIneq ()
        ((twoState ε (alphaHat ν ε β α₀ α₁ (pressR n)) β c h hε hα hβ).Xo () .press
          .cont .stop) := by
  have key : (twoState ε (alphaHat ν ε β α₀ α₁ (pressR n)) β c h hε hα hβ).belowThresholdIneq ()
        ((twoState ε (alphaHat ν ε β α₀ α₁ (pressR n)) β c h hε hα hβ).Xo () .press
          .cont .stop) ↔
      (1 - ε) * alphaHat ν ε β α₀ α₁ (pressR n) * c ≤ ε * β * h := by
    rw [← twoState_deltaMinus_nonneg_iff ε _ β c h hε hα hβ]
    unfold ThreeStep.belowThresholdIneq ThreeStep.deltaMinus
    constructor <;> intro H <;> linarith
  rw [key, not_le]
  unfold alphaHat
  have e : (1 - ε) * (alphaHatNum ν ε β α₀ α₁ (pressR n) / alphaHatDen ν ε β α₀ α₁ (pressR n)) * c =
      alphaHatNum ν ε β α₀ α₁ (pressR n) * (1 - ε) * c / alphaHatDen ν ε β α₀ α₁ (pressR n) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  rw [e, lt_div_iff₀ hden]
  unfold Crosses
  constructor <;> intro H <;> linarith

/-- **`alphaHat_crossing`**: if the sharp sensor `α₁` would violate the threshold
(`α₁ (1 − ε) c > β ε h`) then there is a least number `n` of self-assessed false presses after
which the estimate does — Total Trust toward the button fails after finitely many of them. The
existence is the geometric growth of the odds (`pow_unbounded_of_one_lt`); the least index is
`Nat.find`. The hypothesis is also necessary (`crosses_imp_sharp`, `exists_crosses_iff`).
Source: [[anthropic-davis]] 18 l. 105 ("Total Trust toward the button fails after finitely many
self-assessed false presses"); corr-wf13-2-073
Kind: P
Fidelity: exact
Hyps: (a) `ν < 1`, `0 < α₀ < α₁`, `ε < 1`, `β ε h < α₁ (1 − ε) c` (the existence needs neither
`0 < ν` nor `0 < c`, which the converse `crosses_imp_sharp` does; the intended range is `0 < ν`,
`0 ≤ ε`, `0 < c`, `0 ≤ h`, `α₁ ≤ 1`, `0 ≤ β ≤ 1`) -/
theorem alphaHat_crossing {ε β c h ν α₀ α₁ : ℝ} (hν1 : ν < 1) (hα₀ : 0 < α₀)
    (hlt : α₀ < α₁) (hε1 : ε < 1) (hsharp : β * ε * h < α₁ * (1 - ε) * c) :
    ∃ n, Crosses ε β c h ν α₀ α₁ n ∧ ∀ m < n, ¬ Crosses ε β c h ν α₀ α₁ m := by
  classical
  have hr : 1 < α₁ / α₀ := (one_lt_div hα₀).2 hlt
  have hA₁ : 0 < α₁ * (1 - ε) * c - β * ε * h := by linarith
  have hden : 0 < (1 - ν) * (α₁ * (1 - ε) * c - β * ε * h) := mul_pos (by linarith) hA₁
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
    (ν * (β * ε * h - α₀ * (1 - ε) * c) / ((1 - ν) * (α₁ * (1 - ε) * c - β * ε * h))) hr
  have hex : Crosses ε β c h ν α₀ α₁ n := by
    rw [crosses_iff_core hε1]
    have hpow : 0 < α₀ ^ n := pow_pos hα₀ n
    have h1 : ν * (β * ε * h - α₀ * (1 - ε) * c) <
        (1 - ν) * (α₁ * (1 - ε) * c - β * ε * h) * (α₁ / α₀) ^ n := by
      rw [div_lt_iff₀ hden] at hn; linarith
    have hα₁n : α₁ ^ n = (α₁ / α₀) ^ n * α₀ ^ n := by
      rw [div_pow, div_mul_cancel₀ _ hpow.ne']
    have h2 : 0 < α₀ ^ n * ((1 - ν) * (α₁ * (1 - ε) * c - β * ε * h) * (α₁ / α₀) ^ n -
        ν * (β * ε * h - α₀ * (1 - ε) * c)) := mul_pos hpow (by linarith)
    rw [hα₁n]
    nlinarith [h2]
  exact ⟨Nat.find ⟨n, hex⟩, Nat.find_spec ⟨n, hex⟩, fun m hm => Nat.find_min ⟨n, hex⟩ hm⟩

/-- **The converse**: if the estimate crosses after some history then the sharp sensor crosses
(`α̂ₙ ≤ α₁`, as the estimate is a convex combination of `α₀ < α₁`).
Source: none: infrastructure (audit round 1, fidelity N4(iii))
Kind: L
Fidelity: exact
Hyps: (a) `0 < ν < 1`, `0 < α₀ < α₁`, `ε < 1`, `0 < c` -/
theorem crosses_imp_sharp {ε β c h ν α₀ α₁ : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hα₀ : 0 < α₀)
    (hlt : α₀ < α₁) (hε1 : ε < 1) (hc : 0 < c) {n : ℕ} (hn : Crosses ε β c h ν α₀ α₁ n) :
    β * ε * h < α₁ * (1 - ε) * c := by
  rw [crosses_iff_core hε1] at hn
  have hA : 0 < ν * α₀ ^ n := mul_pos hν0 (pow_pos hα₀ n)
  have hB : 0 ≤ (1 - ν) * α₁ ^ n := mul_nonneg (by linarith) (pow_nonneg (by linarith) n)
  have hD : 0 < (1 - ε) * c := mul_pos (by linarith) hc
  by_contra hcon
  have hcon' : α₁ * (1 - ε) * c ≤ β * ε * h := not_lt.1 hcon
  have hgap : 0 ≤ ν * α₀ ^ n * (α₁ - α₀) * ((1 - ε) * c) :=
    mul_nonneg (mul_nonneg hA.le (sub_nonneg.2 hlt.le)) hD.le
  have h1 : (ν * α₀ ^ n * α₀ + (1 - ν) * α₁ ^ n * α₁) * (1 - ε) * c ≤
      (ν * α₀ ^ n + (1 - ν) * α₁ ^ n) * (α₁ * (1 - ε) * c) := by linarith [hgap]
  have h2 : (ν * α₀ ^ n + (1 - ν) * α₁ ^ n) * (α₁ * (1 - ε) * c) ≤
      (ν * α₀ ^ n + (1 - ν) * α₁ ^ n) * (β * ε * h) :=
    mul_le_mul_of_nonneg_left hcon' (by linarith)
  linarith

/-- **The crossing, as an iff**: under the side conditions, the sharp sensor crosses iff the
estimate crosses after some number of self-assessed false presses.
Source: [[anthropic-davis]] 18 l. 105; audit round 1 (fidelity N4(iii))
Kind: C (`alphaHat_crossing`, `crosses_imp_sharp`)
Fidelity: exact
Hyps: (a) `0 < ν < 1`, `0 < α₀ < α₁`, `ε < 1`, `0 < c` -/
theorem exists_crosses_iff {ε β c h ν α₀ α₁ : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hα₀ : 0 < α₀)
    (hlt : α₀ < α₁) (hε1 : ε < 1) (hc : 0 < c) :
    β * ε * h < α₁ * (1 - ε) * c ↔ ∃ n, Crosses ε β c h ν α₀ α₁ n := by
  constructor
  · intro hs
    obtain ⟨n, hn, -⟩ := alphaHat_crossing hν1 hα₀ hlt hε1 hs
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact crosses_imp_sharp hν0 hν1 hα₀ hlt hε1 hc hn

/-- **A witness for `alphaHat_crossing`**: `ν = 9/10` (prior weight on the dull sensor),
`α₀ = 1/10`, `α₁ = 1/5`, `ε = 1/10`, `β = 9/10`, `c = 1`, `h = 3/2`. The full hypothesis package
holds (the sharp sensor crosses: `27/200 < 9/50`), the estimate crosses at `n = 4` and not at
`n ≤ 3` — the least crossing index is `4` (the odds `(1/9) · 2ⁿ` must exceed `1`). Added at audit
round 1 (adversarial N3).
Source: [[anthropic-davis]] 18 l. 105; mandate T5(b)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem alphaHat_crossing_witness :
    (0 : ℝ) < 9 / 10 ∧ (9 / 10 : ℝ) < 1 ∧ (0 : ℝ) < 1 / 10 ∧ (1 / 10 : ℝ) < 1 / 5 ∧
    (1 / 10 : ℝ) < 1 ∧ (0 : ℝ) < 1 ∧
    (9 / 10 : ℝ) * (1 / 10) * (3 / 2) < 1 / 5 * (1 - 1 / 10) * 1 ∧
    Crosses (1 / 10) (9 / 10) 1 (3 / 2) (9 / 10) (1 / 10) (1 / 5) 4 ∧
    ∀ m < 4, ¬ Crosses (1 / 10) (9 / 10) 1 (3 / 2) (9 / 10) (1 / 10) (1 / 5) m := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, ?_, ?_⟩
  · rw [crosses_iff_core (by norm_num)]; norm_num
  · intro m hm
    rw [crosses_iff_core (by norm_num)]
    have hm' : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
    rcases hm' with rfl | rfl | rfl | rfl <;> norm_num

/-! ## Branch (i): the compliance record alone -/

/-- **`fibre_same_likelihood`** (branch (i)): two sensors on one fibre of `record` have the same
press/silence likelihoods, hence assign every press/silence history the same likelihood — from the
record alone the posterior over the two is the prior (`record_nonidentification`,
`record_undecides_d1` for what the record leaves open).
Source: [[corr-three-step-facts]] `record`, `record_fibre`; [[anthropic-davis]] 18 l. 105
(branch (i)); mandate T5(b)
Kind: L
Fidelity: exact
Hyps: (a) `record ε α β = record ε' α' β'` -/
theorem fibre_same_likelihood {ε α β ε' α' β' : ℝ} (h : record ε α β = record ε' α' β') :
    (∀ o, pObs ε α β o = pObs ε' α' β' o) ∧
    ∀ os : List Obs, (os.map (pObs ε α β)).prod = (os.map (pObs ε' α' β')).prod := by
  unfold record at h
  rw [Prod.mk.injEq] at h
  have hs : pObs ε α β .silent = pObs ε' α' β' .silent := by simp [pObs]; linarith [h.1, h.2]
  have hp : pObs ε α β .press = pObs ε' α' β' .press := by
    have := pObs_sum ε α β
    have := pObs_sum ε' α' β'
    linarith
  have ho : ∀ o, pObs ε α β o = pObs ε' α' β' o := fun o => by cases o <;> assumption
  exact ⟨ho, fun os => by rw [List.map_congr_left (fun o _ => ho o)]⟩

end

end Cleanroom.Corrigibility.CorrLegitModif

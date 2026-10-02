import Cleanroom.Found.CorrThreeStep.TwoState
import Cleanroom.Corrigibility.CorrCautionPower.Setting

/-!
# `corr-caution-power` — Model M: dogmatism, non-identification, labelled feedback

Model M (`caution-final.md` S8): per-step wrong-rate `ε` on the agent's self-model, `ρε` in
truth; overseers press with sensitivity `β` and false-press rate `α`; self-suspicion `μ ∈ [0,1]`
gives the effective self-error `ε_eff = (1 − μ) ε + μ ρ ε`; a press is heeded iff the
below-threshold inequality of `corr-three-step`'s `twoState` at `ε := ε_eff` holds.

* `epsEff`, `pressProb`, `alphaTH`, `likelihood`, `Heed` (defined *as* the parent's `Δ₋ ≥ 0`
  on `twoState (epsEff …)`), `muDagger`.
* **Heed condition, derived (grade (a)):** `heed_iff_epsStar` is
  `twoState_deltaMinus_nonneg_iff_epsStar` instantiated; `heed_iff_muDagger_le` in the regime.
* **(a) Dogmatic** `dogmatic_never_heeds`, `bayesUpdate_zero`, `bayesIter_zero`: `μ = 0` stays
  `0` under every press record, so "never heeds" is a statement about every `t`.
* **(b) Non-identification (load-bearing 2):** `pressProb_alphaTH` (`p_th = p_reck` exactly),
  `likelihood_th_eq_reck` (every record), `bayesFactor_th_reck_eq_one`,
  `postOdds_eq_priorOdds`; **well-formedness** `alphaTH_mem_Icc` (`α' ∈ [0, 1]`), and the
  threshold *rises*: `alpha_le_alphaTH`, `epsStar_mono_alpha`, `epsStar_le_epsStar_alphaTH`.
  Numbers at `(ε, ρ, α, β, c, h) = (1/20, 4, 1/10, 1/2, 1, 2)`: `p_reck = 9/50`,
  `α' = 31/190`, `ε*(α) = 1/11`, `ε*(α') = 31/221` (the source's `0.163`, `0.1403`).
* **(b′) Labelled feedback:** `expect_logLR_eq_klBern` (the per-step expected log-LR is the
  two-point KL) and `klBern_pos` (Gibbs, strict for `ρ > 1`). The a.s. limit `μ_t → 1` is not
  formalized (SLLN; recorded in the findings).
* **Whole-line:** `epsStar_scale` (invariance under `(c, h) ↦ (l c, l h)`), and at
  `(c, h, α, β) = (20, 2, 1/10, 1/2)`: `ε* = 2/3` and `Heed → 2/3 ≤ ρ ε` for every `μ ∈ [0, 1]`.

The Bayes-factor theorem is trivially true once `pressProb_alphaTH` is proved — that *is* the
source's point ("one number for three unknowns"); the content that can be wrong is the
well-formedness and the threshold monotonicity, proved with exact positivity hypotheses.
corr-wf14-009's compliance-record non-identification (run 1 `miri` Prop. 15.1) is
`corr-three-step-facts`'s sibling result, not duplicated here.

Sources: [[corr-wf14-inventory]] 099 → `caution-final.md` S8(a), (b), (b′) (l. 75–78), proof §8
(l. 141–151); [[corr-wf14-2-inventory]] 2-040, 2-041 → `caution-adversary.md` A8.3–A8.4 (l. 69–71).
-/

namespace Cleanroom.Corrigibility.CorrCautionPower

open Cleanroom.Found.CorrThreeStep
open Finset hiding expect expect_const

namespace ModelM

/-! ## Objects -/

/-- **The effective self-error** `ε_eff = (1 − μ) ε + μ ρ ε` under self-suspicion `μ`.
Source: [[corr-wf14-inventory]] 099 / caution-final.md S8 (l. 75)
Kind: D
Fidelity: exact -/
def epsEff (ε ρ μ : ℝ) : ℝ := (1 - μ) * ε + μ * (ρ * ε)

/-- **The press probability** under wrong-rate `ε`, sensitivity `β`, false-press rate `α`:
`P(press) = ε β + (1 − ε) α` (the Bernoulli parameter of the press bit).
Source: [[corr-wf14-inventory]] 099 / caution-final.md S8(b) (l. 77, `p_r`, `p_c`)
Kind: D
Fidelity: exact -/
def pressProb (ε α β : ℝ) : ℝ := ε * β + (1 - ε) * α

/-- **The trigger-happy false-press rate** `α' = (p_reck − ε β) / (1 − ε)`: the `α` at which
"calibrated agent, trigger-happy overseers" fits the press record of the reckless agent.
Source: [[corr-wf14-inventory]] 099 / caution-final.md S8(b) (l. 77); caution-adversary.md A8.3 (l. 69)
Kind: D
Fidelity: exact (needs `ε < 1`; every theorem carries it) -/
noncomputable def alphaTH (ε ρ α β : ℝ) : ℝ := (pressProb (ρ * ε) α β - ε * β) / (1 - ε)

/-- **The likelihood of a press record** `r : Fin n → Bool` under Bernoulli parameter `p`:
`∏ᵢ (if rᵢ then p else 1 − p)`.
Source: [[corr-wf14-inventory]] 099 / caution-final.md proof §8 (l. 147)
Kind: D
Fidelity: exact -/
def likelihood {n : ℕ} (p : ℝ) (r : Fin n → Bool) : ℝ := ∏ i, if r i then p else 1 - p

/-- `ε_eff ∈ [0, 1]` when `ε`, `ρε`, `μ` are. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma epsEff_mem_Icc {ε ρ μ : ℝ} (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hρε : ρ * ε ∈ Set.Icc (0 : ℝ) 1)
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) : epsEff ε ρ μ ∈ Set.Icc (0 : ℝ) 1 := by
  unfold epsEff
  obtain ⟨hε0, hε1⟩ := hε; obtain ⟨hρ0, hρ1⟩ := hρε; obtain ⟨hμ0, hμ1⟩ := hμ
  constructor <;> nlinarith

/-- `ε_eff ≤ ρ ε` when `ε ≤ ρ ε` and `μ ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma epsEff_le {ε ρ μ : ℝ} (hle : ε ≤ ρ * ε) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    epsEff ε ρ μ ≤ ρ * ε := by
  unfold epsEff; obtain ⟨hμ0, hμ1⟩ := hμ; nlinarith

/-- `ε_eff` at `μ = 0` is `ε`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma epsEff_zero (ε ρ : ℝ) : epsEff ε ρ 0 = ε := by simp [epsEff]

/-- `ε_eff` at `μ = 1` is `ρ ε`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma epsEff_one (ε ρ : ℝ) : epsEff ε ρ 1 = ρ * ε := by simp [epsEff]

/-! ## The heed condition, derived from `corr-three-step` -/

/-- **A press is heeded** iff the below-threshold inequality `Δ₋ ≥ 0` holds on
`corr-three-step`'s two-state instance at `ε := ε_eff`: this is *defined* as the parent's
object, so its provenance is (a).
Source: [[corr-wf14-inventory]] 099 / caution-final.md S8 (l. 75, "a press is heeded iff `ε_eff ≥ ε†`"); position statement §2.13(b)
Kind: D
Fidelity: exact (the parent's `deltaMinus` at `epsEff`)
Hyps: n/a (definition) -/
def Heed (ε ρ α β c h μ : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hρε : ρ * ε ∈ Set.Icc (0 : ℝ) 1)
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) : Prop :=
  0 ≤ (twoState (epsEff ε ρ μ) α β c h (epsEff_mem_Icc hε hρε hμ) hα hβ).deltaMinus () .cont .stop

/-- **The heed condition** `Heed ↔ ε* ≤ ε_eff`, derived by instantiating the parent's
`twoState_deltaMinus_nonneg_iff_epsStar` at `ε_eff` (grade (a)).
Source: [[corr-wf14-inventory]] 099 / caution-final.md S8 (l. 75), proof §8 (l. 141)
Kind: L
Fidelity: exact
Hyps: (a) only (`0 < αc + βh` is the parent's junk-value guard) -/
theorem heed_iff_epsStar {ε ρ α β c h μ : ℝ} (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hρε : ρ * ε ∈ Set.Icc (0 : ℝ) 1) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hpos : 0 < α * c + β * h) :
    Heed ε ρ α β c h μ hε hρε hμ hα hβ ↔ epsStar α β c h ≤ epsEff ε ρ μ :=
  twoState_deltaMinus_nonneg_iff_epsStar _ α β c h _ hα hβ hpos

/-- **The self-suspicion threshold** `μ† = (ε† − ε) / ((ρ − 1) ε)`.
Source: [[corr-wf14-inventory]] 099 / caution-final.md proof §8 (l. 141)
Kind: D
Fidelity: exact (needs `ρ > 1`, `ε > 0`; every theorem carries them) -/
noncomputable def muDagger (ε ρ α β c h : ℝ) : ℝ := (epsStar α β c h - ε) / ((ρ - 1) * ε)

/-- **Heed iff `μ† ≤ μ`** in the regime `ρ > 1`, `ε > 0` (the source adds `ε < ε† < ρε`, which
only says `μ† ∈ (0, 1)`; the equivalence holds without it).
Source: [[corr-wf14-inventory]] 099 / caution-final.md proof §8 (l. 141)
Kind: L
Fidelity: stronger: the regime bounds on `ε†` are not needed for the equivalence
Hyps: (a) only -/
theorem heed_iff_muDagger_le {ε ρ α β c h μ : ℝ} (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hρε : ρ * ε ∈ Set.Icc (0 : ℝ) 1) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hpos : 0 < α * c + β * h) (hρ : 1 < ρ) (hε0 : 0 < ε) :
    Heed ε ρ α β c h μ hε hρε hμ hα hβ ↔ muDagger ε ρ α β c h ≤ μ := by
  rw [heed_iff_epsStar hε hρε hμ hα hβ hpos, muDagger, div_le_iff₀ (by nlinarith), epsEff]
  constructor <;> intro H <;> nlinarith

/-! ## (a) Dogmatism -/

/-- **S8(a), dogmatic:** at `μ = 0` with `ε < ε†` the press is not heeded.
Source: [[corr-wf14-inventory]] 099 / caution-final.md S8(a) (l. 76), proof §8 (l. 143)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem dogmatic_never_heeds {ε ρ α β c h : ℝ} (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hρε : ρ * ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1)
    (hpos : 0 < α * c + β * h) (hlt : ε < epsStar α β c h) :
    ¬ Heed ε ρ α β c h 0 hε hρε ⟨le_rfl, zero_le_one⟩ hα hβ := by
  rw [heed_iff_epsStar hε hρε _ hα hβ hpos, epsEff_zero]
  exact not_le.mpr hlt

/-- **S8(a), dogmatic, both halves:** in the regime `ε < ε† ≤ ρε` the dogmatic agent (`μ = 0`)
does not heed the press, *although heeding is warranted in truth* — the fully self-suspicious
agent (`μ = 1`, so `ε_eff = ρε`) heeds it. The second half is the source's clause "although
heeding is warranted" (audit r1 N7).
Source: [[corr-wf14-inventory]] 099 / caution-final.md S8(a) (l. 76, "never heeds … although heeding is warranted in truth")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem dogmatic_never_heeds_though_warranted {ε ρ α β c h : ℝ} (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hρε : ρ * ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1)
    (hpos : 0 < α * c + β * h) (hlt : ε < epsStar α β c h) (hle : epsStar α β c h ≤ ρ * ε) :
    ¬ Heed ε ρ α β c h 0 hε hρε ⟨le_rfl, zero_le_one⟩ hα hβ ∧
      Heed ε ρ α β c h 1 hε hρε ⟨zero_le_one, le_rfl⟩ hα hβ := by
  refine ⟨dogmatic_never_heeds hε hρε hα hβ hpos hlt, ?_⟩
  rw [heed_iff_epsStar hε hρε _ hα hβ hpos, epsEff_one]
  exact hle

/-- **The Bayesian update of the self-suspicion** from likelihoods `L₁` (reckless) and `L₀`
(calibrated): posterior `μ L₁ / (μ L₁ + (1 − μ) L₀)`.
Source: [[corr-wf14-inventory]] 099 / caution-final.md S8(b) (l. 77, "each press multiplies the odds")
Kind: D
Fidelity: exact (Lean's `x/0 = 0` at zero total likelihood; the theorems below never divide by zero) -/
noncomputable def bayesUpdate (μ L₁ L₀ : ℝ) : ℝ := μ * L₁ / (μ * L₁ + (1 - μ) * L₀)

/-- **Dogmatism is absorbing:** `μ = 0` updates to `0` whatever the likelihoods.
Source: [[corr-wf14-inventory]] 099 / caution-final.md S8(a) (l. 76, "never heeds")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem bayesUpdate_zero (L₁ L₀ : ℝ) : bayesUpdate 0 L₁ L₀ = 0 := by simp [bayesUpdate]

/-- The iterated update along a sequence of likelihood pairs.
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def bayesIter (L₁ L₀ : ℕ → ℝ) (μ₀ : ℝ) : ℕ → ℝ
  | 0 => μ₀
  | t + 1 => bayesUpdate (bayesIter L₁ L₀ μ₀ t) (L₁ t) (L₀ t)

/-- **"Never heeds" is about every `t`:** from `μ₀ = 0` the self-suspicion is `0` at every step
of every press record, so `dogmatic_never_heeds` applies at every `t`.
Source: [[corr-wf14-inventory]] 099 / caution-final.md S8(a) (l. 76)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem bayesIter_zero (L₁ L₀ : ℕ → ℝ) (t : ℕ) : bayesIter L₁ L₀ 0 t = 0 := by
  induction t with
  | zero => rfl
  | succ t ih => simp [bayesIter, ih, bayesUpdate_zero]

/-! ## (b) Non-identification -/

/-- **(i) The trigger-happy hypothesis reproduces the reckless press rate exactly:**
`pressProb ε α' β = pressProb (ρε) α β` for `ε ≠ 1`.
Source: [[corr-wf14-inventory]] 099 / caution-final.md proof §8 (l. 147); caution-adversary.md A8.3 (l. 69)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem pressProb_alphaTH {ε ρ α β : ℝ} (hε1 : ε ≠ 1) :
    pressProb ε (alphaTH ε ρ α β) β = pressProb (ρ * ε) α β := by
  unfold alphaTH pressProb
  have : (1 - ε) ≠ 0 := sub_ne_zero.mpr (Ne.symm hε1)
  field_simp
  ring

/-- **(ii) Every press record has the same likelihood under the two hypotheses.**
Source: [[corr-wf14-inventory]] 099 / caution-final.md proof §8 (l. 147, "likelihood ratio 1 at every step")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem likelihood_th_eq_reck {n : ℕ} {ε ρ α β : ℝ} (hε1 : ε ≠ 1) (r : Fin n → Bool) :
    likelihood (pressProb ε (alphaTH ε ρ α β) β) r = likelihood (pressProb (ρ * ε) α β) r := by
  rw [pressProb_alphaTH hε1]

/-- The likelihood is positive for `0 < p < 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma likelihood_pos {n : ℕ} {p : ℝ} (h0 : 0 < p) (h1 : p < 1) (r : Fin n → Bool) :
    0 < likelihood p r := by
  unfold likelihood
  exact prod_pos fun i _ => by split_ifs <;> linarith

/-- **(ii) The Bayes factor between trigger-happy and reckless is exactly `1` on every record**
(with the likelihood positive so the ratio is a ratio, not a junk `0/0`).
Source: [[corr-wf14-inventory]] 099 / caution-final.md S8(b) (l. 77, "the Bayes factor is 1 forever")
Kind: L (a `div_self` once (i) holds; relabelled from P at audit r1)
Fidelity: exact (trivial once (i) holds — the source's own point)
Hyps: (a) only -/
theorem bayesFactor_th_reck_eq_one {n : ℕ} {ε ρ α β : ℝ} (hε1 : ε ≠ 1)
    (h0 : 0 < pressProb (ρ * ε) α β) (h1 : pressProb (ρ * ε) α β < 1) (r : Fin n → Bool) :
    likelihood (pressProb ε (alphaTH ε ρ α β) β) r / likelihood (pressProb (ρ * ε) α β) r = 1 := by
  rw [likelihood_th_eq_reck hε1, div_self (likelihood_pos h0 h1 r).ne']

/-- **(ii) Posterior odds equal prior odds** between the two hypotheses, on every record.
Source: [[corr-wf14-inventory]] 099 / caution-final.md S8(b) (l. 77, "`μ_t` converges to the prior odds split")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem postOdds_eq_priorOdds {n : ℕ} {ε ρ α β : ℝ} (hε1 : ε ≠ 1)
    (h0 : 0 < pressProb (ρ * ε) α β) (h1 : pressProb (ρ * ε) α β < 1) (r : Fin n → Bool)
    (πth πreck : ℝ) :
    (πth * likelihood (pressProb ε (alphaTH ε ρ α β) β) r) /
      (πreck * likelihood (pressProb (ρ * ε) α β) r) = πth / πreck := by
  rw [likelihood_th_eq_reck hε1, mul_div_mul_right _ _ (likelihood_pos h0 h1 r).ne']

/-- **(iii) Well-formedness: the trigger-happy hypothesis is a hypothesis.** Under
`α, β ∈ [0, 1]`, `1 ≤ ρ`, `0 < ε < 1`, `ρ ε ≤ 1`: `α' ∈ [0, 1]`. Without this, "one number for
three unknowns" would be an identity about a non-probability. The source's `α ≤ β` is not needed
(audit r1).
Source: [[corr-wf14-inventory]] 099 / caution-final.md S8(b) (l. 77); caution-adversary.md A8.3 (l. 69)
Kind: P
Fidelity: stronger: `α ≤ β` dropped
Hyps: (a) only -/
theorem alphaTH_mem_Icc {ε ρ α β : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hρ : 1 ≤ ρ) (hε0 : 0 < ε) (hε1 : ε < 1) (hρε : ρ * ε ≤ 1) :
    alphaTH ε ρ α β ∈ Set.Icc (0 : ℝ) 1 := by
  unfold alphaTH pressProb
  have h1ε : 0 < 1 - ε := sub_pos.mpr hε1
  constructor
  · apply div_nonneg _ h1ε.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hρ) (mul_nonneg hε0.le hβ0),
      mul_nonneg (sub_nonneg.mpr hρε) hα0]
  · rw [div_le_one h1ε]
    nlinarith [mul_nonneg (sub_nonneg.mpr hρ) (mul_nonneg hε0.le (sub_nonneg.mpr hβ1)),
      mul_nonneg (sub_nonneg.mpr hρε) (sub_nonneg.mpr hα1)]

/-- **(iv) The trigger-happy rate is at least the true false-press rate:** `α ≤ α'` under
`α ≤ β`, `1 ≤ ρ`, `0 < ε < 1`.
Source: [[corr-wf14-inventory]] 099 / caution-final.md S8(b) (l. 77, "`α' = 0.163` … instead of `0.1`")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem alpha_le_alphaTH {ε ρ α β : ℝ} (hαβ : α ≤ β) (hρ : 1 ≤ ρ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    α ≤ alphaTH ε ρ α β := by
  unfold alphaTH pressProb
  have h1ε : 0 < 1 - ε := sub_pos.mpr hε1
  rw [le_div_iff₀ h1ε]
  nlinarith [mul_nonneg (sub_nonneg.mpr hρ) (mul_nonneg hε0.le (sub_nonneg.mpr hαβ))]

/-- **`ε*` is monotone in the false-press rate** (for `0 ≤ c`, `0 < βh`).
Source: [[corr-wf14-inventory]] 099 / caution-final.md S8(b) (l. 77, "raises the compliance threshold")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem epsStar_mono_alpha {α₁ α₂ β c h : ℝ} (hα1 : 0 ≤ α₁) (h12 : α₁ ≤ α₂) (hc : 0 ≤ c)
    (hβh : 0 < β * h) : epsStar α₁ β c h ≤ epsStar α₂ β c h := by
  unfold epsStar
  have hd1 : 0 < α₁ * c + β * h := by positivity
  have hd2 : 0 < α₂ * c + β * h := by nlinarith
  rw [div_le_div_iff₀ hd1 hd2]
  nlinarith [mul_nonneg (sub_nonneg.mpr h12) (mul_nonneg hc hβh.le)]

/-- **(iv) The trigger-happy hypothesis raises the threshold:** `ε*(α) ≤ ε*(α')`.
Source: [[corr-wf14-inventory]] 099 / caution-final.md S8(b) (l. 77, "`ε†: 0.091 → 0.140`")
Kind: C
Fidelity: exact
Hyps: (a) only -/
theorem epsStar_le_epsStar_alphaTH {ε ρ α β c h : ℝ} (hα0 : 0 ≤ α) (hαβ : α ≤ β) (hρ : 1 ≤ ρ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hc : 0 ≤ c) (hβh : 0 < β * h) :
    epsStar α β c h ≤ epsStar (alphaTH ε ρ α β) β c h :=
  epsStar_mono_alpha hα0 (alpha_le_alphaTH hαβ hρ hε0 hε1) hc hβh

/-- **The source's numbers** at `(ε, ρ, α, β, c, h) = (1/20, 4, 1/10, 1/2, 1, 2)`: `p_reck = 9/50`,
`α' = 31/190` (`≈ 0.163`), `ε*(α) = 1/11` (`≈ 0.091`), `ε*(α') = 31/221` (`≈ 0.1403`).
Source: [[corr-wf14-inventory]] 099 / caution-final.md proof §8 (l. 147)
Kind: N+
Fidelity: exact (rationals for the source's decimals)
Hyps: none -/
theorem numbers_rho4 :
    pressProb (4 * (1 / 20)) (1 / 10) (1 / 2) = 9 / 50 ∧
    alphaTH (1 / 20) 4 (1 / 10) (1 / 2) = 31 / 190 ∧
    epsStar (1 / 10) (1 / 2) 1 2 = 1 / 11 ∧
    epsStar (31 / 190) (1 / 2) 1 2 = 31 / 221 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [pressProb, alphaTH, epsStar]

/-! ## (b′) Labelled feedback -/

/-- **The labelled-step log-likelihood ratio** of wrong-rate `p₁` against `p₂` on the label
`wrong`: `log (p₁/p₂)` if wrong, `log ((1 − p₁)/(1 − p₂))` if not.
Source: [[corr-wf14-inventory]] 099 / caution-final.md S8(b′) (l. 78), proof §8 (l. 149)
Kind: D
Fidelity: exact -/
noncomputable def logLR (p₁ p₂ : ℝ) : Bool → ℝ
  | true => Real.log (p₁ / p₂)
  | false => Real.log ((1 - p₁) / (1 - p₂))

/-- **The two-point KL divergence** `D(Bern p₁ ‖ Bern p₂)`, written out (no `ShannonInformation`).
Source: [[corr-wf14-inventory]] 099 / caution-final.md S8(b′) (l. 78)
Kind: D
Fidelity: exact -/
noncomputable def klBern (p₁ p₂ : ℝ) : ℝ :=
  p₁ * Real.log (p₁ / p₂) + (1 - p₁) * Real.log ((1 - p₁) / (1 - p₂))

/-- **The expected log-LR under `Bern p₁` is the KL divergence** — the per-labelled-step
information against the calibrated (and the trigger-happy, which shares `ε`) hypothesis.
Source: [[corr-wf14-inventory]] 099 / caution-final.md proof §8 (l. 149)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem expect_logLR_eq_klBern (p₁ p₂ : ℝ) :
    p₁ * logLR p₁ p₂ true + (1 - p₁) * logLR p₁ p₂ false = klBern p₁ p₂ := rfl

/-- **Gibbs' inequality for two points, strict:** `0 < D(Bern p₁ ‖ Bern p₂)` for `p₁ ≠ p₂` in
`(0, 1)` — so labelled feedback identifies the true wrong-rate at a positive rate per step.
Source: [[corr-wf14-inventory]] 099 / caution-final.md S8(b′) (l. 78, "at `ℓ · D_KL` nats per step")
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem klBern_pos {p₁ p₂ : ℝ} (h10 : 0 < p₁) (h11 : p₁ < 1) (h20 : 0 < p₂) (h21 : p₂ < 1)
    (hne : p₁ ≠ p₂) : 0 < klBern p₁ p₂ := by
  unfold klBern
  have hq1 : 0 < 1 - p₁ := sub_pos.mpr h11
  have hq2 : 0 < 1 - p₂ := sub_pos.mpr h21
  -- `log (p₂/p₁) < p₂/p₁ − 1` and `log ((1−p₂)/(1−p₁)) ≤ (1−p₂)/(1−p₁) − 1`
  have hA : Real.log (p₂ / p₁) < p₂ / p₁ - 1 :=
    Real.log_lt_sub_one_of_pos (by positivity) (by
      rw [Ne, div_eq_one_iff_eq h10.ne']; exact hne.symm)
  have hB : Real.log ((1 - p₂) / (1 - p₁)) ≤ (1 - p₂) / (1 - p₁) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div h20.ne' h10.ne'] at hA
  rw [Real.log_div hq2.ne' hq1.ne'] at hB
  rw [Real.log_div h10.ne' h20.ne', Real.log_div hq1.ne' hq2.ne']
  have hA' : p₁ - p₂ < p₁ * (Real.log p₁ - Real.log p₂) := by
    have := mul_lt_mul_of_pos_left hA h10
    have e : p₁ * (p₂ / p₁ - 1) = p₂ - p₁ := by field_simp
    rw [e] at this
    linarith
  have hB' : (1 - p₁) - (1 - p₂) ≤ (1 - p₁) * (Real.log (1 - p₁) - Real.log (1 - p₂)) := by
    have := mul_le_mul_of_nonneg_left hB hq1.le
    have e : (1 - p₁) * ((1 - p₂) / (1 - p₁) - 1) = (1 - p₂) - (1 - p₁) := by field_simp
    rw [e] at this
    linarith
  linarith

/-- **Labelled feedback at `ρ = 4`, `ε = 1/20`:** the per-step KL is positive (the source's
`0.1398` nats is recorded, not proved).
Source: [[corr-wf14-inventory]] 099 / caution-final.md proof §8 (l. 149)
Kind: N+
Fidelity: exact (positivity; the decimal is not a theorem)
Hyps: none -/
theorem klBern_rho4_pos : 0 < klBern (4 * (1 / 20)) (1 / 20) :=
  klBern_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## Whole-line accounting -/

/-- **`ε*` depends on the stakes only through `h/c`:** invariant under `(c, h) ↦ (l c, l h)` for
`l ≠ 0`.
Source: [[corr-wf14-2-inventory]] 2-041 / caution-final.md proof §8 whole-line (l. 151); caution-adversary.md A8.4 (l. 71)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem epsStar_scale {α β c h l : ℝ} (hl : l ≠ 0) :
    epsStar α β (l * c) (l * h) = epsStar α β c h := by
  unfold epsStar
  rw [show α * (l * c) + β * (l * h) = l * (α * c + β * h) by ring,
    show α * (l * c) = l * (α * c) by ring, mul_div_mul_left _ _ hl]

/-- **Whole-line `c` alone (A8.4):** at `(c, h, α, β) = (20, 2, 1/10, 1/2)`, `ε* = 2/3`, and a
press is heeded only if `2/3 ≤ ρ ε` — for every self-suspicion `μ ∈ [0, 1]` and every `ρ ≥ 1`:
self-suspicion cannot produce compliance for an agent right more than a third of the time when
`c` alone scales.
Source: [[corr-wf14-2-inventory]] 2-041 / caution-adversary.md A8.4 (l. 71); caution-final.md proof §8 (l. 151)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem wholeLine_c_alone {ε ρ μ : ℝ} (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hρε : ρ * ε ∈ Set.Icc (0 : ℝ) 1)
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (hρ : 1 ≤ ρ) :
    epsStar (1 / 10) (1 / 2) 20 2 = 2 / 3 ∧
    (Heed ε ρ (1 / 10) (1 / 2) 20 2 μ hε hρε hμ (by norm_num) (by norm_num) → 2 / 3 ≤ ρ * ε) := by
  have hstar : epsStar (1 / 10) (1 / 2) 20 2 = 2 / 3 := by norm_num [epsStar]
  refine ⟨hstar, fun H => ?_⟩
  rw [heed_iff_epsStar hε hρε hμ (by norm_num) (by norm_num) (by norm_num), hstar] at H
  have hle : ε ≤ ρ * ε := by nlinarith [hε.1]
  exact H.trans (epsEff_le hle hμ)

end ModelM

end Cleanroom.Corrigibility.CorrCautionPower

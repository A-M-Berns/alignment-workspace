import Cleanroom.Corrigibility.CorrChannelVoi.Consent

/-!
# `corr-channel-voi` — Reliability: D7, the 1a model and the discount `eρ` (T7)

**D7.** `World × Reliab` (`sound | comp`, `P(comp) = e`, independent of the world); the agent's
self-check in two readings, both defined: **(I)** the script's (`scan_test.py` l. 97–100, the
source of the `[checked]` closed form): sound ⇒ reports the world; compromised ⇒ reports `R`
with probability `ρ` when wrong and *always* when right; **(II)** the prose's (R7 item 29):
compromised ⇒ reports `R` with probability `ρ` regardless of the world. The button reads the
world only.

**T7.** Reading (I): after "check says `R`" the world masses are `(1−ε) : εeρ`, and
`VOI(button | check) = (εeρβh − (1−ε)αc)⁺` under the post-check continue-by-default regime in
product form; positive iff `(1−ε)αc < εeρβh`; outside the regime the closed form overstates
(the source's grid point `e = 1/2, ρ = 1, ε = 1/5` is `Witnesses.w_1a_offregime`). After
"check says `Wr`" the agent stops. Reading (II): the `R`-branch closed form carries the factor
`(1 − e + eρ)` on the `αc` term; and — Known issue 2 sharpened — under (II) the `Wr` branch is
*not* decisive: a compromised check says `Wr` in the right world with mass `(1−ε)e(1−ρ)`, so
"after `Wr` the agent stops" needs a hypothesis there (`Witnesses.w_readingII_continues_on_Wr`).
-/

namespace Cleanroom.Corrigibility.CorrChannelVoi

open Finset hiding expect
open FactoredSpaces
open Cleanroom.Found.LitDdbFrames.Blackwell
open Cleanroom.Trust.TtFiniteFrames
open Cleanroom.Found.CorrThreeStep
open Cleanroom.Found.CorrThreeStep.ThreeStep

noncomputable section

set_option linter.unusedSectionVars false

/-- The reliability latent: the agent's self-check is sound or compromised.
Source: substitution.md R7 item 29 (`E` = "the agent's self-check is compromised")
Kind: D
Fidelity: exact -/
inductive Reliab
  | sound
  | comp
  deriving DecidableEq

/-- `Reliab` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype Reliab := ⟨{Reliab.sound, Reliab.comp}, fun x => by cases x <;> simp⟩

/-- Sums over `Reliab`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem Reliab.sum_eq (f : Reliab → ℝ) : ∑ r, f r = f .sound + f .comp := by
  rw [show (univ : Finset Reliab) = {Reliab.sound, Reliab.comp} from rfl, Finset.sum_pair (by decide)]

/-- `P(comp) = e`. Source: substitution.md R7 item 29. Kind: D. Fidelity: exact -/
def reliabPrior (e : ℝ) (he : e ∈ Set.Icc (0 : ℝ) 1) : Distr Reliab where
  mass r := match r with
    | .sound => 1 - e
    | .comp => e
  nonneg r := by cases r <;> simp <;> linarith [he.1, he.2]
  sum_eq_one := by rw [Reliab.sum_eq]; simp

/-- The self-check kernel, reading (I) (the script's): signal `0` = "`R`", `1` = "`Wr`".
Source: `scan_test.py` l. 97–100 (`button_voi_after_scan`); [[corr-wf14-inventory]] 042
Kind: D
Fidelity: exact (the script's model) -/
def checkKernelI (ρ : ℝ) : World → Reliab → Fin 2 → ℝ
  | .right, _ => ![1, 0]
  | .wrong, .sound => ![0, 1]
  | .wrong, .comp => ![ρ, 1 - ρ]

/-- The self-check kernel, reading (II) (the prose's): a compromised check says `R` with
probability `ρ` in either world.
Source: substitution.md R7 item 29 ("reports `R` with probability `ρ` regardless of `W`")
Kind: D
Fidelity: exact (the prose's model) -/
def checkKernelII (ρ : ℝ) : World → Reliab → Fin 2 → ℝ
  | .right, .sound => ![1, 0]
  | .wrong, .sound => ![0, 1]
  | _, .comp => ![ρ, 1 - ρ]

/-- **D7 (I). The self-check, script reading**, as an experiment on `World × Reliab`.
Source: `scan_test.py` l. 97–100; [[corr-wf14-inventory]] 042
Kind: D
Fidelity: exact -/
def selfCheckI (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : Experiment (World × Reliab) (Fin 2) where
  k p := checkKernelI ρ p.1 p.2
  k_mem := by
    rintro ⟨w, r⟩
    cases w <;> cases r <;>
      exact ⟨fun s => by fin_cases s <;> simp [checkKernelI] <;> linarith [hρ.1, hρ.2],
        by simp [checkKernelI, Fin.sum_univ_two]⟩

/-- **D7 (II). The self-check, prose reading.**
Source: substitution.md R7 item 29
Kind: D
Fidelity: exact -/
def selfCheckII (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : Experiment (World × Reliab) (Fin 2) where
  k p := checkKernelII ρ p.1 p.2
  k_mem := by
    rintro ⟨w, r⟩
    cases w <;> cases r <;>
      exact ⟨fun s => by fin_cases s <;> simp [checkKernelII] <;> linarith [hρ.1, hρ.2],
        by simp [checkKernelII, Fin.sum_univ_two]⟩

section Model

variable (ε e ρ α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (he : e ∈ Set.Icc (0 : ℝ) 1)
  (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- The 1a prior: `twoPoint ε ⊗ reliabPrior e`. Source: substitution.md R7 item 29. Kind: D. Fidelity: exact -/
abbrev relPrior : Distr (World × Reliab) := distrProd (twoPoint ε hε) (reliabPrior e he)

/-- The 1a stakes: the world's stakes, independent of reliability. Source: substitution.md R7. Kind: D. Fidelity: exact -/
def relStakes : World × Reliab → ℝ := fun p => twoValue c h .cont p.1

/-- The button on the 1a world reads the world only. Source: substitution.md R7 item 29. Kind: D. Fidelity: exact -/
abbrev relButton : Experiment (World × Reliab) (Fin 2) := expComap Prod.fst (twoButton α β hα hβ)

/-! ### Reading (I): signal gains -/

/-- Check alone, signal `R`: gain `(1−ε)c − εeρh` — the world masses after `R` are `(1−ε) : εeρ`
(the source's posterior odds, in product form).
Source: substitution.md R7 item 30 (`ε' = εeρ/(εeρ + 1 − ε)`)
Kind: L
Fidelity: exact -/
theorem checkI_gain_R :
    signalGain (relPrior ε e hε he) (selfCheckI ρ hρ) (relStakes c h) 0 = (1 - ε) * c - ε * e * ρ * h := by
  simp [signalGain, Fintype.sum_prod_type, World.sum_eq, Reliab.sum_eq, reliabPrior, selfCheckI,
    checkKernelI, relStakes, twoValue]
  ring

/-- Check alone, signal `Wr`: gain `−ε(1−eρ)h ≤ 0` — only the wrong world reports `Wr` (the
sound check always, the compromised one with probability `1−ρ`), so after `Wr` the agent stops.
Source: substitution.md R7 item 30 ("After 'scan says `Wr`' the agent shuts down")
Kind: L
Fidelity: exact -/
theorem checkI_gain_Wr :
    signalGain (relPrior ε e hε he) (selfCheckI ρ hρ) (relStakes c h) 1 = -(ε * (1 - e * ρ) * h) := by
  simp [signalGain, Fintype.sum_prod_type, World.sum_eq, Reliab.sum_eq, reliabPrior, selfCheckI,
    checkKernelI, relStakes, twoValue]
  ring

/-- Check and button, cell `(R, press)`: `(1−ε)αc − εeρβh`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem checkI_button_gain_R_press :
    signalGain (relPrior ε e hε he) (expProd (selfCheckI ρ hρ) (relButton α β hα hβ)) (relStakes c h) (0, 0) =
      (1 - ε) * α * c - ε * e * ρ * β * h := by
  simp [signalGain, Fintype.sum_prod_type, World.sum_eq, Reliab.sum_eq, reliabPrior, selfCheckI,
    checkKernelI, relStakes, twoValue, expProd, expComap]
  ring

/-- Cell `(R, silent)`: `(1−ε)(1−α)c − εeρ(1−β)h`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem checkI_button_gain_R_silent :
    signalGain (relPrior ε e hε he) (expProd (selfCheckI ρ hρ) (relButton α β hα hβ)) (relStakes c h) (0, 1) =
      (1 - ε) * (1 - α) * c - ε * e * ρ * (1 - β) * h := by
  simp [signalGain, Fintype.sum_prod_type, World.sum_eq, Reliab.sum_eq, reliabPrior, selfCheckI,
    checkKernelI, relStakes, twoValue, expProd, expComap]
  ring

/-- Cell `(Wr, press)`: `−ε(1−eρ)βh`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem checkI_button_gain_Wr_press :
    signalGain (relPrior ε e hε he) (expProd (selfCheckI ρ hρ) (relButton α β hα hβ)) (relStakes c h) (1, 0) =
      -(ε * (1 - e * ρ) * β * h) := by
  simp [signalGain, Fintype.sum_prod_type, World.sum_eq, Reliab.sum_eq, reliabPrior, selfCheckI,
    checkKernelI, relStakes, twoValue, expProd, expComap]
  ring

/-- Cell `(Wr, silent)`: `−ε(1−eρ)(1−β)h`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem checkI_button_gain_Wr_silent :
    signalGain (relPrior ε e hε he) (expProd (selfCheckI ρ hρ) (relButton α β hα hβ)) (relStakes c h) (1, 1) =
      -(ε * (1 - e * ρ) * (1 - β) * h) := by
  simp [signalGain, Fintype.sum_prod_type, World.sum_eq, Reliab.sum_eq, reliabPrior, selfCheckI,
    checkKernelI, relStakes, twoValue, expProd, expComap]
  ring

/-- **T7 (I), regime-free**: `VOI(button | check) = max(A, 0) + max(B, 0) − max(A + B, 0)` with
`A = (1−ε)αc − εeρβh`, `B = (1−ε)(1−α)c − εeρ(1−β)h` (`h ≥ 0`, so the `Wr` cells contribute
nothing).
Source: substitution.md R7 item 30 (derived here in regime-free form)
Kind: P
Fidelity: stronger: regime-free
Hyps: (a) `0 ≤ h` -/
theorem selfCheckI_voiGiven_eq (hh : 0 ≤ h) :
    voiGiven (relPrior ε e hε he) (selfCheckI ρ hρ) (relButton α β hα hβ) (relStakes c h) =
      max ((1 - ε) * α * c - ε * e * ρ * β * h) 0 +
        max ((1 - ε) * (1 - α) * c - ε * e * ρ * (1 - β) * h) 0 -
        max ((1 - ε) * c - ε * e * ρ * h) 0 := by
  unfold voiGiven
  rw [sensorValue_eq_sum_max, sensorValue_eq_sum_max, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  rw [checkI_button_gain_R_press, checkI_button_gain_R_silent, checkI_button_gain_Wr_press,
    checkI_button_gain_Wr_silent, checkI_gain_R, checkI_gain_Wr]
  have heρ : 0 ≤ 1 - e * ρ := by nlinarith [he.1, he.2, hρ.1, hρ.2]
  have h1 : 0 ≤ ε * (1 - e * ρ) * β * h := by
    have := mul_nonneg (mul_nonneg hε.1 heρ) hβ.1; nlinarith
  have h2 : 0 ≤ ε * (1 - e * ρ) * (1 - β) * h := by
    have := mul_nonneg (mul_nonneg hε.1 heρ) (sub_nonneg.mpr hβ.2); nlinarith
  have h3 : 0 ≤ ε * (1 - e * ρ) * h := by
    have := mul_nonneg hε.1 heρ; nlinarith
  rw [max_eq_right (show -(ε * (1 - e * ρ) * β * h) ≤ 0 by linarith),
    max_eq_right (show -(ε * (1 - e * ρ) * (1 - β) * h) ≤ 0 by linarith),
    max_eq_right (show -(ε * (1 - e * ρ) * h) ≤ 0 by linarith)]
  ring

/-- **T7 (I), the closed form (load-bearing for R7)**: under the post-check continue-by-default
regime in product form — `εeρh ≤ (1−ε)c` and `εeρ(1−β)h ≤ (1−ε)(1−α)c` —
`VOI(button | check) = (εeρβh − (1−ε)αc)⁺`: the base-rate form with `ε` replaced by `εeρ`, the
self-distrust the check cannot remove.
Source: substitution.md R7 item 30; miri.md I10.8(b) ("dissolves, at a discount"); [[corr-wf14-inventory]] 042
Kind: C
Fidelity: exact (the mandate's regime hypothesis plus the silence-continues clause; the latter follows from `α ≤ β`, `selfCheckI_voiGiven_closed_of_le`)
Hyps: (a) the regime named in product form; `0 ≤ h` -/
theorem selfCheckI_voiGiven_closed (hh : 0 ≤ h) (hprior : ε * e * ρ * h ≤ (1 - ε) * c)
    (hsilent : ε * e * ρ * (1 - β) * h ≤ (1 - ε) * (1 - α) * c) :
    voiGiven (relPrior ε e hε he) (selfCheckI ρ hρ) (relButton α β hα hβ) (relStakes c h) =
      max (ε * e * ρ * β * h - (1 - ε) * α * c) 0 := by
  rw [selfCheckI_voiGiven_eq ε e ρ α β c h hε he hρ hα hβ hh,
    max_eq_left (show (0 : ℝ) ≤ (1 - ε) * (1 - α) * c - ε * e * ρ * (1 - β) * h by linarith),
    max_eq_left (show (0 : ℝ) ≤ (1 - ε) * c - ε * e * ρ * h by linarith)]
  rcases le_total 0 ((1 - ε) * α * c - ε * e * ρ * β * h) with h0 | h0
  · rw [max_eq_left h0, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h0, max_eq_left (by linarith)]; ring

include hε he hρ hα in
/-- Under `α ≤ β`, `c, h ≥ 0`, the mandate's single regime hypothesis `εeρh ≤ (1−ε)c` gives
the silence-continues clause.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem selfCheckI_silent_of_le (hαβ : α ≤ β) (hc : 0 ≤ c) (hh : 0 ≤ h)
    (hprior : ε * e * ρ * h ≤ (1 - ε) * c) :
    ε * e * ρ * (1 - β) * h ≤ (1 - ε) * (1 - α) * c := by
  have hk : 0 ≤ ε * e * ρ := mul_nonneg (mul_nonneg hε.1 he.1) hρ.1
  have h1 : ε * e * ρ * (1 - β) * h ≤ ε * e * ρ * (1 - α) * h := by
    have := mul_nonneg hk hh; nlinarith
  have h2 : ε * e * ρ * (1 - α) * h ≤ (1 - ε) * (1 - α) * c := by
    have := sub_nonneg.mpr hα.2; nlinarith
  linarith

/-- **T7 (I), the closed form under the mandate's hypotheses**: `α ≤ β`, `c, h ≥ 0`,
`εeρh ≤ (1−ε)c` ⟹ `VOI(button | check) = (εeρβh − (1−ε)αc)⁺`.
Source: substitution.md R7 item 30
Kind: C
Fidelity: exact -/
theorem selfCheckI_voiGiven_closed_of_le (hαβ : α ≤ β) (hc : 0 ≤ c) (hh : 0 ≤ h)
    (hprior : ε * e * ρ * h ≤ (1 - ε) * c) :
    voiGiven (relPrior ε e hε he) (selfCheckI ρ hρ) (relButton α β hα hβ) (relStakes c h) =
      max (ε * e * ρ * β * h - (1 - ε) * α * c) 0 :=
  selfCheckI_voiGiven_closed ε e ρ α β c h hε he hρ hα hβ hh hprior
    (selfCheckI_silent_of_le ε e ρ α β c h hε he hρ hα hαβ hc hh hprior)

/-- **T7 (I), positivity**: in the regime, the button survives the check iff `(1−ε)αc < εeρβh`
— the base-rate inequality at the discounted error rate `εeρ`.
Source: substitution.md R7 item 30 ("positive iff `α/β ≤ (εeρ/(1−ε))·(h/c)`", strict here)
Kind: L
Fidelity: exact (strict form) -/
theorem selfCheckI_voiGiven_pos_iff (hh : 0 ≤ h) (hprior : ε * e * ρ * h ≤ (1 - ε) * c)
    (hsilent : ε * e * ρ * (1 - β) * h ≤ (1 - ε) * (1 - α) * c) :
    0 < voiGiven (relPrior ε e hε he) (selfCheckI ρ hρ) (relButton α β hα hβ) (relStakes c h) ↔
      (1 - ε) * α * c < ε * e * ρ * β * h := by
  rw [selfCheckI_voiGiven_closed ε e ρ α β c h hε he hρ hα hβ hh hprior hsilent]
  constructor
  · intro H
    rcases lt_max_iff.mp H with H | H
    · linarith
    · exact absurd H (lt_irrefl 0)
  · intro H; exact lt_max_of_lt_left (by linarith)

/-- **After "check says `Wr`" the agent stops (reading I)**: stop is optimal on both `Wr` cells
(`h ≥ 0`).
Source: substitution.md R7 item 30
Kind: L
Fidelity: exact -/
theorem selfCheckI_stops_on_Wr (hh : 0 ≤ h) :
    signalGain (relPrior ε e hε he) (expProd (selfCheckI ρ hρ) (relButton α β hα hβ)) (relStakes c h) (1, 0) ≤ 0 ∧
    signalGain (relPrior ε e hε he) (expProd (selfCheckI ρ hρ) (relButton α β hα hβ)) (relStakes c h) (1, 1) ≤ 0 := by
  rw [checkI_button_gain_Wr_press, checkI_button_gain_Wr_silent]
  have heρ : 0 ≤ 1 - e * ρ := by nlinarith [he.1, he.2, hρ.1, hρ.2]
  have h0 := mul_nonneg hε.1 heρ
  constructor
  · nlinarith [mul_nonneg h0 hβ.1, hh]
  · nlinarith [mul_nonneg h0 (sub_nonneg.mpr hβ.2), hh]

/-! ### Reading (II): signal gains and the `Wr` branch -/

/-- Check alone (II), signal `R`: `(1−ε)(1−e+eρ)c − εeρh` — the odds `εeρ : (1−ε)(1−e+eρ)`.
Source: [[corr-channel-voi-mandate]] T7 (reading II)
Kind: L
Fidelity: exact -/
theorem checkII_gain_R :
    signalGain (relPrior ε e hε he) (selfCheckII ρ hρ) (relStakes c h) 0 =
      (1 - ε) * (1 - e + e * ρ) * c - ε * e * ρ * h := by
  simp [signalGain, Fintype.sum_prod_type, World.sum_eq, Reliab.sum_eq, reliabPrior, selfCheckII,
    checkKernelII, relStakes, twoValue]
  ring

/-- Check alone (II), signal `Wr`: `(1−ε)e(1−ρ)c − ε(1−eρ)h` — **not** nonpositive in general
(Known issue 2, sharpened): a compromised check says `Wr` in the right world too.
Source: [[corr-channel-voi-mandate]] Known issue 2; substitution.md R7 item 29
Kind: L
Fidelity: exact -/
theorem checkII_gain_Wr :
    signalGain (relPrior ε e hε he) (selfCheckII ρ hρ) (relStakes c h) 1 =
      (1 - ε) * e * (1 - ρ) * c - ε * (1 - e * ρ) * h := by
  simp [signalGain, Fintype.sum_prod_type, World.sum_eq, Reliab.sum_eq, reliabPrior, selfCheckII,
    checkKernelII, relStakes, twoValue]
  ring

/-- (II) cell `(R, press)`: `(1−ε)(1−e+eρ)αc − εeρβh`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem checkII_button_gain_R_press :
    signalGain (relPrior ε e hε he) (expProd (selfCheckII ρ hρ) (relButton α β hα hβ)) (relStakes c h) (0, 0) =
      (1 - ε) * (1 - e + e * ρ) * α * c - ε * e * ρ * β * h := by
  simp [signalGain, Fintype.sum_prod_type, World.sum_eq, Reliab.sum_eq, reliabPrior, selfCheckII,
    checkKernelII, relStakes, twoValue, expProd, expComap]
  ring

/-- (II) cell `(R, silent)`: `(1−ε)(1−e+eρ)(1−α)c − εeρ(1−β)h`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem checkII_button_gain_R_silent :
    signalGain (relPrior ε e hε he) (expProd (selfCheckII ρ hρ) (relButton α β hα hβ)) (relStakes c h) (0, 1) =
      (1 - ε) * (1 - e + e * ρ) * (1 - α) * c - ε * e * ρ * (1 - β) * h := by
  simp [signalGain, Fintype.sum_prod_type, World.sum_eq, Reliab.sum_eq, reliabPrior, selfCheckII,
    checkKernelII, relStakes, twoValue, expProd, expComap]
  ring

/-- (II) cell `(Wr, press)`: `(1−ε)e(1−ρ)αc − ε(1−eρ)βh`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem checkII_button_gain_Wr_press :
    signalGain (relPrior ε e hε he) (expProd (selfCheckII ρ hρ) (relButton α β hα hβ)) (relStakes c h) (1, 0) =
      (1 - ε) * e * (1 - ρ) * α * c - ε * (1 - e * ρ) * β * h := by
  simp [signalGain, Fintype.sum_prod_type, World.sum_eq, Reliab.sum_eq, reliabPrior, selfCheckII,
    checkKernelII, relStakes, twoValue, expProd, expComap]
  ring

/-- (II) cell `(Wr, silent)`: `(1−ε)e(1−ρ)(1−α)c − ε(1−eρ)(1−β)h`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem checkII_button_gain_Wr_silent :
    signalGain (relPrior ε e hε he) (expProd (selfCheckII ρ hρ) (relButton α β hα hβ)) (relStakes c h) (1, 1) =
      (1 - ε) * e * (1 - ρ) * (1 - α) * c - ε * (1 - e * ρ) * (1 - β) * h := by
  simp [signalGain, Fintype.sum_prod_type, World.sum_eq, Reliab.sum_eq, reliabPrior, selfCheckII,
    checkKernelII, relStakes, twoValue, expProd, expComap]
  ring

/-- **T7 (II), regime-free**: `VOI(button | check)` in the prose's reading is the `R`-branch term
plus the `Wr`-branch term, each of the form `max(P,0) + max(S,0) − max(P + S, 0)`.
Source: [[corr-channel-voi-mandate]] T7 (reading II); Known issue 2
Kind: C (`sensorValue_eq_sum_max` twice + the six cell-gain lemmas + `ring`, no sign reasoning — unlike `selfCheckI_voiGiven_eq`, which drops the `Wr` maxima by sign; regraded from P in audit r2)
Fidelity: stronger: regime-free, both branches -/
theorem selfCheckII_voiGiven_eq :
    voiGiven (relPrior ε e hε he) (selfCheckII ρ hρ) (relButton α β hα hβ) (relStakes c h) =
      (max ((1 - ε) * (1 - e + e * ρ) * α * c - ε * e * ρ * β * h) 0 +
        max ((1 - ε) * (1 - e + e * ρ) * (1 - α) * c - ε * e * ρ * (1 - β) * h) 0 -
        max ((1 - ε) * (1 - e + e * ρ) * c - ε * e * ρ * h) 0) +
      (max ((1 - ε) * e * (1 - ρ) * α * c - ε * (1 - e * ρ) * β * h) 0 +
        max ((1 - ε) * e * (1 - ρ) * (1 - α) * c - ε * (1 - e * ρ) * (1 - β) * h) 0 -
        max ((1 - ε) * e * (1 - ρ) * c - ε * (1 - e * ρ) * h) 0) := by
  unfold voiGiven
  rw [sensorValue_eq_sum_max, sensorValue_eq_sum_max, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  rw [checkII_button_gain_R_press, checkII_button_gain_R_silent, checkII_button_gain_Wr_press,
    checkII_button_gain_Wr_silent, checkII_gain_R, checkII_gain_Wr]
  ring

/-- **T7 (II), the `R`-branch closed form**: under the `R`-branch regime
(`εeρ(1−β)h ≤ (1−ε)(1−e+eρ)(1−α)c` and `εeρh ≤ (1−ε)(1−e+eρ)c`) and with the `Wr` branch
decisive (`Wr` cells nonpositive), `VOI(button | check) = (εeρβh − (1−ε)(1−e+eρ)αc)⁺` — the
factor `(1 − e + eρ)` on the `αc` term. The `Wr`-decisiveness hypotheses are *automatic* in
reading (I) and *not* in reading (II) (Known issue 2).
Source: [[corr-channel-voi-mandate]] T7 (reading II)
Kind: C
Fidelity: exact
Hyps: (a) the four product-form conditions named -/
theorem selfCheckII_voiGiven_closed
    (hRs : ε * e * ρ * (1 - β) * h ≤ (1 - ε) * (1 - e + e * ρ) * (1 - α) * c)
    (hR : ε * e * ρ * h ≤ (1 - ε) * (1 - e + e * ρ) * c)
    (hWp : (1 - ε) * e * (1 - ρ) * α * c ≤ ε * (1 - e * ρ) * β * h)
    (hWs : (1 - ε) * e * (1 - ρ) * (1 - α) * c ≤ ε * (1 - e * ρ) * (1 - β) * h) :
    voiGiven (relPrior ε e hε he) (selfCheckII ρ hρ) (relButton α β hα hβ) (relStakes c h) =
      max (ε * e * ρ * β * h - (1 - ε) * (1 - e + e * ρ) * α * c) 0 := by
  rw [selfCheckII_voiGiven_eq,
    max_eq_left (show (0 : ℝ) ≤ (1 - ε) * (1 - e + e * ρ) * (1 - α) * c - ε * e * ρ * (1 - β) * h by
      linarith),
    max_eq_left (show (0 : ℝ) ≤ (1 - ε) * (1 - e + e * ρ) * c - ε * e * ρ * h by linarith),
    max_eq_right (show (1 - ε) * e * (1 - ρ) * α * c - ε * (1 - e * ρ) * β * h ≤ 0 by linarith),
    max_eq_right (show (1 - ε) * e * (1 - ρ) * (1 - α) * c - ε * (1 - e * ρ) * (1 - β) * h ≤ 0 by
      linarith),
    max_eq_right (show (1 - ε) * e * (1 - ρ) * c - ε * (1 - e * ρ) * h ≤ 0 by linarith)]
  rcases le_total 0 ((1 - ε) * (1 - e + e * ρ) * α * c - ε * e * ρ * β * h) with h0 | h0
  · rw [max_eq_left h0, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h0, max_eq_left (by linarith)]; ring

/-- **T7 (II), positivity**: under the four conditions, `VOI(button | check) > 0` iff
`(1−ε)(1−e+eρ)αc < εeρβh` — reading (I)'s criterion with the factor on the `αc` term.
Source: substitution.md R7 item 30 (reading (II)); [[corr-channel-voi-mandate]] T7
Kind: L (`selfCheckII_voiGiven_closed` + the sign of a `max`)
Fidelity: exact -/
theorem selfCheckII_voiGiven_pos_iff
    (hRs : ε * e * ρ * (1 - β) * h ≤ (1 - ε) * (1 - e + e * ρ) * (1 - α) * c)
    (hR : ε * e * ρ * h ≤ (1 - ε) * (1 - e + e * ρ) * c)
    (hWp : (1 - ε) * e * (1 - ρ) * α * c ≤ ε * (1 - e * ρ) * β * h)
    (hWs : (1 - ε) * e * (1 - ρ) * (1 - α) * c ≤ ε * (1 - e * ρ) * (1 - β) * h) :
    0 < voiGiven (relPrior ε e hε he) (selfCheckII ρ hρ) (relButton α β hα hβ) (relStakes c h) ↔
      (1 - ε) * (1 - e + e * ρ) * α * c < ε * e * ρ * β * h := by
  rw [selfCheckII_voiGiven_closed ε e ρ α β c h hε he hρ hα hβ hRs hR hWp hWs]
  constructor
  · intro H
    rcases lt_max_iff.mp H with H | H
    · linarith
    · exact absurd H (lt_irrefl 0)
  · intro H; exact lt_max_of_lt_left (by linarith)

include hε he hρ hα in
/-- The factor's work is nonnegative: `(1−ε)(1−e+eρ)αc ≤ (1−ε)αc`, the difference being
`(1−ε)·e(1−ρ)·αc ≥ 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem factor_term_le (hc : 0 ≤ c) :
    (1 - ε) * (1 - e + e * ρ) * α * c ≤ (1 - ε) * α * c := by
  have hnn : 0 ≤ (1 - ε) * e * (1 - ρ) * α * c :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hε.2) he.1)
      (sub_nonneg.mpr hρ.2)) hα.1) hc
  have key : (1 - ε) * α * c - (1 - ε) * (1 - e + e * ρ) * α * c =
      (1 - ε) * e * (1 - ρ) * α * c := by ring
  linarith

/-- **T7, the two readings compared (push, repair round 2)**: wherever both closed forms hold,
the prose's reading (II) values the button *at least* as much as the script's reading (I):
`VOI_I(button | check) ≤ VOI_II(button | check)`. The reason is the factor: a compromised check
that says `R` only with probability `ρ` in the right world leaves *less* of the honest-`R` mass
`(1−ε)αc` to be lost, and `max` is monotone. (`w_readings_differ` is the strict instance.)
Source: [[corr-channel-voi-mandate]] T7 (both readings); Known issue 2 — the natural next result
Kind: C (both closed forms + `factor_term_le` + monotonicity of `max`)
Fidelity: exact
Hyps: (a) reading (I)'s two and reading (II)'s four regime conditions, `0 ≤ c`, `0 ≤ h`, all named -/
theorem selfCheckI_le_selfCheckII (hc : 0 ≤ c) (hh : 0 ≤ h)
    (hprior : ε * e * ρ * h ≤ (1 - ε) * c)
    (hsilent : ε * e * ρ * (1 - β) * h ≤ (1 - ε) * (1 - α) * c)
    (hRs : ε * e * ρ * (1 - β) * h ≤ (1 - ε) * (1 - e + e * ρ) * (1 - α) * c)
    (hR : ε * e * ρ * h ≤ (1 - ε) * (1 - e + e * ρ) * c)
    (hWp : (1 - ε) * e * (1 - ρ) * α * c ≤ ε * (1 - e * ρ) * β * h)
    (hWs : (1 - ε) * e * (1 - ρ) * (1 - α) * c ≤ ε * (1 - e * ρ) * (1 - β) * h) :
    voiGiven (relPrior ε e hε he) (selfCheckI ρ hρ) (relButton α β hα hβ) (relStakes c h) ≤
      voiGiven (relPrior ε e hε he) (selfCheckII ρ hρ) (relButton α β hα hβ) (relStakes c h) := by
  rw [selfCheckI_voiGiven_closed ε e ρ α β c h hε he hρ hα hβ hh hprior hsilent,
    selfCheckII_voiGiven_closed ε e ρ α β c h hε he hρ hα hβ hRs hR hWp hWs]
  have := factor_term_le ε e ρ α c hε he hρ hα hc
  exact max_le_max (by linarith) le_rfl

/-- **T7, the gap between the readings (push, repair round 2)**: where both closed forms hold
and reading (I)'s value is in its positive part (`(1−ε)αc ≤ εeρβh`), the two readings differ by
exactly the factor's work, `VOI_II − VOI_I = (1−ε)·e(1−ρ)·αc`: zero iff `α = 0`, `e = 0`,
`ρ = 1`, `ε = 1` or `c = 0` — the complete list of where the prose and the script agree in value
(the shipped `α = 0` cell `w_readingII_closed` is one of them, which is why it is N− for the factor).
Source: [[corr-channel-voi-mandate]] T7; Known issue 2 — the natural next result
Kind: C (both closed forms in their positive parts + `ring`)
Fidelity: exact
Hyps: (a) the regimes and reading (I)'s positivity, all named -/
theorem selfCheck_readings_gap (hc : 0 ≤ c) (hh : 0 ≤ h)
    (hprior : ε * e * ρ * h ≤ (1 - ε) * c)
    (hsilent : ε * e * ρ * (1 - β) * h ≤ (1 - ε) * (1 - α) * c)
    (hRs : ε * e * ρ * (1 - β) * h ≤ (1 - ε) * (1 - e + e * ρ) * (1 - α) * c)
    (hR : ε * e * ρ * h ≤ (1 - ε) * (1 - e + e * ρ) * c)
    (hWp : (1 - ε) * e * (1 - ρ) * α * c ≤ ε * (1 - e * ρ) * β * h)
    (hWs : (1 - ε) * e * (1 - ρ) * (1 - α) * c ≤ ε * (1 - e * ρ) * (1 - β) * h)
    (hposI : (1 - ε) * α * c ≤ ε * e * ρ * β * h) :
    voiGiven (relPrior ε e hε he) (selfCheckII ρ hρ) (relButton α β hα hβ) (relStakes c h) -
        voiGiven (relPrior ε e hε he) (selfCheckI ρ hρ) (relButton α β hα hβ) (relStakes c h) =
      (1 - ε) * e * (1 - ρ) * α * c := by
  rw [selfCheckI_voiGiven_closed ε e ρ α β c h hε he hρ hα hβ hh hprior hsilent,
    selfCheckII_voiGiven_closed ε e ρ α β c h hε he hρ hα hβ hRs hR hWp hWs]
  have := factor_term_le ε e ρ α c hε he hρ hα hc
  rw [max_eq_left (by linarith), max_eq_left (by linarith)]
  ring

end Model

end

end Cleanroom.Corrigibility.CorrChannelVoi

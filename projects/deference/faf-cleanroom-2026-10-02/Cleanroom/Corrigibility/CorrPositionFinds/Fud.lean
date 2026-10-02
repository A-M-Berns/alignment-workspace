import Cleanroom.Corrigibility.CorrPositionFinds.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Algebra.Monoid

/-!
# `corr-position-finds` — T3, T4: fully updated deference as arithmetic; Good's theorem up to `εβh`

**T3** (position statement §1, ABRAM): "So long as learning is anticipated to be legitimate, the
reflection principle holds, so there is no fully updated deference problem." On the two-state
instance at fixed `(α, β, c, h)`: (a) for every `ε ∈ (0, ε*)` desideratum 1 fails *and* the
two-option value of the button is `0` — the band is nonempty for every `α > 0`; (b) the escape
"`α` falls in step", `α = κ·ε`: D1 holds at every `ε ∈ (0, 1)` iff `κc ≤ βh` (the same threshold
for the strict form — see the docstring). (c) is the findings file's verdict.

**T4** (§1, ABRAM): "help repair the shutdown button … is just a consequence of Good's
theorem." (a) `voiButton2(ε_t) → 0` along any `ε_t → 0`, with no regime assumption; (b) in the
regime `voiButton2 = max(Δ₋, 0)` is antitone in `α` and monotone in `β` — improvement is valued
at least as highly as repair.

Every object is `corr-three-step`'s.
-/

namespace Cleanroom.Corrigibility.CorrPositionFinds

open FactoredSpaces Finset Filter Topology Cleanroom.Found.CorrThreeStep
  Cleanroom.Found.CorrThreeStep.ThreeStep

/-! ## T3(a) — FUD as a limit statement -/

section Band

variable (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- `ε* ≤ c/(c + h)` whenever `α ≤ β` (and `0 ≤ α`, `0 < β`, `0 < c`, `0 < h`): the failing band
sits inside the continue-by-default threshold.
Source: none: infrastructure (the arithmetic linking `epsStar` to `complianceThreshold`)
Kind: L
Fidelity: n/a -/
lemma epsStar_le_complianceThreshold (hα0 : 0 ≤ α) (hβ0 : 0 < β) (hc : 0 < c) (hh : 0 < h)
    (hαβ : α ≤ β) : epsStar α β c h ≤ complianceThreshold c h := by
  unfold epsStar complianceThreshold
  have hden : 0 < α * c + β * h := add_pos_of_nonneg_of_pos (mul_nonneg hα0 hc.le) (mul_pos hβ0 hh)
  rw [div_le_div_iff₀ hden (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_right hαβ (mul_pos hc hh).le]

/-- `0 < ε*` for `0 < α`, `0 < β`, `0 < c`, `0 < h`.
Source: [[corr-wf13-inventory]] 094 / position statement §2.13(b) (the band is nonempty)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem epsStar_pos (hα0 : 0 < α) (hβ0 : 0 < β) (hc : 0 < c) (hh : 0 < h) :
    0 < epsStar α β c h :=
  div_pos (mul_pos hα0 hc) (add_pos (mul_pos hα0 hc) (mul_pos hβ0 hh))

/-- `ε* < 1` for `0 ≤ α`, `0 < β`, `0 ≤ c`, `0 < h`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma epsStar_lt_one (hα0 : 0 ≤ α) (hβ0 : 0 < β) (hc : 0 ≤ c) (hh : 0 < h) :
    epsStar α β c h < 1 := by
  unfold epsStar
  have hβh := mul_pos hβ0 hh
  rw [div_lt_one (add_pos_of_nonneg_of_pos (mul_nonneg hα0 hc) hβh)]
  linarith

/-- **T3(a): fully updated deference as arithmetic.** On the two-state instance with `0 < α ≤ β`,
`0 < c`, `0 < h`: for every `ε < ε* = αc/(αc + βh)`, desideratum 1 fails and the two-option value
of the button is `0` — D1 and the repair incentive fail *together*. Chains
`twoState_deltaMinus_nonneg_iff_epsStar` (D1 ↔ `ε* ≤ ε`) with `voiButton2_eq_max_deltaMinus`
(the regime formula), the regime supplied by `twoState_regime_of_threshold` through
`ε < ε* ≤ c/(c + h)` (`epsStar_le_complianceThreshold`, which is where `α ≤ β` is used).
Source: [[corr-wf13-inventory]] 094 / position statement §1 (ABRAM), §2.13(b) (CLAUDE: "fully updated deference as arithmetic"); miri.md Prop. 10.5
Kind: C
Fidelity: exact (the §2.13(b) arithmetic; the §1 sentence's "no fully updated deference problem" is the verdict of the findings file)
Hyps: (a) only; the regime is derived, not assumed; `α ≤ β` (the sensor is informative) is named -/
theorem fud_band (hα0 : 0 < α) (hβ0 : 0 < β) (hc : 0 < c) (hh : 0 < h) (hαβ : α ≤ β)
    (hεs : ε < epsStar α β c h) (o₀ : Obs) :
    ¬ (twoState ε α β c h hε hα hβ).D1At () ∧
      (twoState ε α β c h hε hα hβ).voiButton2 () o₀ .cont .stop = 0 := by
  have hpos : 0 < α * c + β * h := add_pos (mul_pos hα0 hc) (mul_pos hβ0 hh)
  have hneg : ¬ 0 ≤ (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop := by
    rw [twoState_deltaMinus_nonneg_iff_epsStar ε α β c h hε hα hβ hpos]
    exact not_le.mpr hεs
  refine ⟨fun hd => hneg ((twoState_d1At_iff ε α β c h hε hα hβ).mp hd), ?_⟩
  have hεth : ε ≤ complianceThreshold c h :=
    hεs.le.trans (epsStar_le_complianceThreshold α β c h hα0.le hβ0 hc hh hαβ)
  obtain ⟨hprior, hsilent⟩ :=
    twoState_regime_of_threshold ε α β c h hε hα hβ hc hh hεth hαβ o₀
  rw [voiButton2_eq_max_deltaMinus _ (twoState_A1 ε α β c h hε hα hβ) () o₀ .cont .stop hprior hsilent]
  exact max_eq_right (le_of_not_ge hneg)

/-- **T3(a), corollary: the failing band is nonempty for every fixed `α > 0`.** There is an
`ε ∈ (0, ε*)` (namely `ε*/2`), lying in `[0, 1]`.
Source: [[corr-wf13-inventory]] 094 / position statement §2.13(b)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem fud_band_nonempty (hα0 : 0 < α) (hβ0 : 0 < β) (hc : 0 < c) (hh : 0 < h) :
    ∃ ε' : ℝ, ε' ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < ε' ∧ ε' < epsStar α β c h := by
  have h0 := epsStar_pos α β c h hα0 hβ0 hc hh
  have h1 := epsStar_lt_one α β c h hα0.le hβ0 hc.le hh
  exact ⟨epsStar α β c h / 2, ⟨by linarith, by linarith⟩, by linarith, by linarith⟩

end Band

/-- **T3(a), the N+ inhabitant of `fud_band`'s full package.** T1(c)'s targeted instance
`(ε, α, β, c, h) = (1/100, 1/20, 1/5, 1, 20)` has `0 < α ≤ β`, `0 < c, h` and lies in the band:
`1/100 < ε* = 1/81`. `fud_band` itself — not a direct cell computation — then delivers
`¬ D1At ∧ voiButton2 = 0` (the same numbers `targeted_not_d1At` and `script_cell` compute
directly). (Audit r1, adversarial B3.)
Source: [[corr-wf13-inventory]] 094 / position statement §2.13(b); miri.md I9.4 (the targeted instance)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem targeted_in_band :
    (1/100 : ℝ) < epsStar (1/20) (1/5) 1 20 ∧
    (¬ (twoState (1/100) (1/20) (1/5) 1 20 mem_Icc_1_100 mem_Icc_1_20 mem_Icc_1_5).D1At () ∧
      (twoState (1/100) (1/20) (1/5) 1 20 mem_Icc_1_100 mem_Icc_1_20 mem_Icc_1_5).voiButton2 () .press .cont .stop = 0) := by
  have h : (1/100 : ℝ) < epsStar (1/20) (1/5) 1 20 := by unfold epsStar; norm_num
  exact ⟨h, fud_band (1/100) (1/20) (1/5) 1 20 mem_Icc_1_100 mem_Icc_1_20 mem_Icc_1_5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h .press⟩

/-! ## T3(b) — the escape "`α` falls in step": `α = κ·ε` -/

section Kappa

variable (β c h κ : ℝ) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hκ : κ ∈ Set.Icc (0 : ℝ) 1)

/-- With `α = κ·ε`, `Δ₋ = ε·(βh − κ(1 − ε)c)`.
Source: [[corr-wf13-inventory]] 094 / position statement §2.13(b) ("unless the false-press rate `α` falls with it")
Kind: L
Fidelity: exact -/
lemma kappa_deltaMinus (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) :
    (twoState ε (κ * ε) β c h hε (mul_mem_Icc hκ hε) hβ).deltaMinus () .cont .stop =
      ε * (β * h - κ * (1 - ε) * c) := by
  rw [twoState_deltaMinus]; ring

/-- **T3(b), pointwise.** With `α = κ·ε` and `0 < ε`: `0 < Δ₋ ↔ κ(1 − ε)c < βh`.
Source: [[corr-wf13-inventory]] 094 / position statement §2.13(b)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem kappa_deltaMinus_pos_iff (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hε0 : 0 < ε) :
    0 < (twoState ε (κ * ε) β c h hε (mul_mem_Icc hκ hε) hβ).deltaMinus () .cont .stop ↔
      κ * (1 - ε) * c < β * h := by
  rw [kappa_deltaMinus β c h κ hβ hκ ε hε, mul_pos_iff_of_pos_left hε0]
  exact sub_pos

/-- **T3(b), the escape's exact condition.** With `α = κ·ε`, `κ ∈ [0, 1]`, `0 < β`, `0 < c`,
`0 < h`: desideratum 1 holds at *every* `ε ∈ (0, 1)` iff `κc ≤ βh`. (`corr-three-step`'s
`epsStar_half_lt` is the `κ = 1/2` cell.) Note: the *strict* form `0 < Δ₋` at every `ε ∈ (0, 1)`
has the *same* threshold `κc ≤ βh` (`kappa_strict_forall_iff`), not a strict one: at `κc = βh`
the factor `1 − ε < 1` supplies the slack — the mandate's parenthetical "strict for the strict
form" is not right.
Source: [[corr-wf13-inventory]] 094 / position statement §2.13(b); channel-final.md S12(c) (the `κ = 1/2` cell)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem kappa_d1At_forall_iff (hβ0 : 0 < β) (hc : 0 < c) (hh : 0 < h) :
    (∀ ε : ℝ, ∀ hε : ε ∈ Set.Icc (0 : ℝ) 1, 0 < ε → ε < 1 →
        (twoState ε (κ * ε) β c h hε (mul_mem_Icc hκ hε) hβ).D1At ()) ↔
      κ * c ≤ β * h := by
  constructor
  · intro H
    by_contra hlt
    have hlt := not_le.mp hlt
    have hκ0 : 0 < κ := by
      by_contra hk
      have hk := not_lt.mp hk
      have : κ = 0 := le_antisymm hk hκ.1
      subst this
      linarith [mul_pos hβ0 hh]
    have hκc : 0 < κ * c := mul_pos hκ0 hc
    -- the witness `ε = (κc − βh) / (2κc) ∈ (0, 1/2)`
    set ε := (κ * c - β * h) / (2 * (κ * c)) with hεdef
    have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
    have hεhalf : ε < 1 / 2 := by
      rw [hεdef, div_lt_div_iff₀ (by linarith) (by norm_num)]
      nlinarith [mul_pos hβ0 hh]
    have hεI : ε ∈ Set.Icc (0 : ℝ) 1 := ⟨hε0.le, by linarith⟩
    have hd := (twoState_d1At_iff ε (κ * ε) β c h hεI (mul_mem_Icc hκ hεI) hβ).mp
      (H ε hεI hε0 (by linarith))
    rw [kappa_deltaMinus β c h κ hβ hκ ε hεI] at hd
    have hfac : 0 ≤ β * h - κ * (1 - ε) * c := by
      by_contra hneg
      have hneg := not_le.mp hneg
      nlinarith
    have hεκ : ε * (2 * (κ * c)) = κ * c - β * h := by
      rw [hεdef]; field_simp
    nlinarith
  · intro hle ε hε hε0 hε1
    rw [twoState_d1At_iff, kappa_deltaMinus β c h κ hβ hκ ε hε]
    apply mul_nonneg hε0.le
    have : κ * (1 - ε) * c ≤ κ * c := by
      have := mul_nonneg (mul_nonneg hκ.1 hε0.le) hc.le
      nlinarith
    linarith

/-- **T3(b), strict form.** With `α = κ·ε`: `0 < Δ₋` at every `ε ∈ (0, 1)` iff `κc ≤ βh` — the
same (non-strict) threshold as the non-strict form.
Source: [[corr-wf13-inventory]] 094 / position statement §2.13(b)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem kappa_strict_forall_iff (hβ0 : 0 < β) (hc : 0 < c) (hh : 0 < h) :
    (∀ ε : ℝ, ∀ hε : ε ∈ Set.Icc (0 : ℝ) 1, 0 < ε → ε < 1 →
        0 < (twoState ε (κ * ε) β c h hε (mul_mem_Icc hκ hε) hβ).deltaMinus () .cont .stop) ↔
      κ * c ≤ β * h := by
  constructor
  · intro H
    rw [← kappa_d1At_forall_iff β c h κ hβ hκ hβ0 hc hh]
    intro ε hε hε0 hε1
    rw [twoState_d1At_iff]
    exact (H ε hε hε0 hε1).le
  · intro hle ε hε hε0 hε1
    rw [kappa_deltaMinus β c h κ hβ hκ ε hε]
    apply mul_pos hε0
    rcases eq_or_lt_of_le hκ.1 with h0 | h0
    · subst h0; simp; exact mul_pos hβ0 hh
    · have : κ * (1 - ε) * c < κ * c := by
        have := mul_pos (mul_pos h0 hε0) hc
        nlinarith
      linarith

end Kappa

/-! ## T4(a) — the repair incentive vanishes with the agent's self-distrust -/

section Rate

variable (α β c h : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- **T4(a): the rate.** Along any sequence `ε_t → 0` (in `[0, 1]`) with `(α, β, c, h)` fixed,
`c, h ≥ 0`, the two-option value of the button tends to `0` — with **no regime assumption**:
squeezed between `0` (`voiButton2_nonneg`) and `ε_t·h` (the regime-free perfect-information bound
`twoState_voiButton2_le_perfectInfo`, which is `≤ εh`). The repair incentive is `O(ε)` in the
agent's self-distrust.
Source: [[corr-wf13-2-inventory]] 2-120 / position statement §1 (ABRAM); wentworth.md §2.4(b); miri.md I11.2
Kind: L (a squeeze between two cited bounds; the mandate's Kind)
Fidelity: stronger: no regime hypothesis (the mandate squeezes under `εβh`, which needs the regime)
Hyps: (a) only -/
theorem voiButton2_tendsto_zero (ε : ℕ → ℝ) (hε : ∀ t, ε t ∈ Set.Icc (0 : ℝ) 1)
    (hlim : Tendsto ε atTop (𝓝 0)) (hc : 0 ≤ c) (hh : 0 ≤ h) (o₀ : Obs) :
    Tendsto (fun t => (twoState (ε t) α β c h (hε t) hα hβ).voiButton2 () o₀ .cont .stop)
      atTop (𝓝 0) := by
  have hmul : Tendsto (fun t => ε t * h) atTop (𝓝 0) := by
    simpa using hlim.mul_const h
  refine squeeze_zero (fun t => ?_) (fun t => ?_) hmul
  · exact voiButton2_nonneg _ (twoState_A1 _ _ _ _ _ _ _ _) () o₀ .cont .stop
  · exact (twoState_voiButton2_le_perfectInfo (ε t) α β c h (hε t) hα hβ hc hh o₀).trans
      (min_le_right _ _)

end Rate

/-! ## T4(b) — improvement is valued at least as highly as repair -/

section Monotone

variable (ε α α' β β' c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hα' : α' ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hβ' : β' ∈ Set.Icc (0 : ℝ) 1)

/-- **In the regime the repair incentive is exactly `max(εβh − (1 − ε)αc, 0)`** on the two-option
menu — the sentence's content, with its bound visible.
Source: [[corr-wf13-2-inventory]] 2-120 / wentworth.md §2.4; filler.md F4(b)
Kind: L (two cited facts rewritten)
Fidelity: exact
Hyps: (a) only; the regime is named -/
theorem twoState_voiButton2_eq_max (o₀ : Obs)
    (hprior : 0 ≤ expect (twoPoint ε hε) ((twoState ε α β c h hε hα hβ).Xo () o₀ .cont .stop))
    (hsilent : 0 ≤ (twoState ε α β c h hε hα hβ).deltaPlus () .cont .stop) :
    (twoState ε α β c h hε hα hβ).voiButton2 () o₀ .cont .stop =
      max (ε * β * h - (1 - ε) * α * c) 0 := by
  rw [voiButton2_eq_max_deltaMinus _ (twoState_A1 ε α β c h hε hα hβ) () o₀ .cont .stop hprior hsilent,
    twoState_deltaMinus]

/-- `Δ₋` is antitone in the false-press rate `α` (for `ε ≤ 1`, `0 ≤ c`).
Source: [[corr-wf13-2-inventory]] 2-120 / shah.md C10; wentworth.md §2.4
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoState_deltaMinus_antitone_alpha (hαα' : α ≤ α') (hc : 0 ≤ c) :
    (twoState ε α' β c h hε hα' hβ).deltaMinus () .cont .stop ≤
      (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop := by
  rw [twoState_deltaMinus, twoState_deltaMinus]
  nlinarith [mul_le_mul_of_nonneg_right hαα' (mul_nonneg (sub_nonneg.mpr hε.2) hc)]

/-- `Δ₋` is monotone in the hit rate `β` (for `0 ≤ ε`, `0 ≤ h`).
Source: [[corr-wf13-2-inventory]] 2-120 / shah.md C10; wentworth.md §2.4
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoState_deltaMinus_monotone_beta (hββ' : β ≤ β') (hh : 0 ≤ h) :
    (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop ≤
      (twoState ε α β' c h hε hα hβ').deltaMinus () .cont .stop := by
  rw [twoState_deltaMinus, twoState_deltaMinus]
  nlinarith [mul_le_mul_of_nonneg_right hββ' (mul_nonneg hε.1 hh)]

/-- **T4(b), `α`.** In the regime at both sensors, the two-option value of the button is antitone
in the false-press rate: a sensor with fewer false presses is worth at least as much — improving
the channel is valued at least as highly as repairing it.
Source: [[corr-wf13-2-inventory]] 2-120 / shah.md C10; miri.md I11.2(c)
Kind: L
Fidelity: exact
Hyps: (a) only; the regime at both sensors is named -/
theorem twoState_voiButton2_antitone_alpha (o₀ : Obs) (hαα' : α ≤ α') (hc : 0 ≤ c)
    (hprior : 0 ≤ expect (twoPoint ε hε) ((twoState ε α β c h hε hα hβ).Xo () o₀ .cont .stop))
    (hsilent : 0 ≤ (twoState ε α β c h hε hα hβ).deltaPlus () .cont .stop)
    (hprior' : 0 ≤ expect (twoPoint ε hε) ((twoState ε α' β c h hε hα' hβ).Xo () o₀ .cont .stop))
    (hsilent' : 0 ≤ (twoState ε α' β c h hε hα' hβ).deltaPlus () .cont .stop) :
    (twoState ε α' β c h hε hα' hβ).voiButton2 () o₀ .cont .stop ≤
      (twoState ε α β c h hε hα hβ).voiButton2 () o₀ .cont .stop := by
  rw [voiButton2_eq_max_deltaMinus _ (twoState_A1 _ _ _ _ _ _ _ _) () o₀ .cont .stop hprior hsilent,
    voiButton2_eq_max_deltaMinus _ (twoState_A1 _ _ _ _ _ _ _ _) () o₀ .cont .stop hprior' hsilent']
  exact max_le_max (twoState_deltaMinus_antitone_alpha ε α α' β c h hε hα hα' hβ hαα' hc) le_rfl

/-- **T4(b), `β`.** In the regime at both sensors, the value of the button is monotone in the hit
rate.
Source: [[corr-wf13-2-inventory]] 2-120 / shah.md C10; miri.md I11.2(c)
Kind: L
Fidelity: exact
Hyps: (a) only; the regime at both sensors is named -/
theorem twoState_voiButton2_monotone_beta (o₀ : Obs) (hββ' : β ≤ β') (hh : 0 ≤ h)
    (hprior : 0 ≤ expect (twoPoint ε hε) ((twoState ε α β c h hε hα hβ).Xo () o₀ .cont .stop))
    (hsilent : 0 ≤ (twoState ε α β c h hε hα hβ).deltaPlus () .cont .stop)
    (hprior' : 0 ≤ expect (twoPoint ε hε) ((twoState ε α β' c h hε hα hβ').Xo () o₀ .cont .stop))
    (hsilent' : 0 ≤ (twoState ε α β' c h hε hα hβ').deltaPlus () .cont .stop) :
    (twoState ε α β c h hε hα hβ).voiButton2 () o₀ .cont .stop ≤
      (twoState ε α β' c h hε hα hβ').voiButton2 () o₀ .cont .stop := by
  rw [voiButton2_eq_max_deltaMinus _ (twoState_A1 _ _ _ _ _ _ _ _) () o₀ .cont .stop hprior hsilent,
    voiButton2_eq_max_deltaMinus _ (twoState_A1 _ _ _ _ _ _ _ _) () o₀ .cont .stop hprior' hsilent']
  exact max_le_max (twoState_deltaMinus_monotone_beta ε α β β' c h hε hα hβ hβ' hββ' hh) le_rfl

end Monotone

/-- **T4(b), the N+ cell, in the regime.** At `(ε, β, c, h) = (1/20, 9/10, 1, 10)` — the `h = 10`
regime instance of `corr-three-step` (`E_μ[X] = 9/20`) — the refined sensor `α = 1/40` has
`voiButton2 = 341/800`, the honest `α = 1/20` has `161/400 = 322/800`; both instances are in the
regime (`Δ₊ = 701/800` and `341/400`). (T2(ii)'s refinement cell at `h = 20` is *outside* the regime;
its inequality is `believed_sensor_is_refinement`, computed regime-free.)
Source: [[corr-wf13-2-inventory]] 2-120 / miri.md I9.7 (the refinement side)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem refinement_cell_regime :
    (0 ≤ expect (twoPoint (1/20) mem_Icc_1_20)
        ((twoState (1/20) (1/40) (9/10) 1 10 mem_Icc_1_20 mem_Icc_1_40 mem_Icc_9_10).Xo () .press .cont .stop) ∧
      0 ≤ (twoState (1/20) (1/40) (9/10) 1 10 mem_Icc_1_20 mem_Icc_1_40 mem_Icc_9_10).deltaPlus () .cont .stop) ∧
    (0 ≤ expect (twoPoint (1/20) mem_Icc_1_20)
        ((twoState (1/20) (1/20) (9/10) 1 10 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).Xo () .press .cont .stop) ∧
      0 ≤ (twoState (1/20) (1/20) (9/10) 1 10 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).deltaPlus () .cont .stop) ∧
    (twoState (1/20) (1/40) (9/10) 1 10 mem_Icc_1_20 mem_Icc_1_40 mem_Icc_9_10).voiButton2 () .press .cont .stop =
        341 / 800 ∧
    (twoState (1/20) (1/20) (9/10) 1 10 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).voiButton2 () .press .cont .stop =
        161 / 400 := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [twoState_expect_Xo]; norm_num
  · rw [twoState_deltaPlus]; norm_num
  · rw [twoState_expect_Xo]; norm_num
  · rw [twoState_deltaPlus]; norm_num
  · rw [voiButton2_eq _ (twoState_A1 _ _ _ _ _ _ _ _), twoState_deltaMinus, twoState_deltaPlus]; norm_num
  · rw [voiButton2_eq _ (twoState_A1 _ _ _ _ _ _ _ _), twoState_deltaMinus, twoState_deltaPlus]; norm_num

end Cleanroom.Corrigibility.CorrPositionFinds

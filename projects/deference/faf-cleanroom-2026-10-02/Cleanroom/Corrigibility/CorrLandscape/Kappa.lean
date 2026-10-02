import Cleanroom.Corrigibility.CorrLandscape.Margin
import Mathlib.Tactic.IntervalCases

/-!
# `corr-landscape` — `Kappa`: S4(ii)–(iii), the margin in the value coordinate (T3, load-bearing 4)

D14's coupling `κ` ([[corr-wf14-inventory]] 116; [[corr-wf14-2-inventory]] 2-051; P3′):

* (a) `m(κ)` is affine in `κ`; `m(0) = π (ε/(1−ε)·(h/c) − 1)`; `m(0) < 0 ↔ ε < c/(c+h)` for `π > 0` —
  so at `ε ≥ c/(c+h)` an uninformative press is obeyed at every `κ` (2-051(c)).
* (b) the crossing `κ* = −m(0)/(m(1) − m(0))` on the regime `m(0) < 0 ≤ m(1)`: `m(κ) ≥ 0 ↔ κ ≥ κ*`;
  compliance for every `κ ∈ [0,1]` when `m(0), m(1) ≥ 0`; for none when both are negative. **The
  source's trichotomy presupposes `m(0) ≤ m(1)`**, which holds under `α ≤ π ≤ β` (`effMargin_zero_le_one`);
  the general statements carry the two endpoint signs explicitly.
* (c) with `u = ε/(1−ε)·(h/c)`, `κ* = π(1 − u)/(u(β − π) + π − α)`; strictly decreasing in `ε` on the
  regime (`β > α`, `π > 0`), and **`κ*(ε*) = 1` exactly** — replacing the inventory's loose
  "`1 − κ*_t → 0` as `ε_t → 0`": at `t = t*` the tolerable misspecification is `0`, after it `κ*` is
  undefined (the regime fails).
* (d) the worked table (P3′) at `t ∈ {8, 10, 12, 15, 16}` as exact rationals, and `t_conf = 7` as the
  least `t` with `ε_t < 1/21`.

Register: the `κ` model is the source's CLAUDE stand-in for Carey 2018 (D14); the attribution of
Christiano's "slight divergence" sentence to this coordinate is ATTRIBUTION-UNVETTED. `kappaStar`
outside its regime is a junk quotient: every use is guarded by the regime hypothesis.
-/

namespace Cleanroom.Corrigibility.CorrLandscape

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrTrajectory
open Corruption (oddsIneq)

set_option linter.unusedSectionVars false

namespace Kappa

open Margin

/-! ## (a) affine in `κ`; the uninformative margin -/

/-- **`m(κ)` is affine in `κ`**: `m(κ) = m(0) + κ (m(1) − m(0))`.
Source: [[corr-wf14-inventory]] 116 / approval-final.md P3′ ("affine in `κ`")
Kind: L
Fidelity: exact -/
theorem effMargin_affine (ε β α π κ c h : ℝ) :
    effMargin ε β α π κ c h = effMargin ε β α π 0 c h + κ * (effMargin ε β α π 1 c h - effMargin ε β α π 0 c h) := by
  simp only [effMargin, effRates]; ring

/-- **`m(0) = π (ε/(1−ε)·(h/c) − 1)`**: the margin of a press carrying no information about `X`.
Source: [[corr-wf14-inventory]] 116 / approval-final.md P3′
Kind: L
Fidelity: exact -/
theorem effMargin_zero (ε β α π c h : ℝ) : effMargin ε β α π 0 c h = π * (ε / (1 - ε) * (h / c) - 1) := by
  simp only [effMargin, effRates]; ring

/-- **`m(0) < 0 ↔ ε < c/(c+h)`** for `π > 0`, `0 < c`, `0 ≤ h`, `ε < 1`, `0 ≤ ε`.
Source: [[corr-wf14-inventory]] 116 / approval-final.md P3′ ("`m(0) < 0 ⟺ ε < c/(c+h)`")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem effMargin_zero_neg_iff (ε β α π c h : ℝ) (hπ : 0 < π) (hc : 0 < c) (hh : 0 ≤ h) (hε : ε < 1)
    (hε0 : 0 ≤ ε) : effMargin ε β α π 0 c h < 0 ↔ ε < complianceThreshold c h := by
  rw [effMargin_zero, complianceThreshold]
  have h1 : 0 < 1 - ε := by linarith
  have hch : 0 < c + h := by linarith
  rw [mul_neg_iff, div_mul_div_comm, lt_div_iff₀ hch]
  constructor
  · rintro (⟨-, H⟩ | ⟨H, -⟩)
    · rw [sub_neg, div_lt_one (mul_pos h1 hc)] at H
      nlinarith
    · linarith
  · intro H
    left
    refine ⟨hπ, ?_⟩
    rw [sub_neg, div_lt_one (mul_pos h1 hc)]
    nlinarith

/-- **2-051(c): at `ε ≥ c/(c+h)` the uninformative margin is nonnegative** (`π ≥ 0`): an uninformative
press is obeyed by an agent uncertain enough.
Source: [[corr-wf14-2-inventory]] 2-051 / `s4_misspec_two_coordinates.py` ("for `eps >= c/(c+h)` the
press is obeyed even at `kappa=0`")
Kind: L
Fidelity: exact -/
theorem effMargin_zero_nonneg_of_threshold_le (ε β α π c h : ℝ) (hπ : 0 ≤ π) (hc : 0 < c) (hh : 0 ≤ h)
    (hε : ε < 1) (hth : complianceThreshold c h ≤ ε) : 0 ≤ effMargin ε β α π 0 c h := by
  rw [effMargin_zero]
  have h1 : 0 < 1 - ε := by linarith
  have hch : 0 < c + h := by linarith
  rw [complianceThreshold, div_le_iff₀ hch] at hth
  refine mul_nonneg hπ ?_
  rw [sub_nonneg, div_mul_div_comm, one_le_div (mul_pos h1 hc)]
  nlinarith

/-- **The ordering `m(0) ≤ m(1)`** under `α ≤ π ≤ β` and `0 ≤ u`: the presupposition of the source's
trichotomy, made explicit.
Source: [[corr-wf14-inventory]] 116 / approval-final.md P3′ (implicit); mandate T3(c) ("under `α < π < β`")
Kind: L
Fidelity: exact -/
theorem effMargin_zero_le_one (ε β α π c h : ℝ) (hu : 0 ≤ ε / (1 - ε) * (h / c)) (hαπ : α ≤ π)
    (hπβ : π ≤ β) : effMargin ε β α π 0 c h ≤ effMargin ε β α π 1 c h := by
  simp only [effMargin, effRates]
  nlinarith [mul_le_mul_of_nonneg_left hπβ hu]

/-! ## (b) the crossing `κ*` -/

/-- **The crossing** `κ* = −m(0)/(m(1) − m(0))`. A junk quotient outside the regime `m(0) < 0 ≤ m(1)`:
every use below carries the regime.
Source: [[corr-wf14-inventory]] 116 / approval-final.md P3′ ("the crossing is `κ* = −m(0)/(m(1)−m(0))`")
Kind: D
Fidelity: exact under the regime -/
noncomputable def kappaStar (ε β α π c h : ℝ) : ℝ :=
  -effMargin ε β α π 0 c h / (effMargin ε β α π 1 c h - effMargin ε β α π 0 c h)

/-- **The crossing theorem**: on the regime `m(0) < 0 ≤ m(1)`, compliance at coupling `κ` holds iff
`κ ≥ κ*`.
Source: [[corr-wf14-inventory]] 116 / approval-final.md P3′ ("compliance fails for `κ < κ*`")
Kind: P
Fidelity: exact
Hyps: (a) the regime -/
theorem comply_iff_kappaStar_le (ε β α π c h κ : ℝ) (h0 : effMargin ε β α π 0 c h < 0)
    (h1 : 0 ≤ effMargin ε β α π 1 c h) :
    0 ≤ effMargin ε β α π κ c h ↔ kappaStar ε β α π c h ≤ κ := by
  rw [effMargin_affine ε β α π κ, kappaStar, div_le_iff₀ (by linarith)]
  constructor <;> intro H <;> nlinarith

/-- **Compliance for every `κ ∈ [0,1]` when both endpoint margins are nonnegative** (the source's
"if `m(0) ≥ 0`, compliance holds for every `κ`", with the `m(1) ≥ 0` half it needs made explicit —
under `α ≤ π ≤ β` it follows from `m(0) ≥ 0` by `effMargin_zero_le_one`).
Source: [[corr-wf14-inventory]] 116 / approval-final.md P3′
Kind: L
Fidelity: variant: the second endpoint sign is an explicit hypothesis (the source's trichotomy
presupposes `m(0) ≤ m(1)`)
Hyps: (a) only -/
theorem comply_all_of_nonneg (ε β α π c h κ : ℝ) (h0 : 0 ≤ effMargin ε β α π 0 c h)
    (h1 : 0 ≤ effMargin ε β α π 1 c h) (hκ : κ ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ effMargin ε β α π κ c h := by
  rw [effMargin_affine ε β α π κ]
  nlinarith [hκ.1, hκ.2]

/-- **Compliance for no `κ ∈ [0,1]` when both endpoint margins are negative** (the source's "if
`m(1) < 0` compliance fails for every `κ`", under `m(0) ≤ m(1)`).
Source: [[corr-wf14-inventory]] 116 / approval-final.md P3′
Kind: L
Fidelity: variant: as above
Hyps: (a) only -/
theorem fail_all_of_neg (ε β α π c h κ : ℝ) (h0 : effMargin ε β α π 0 c h < 0)
    (h1 : effMargin ε β α π 1 c h < 0) (hκ : κ ∈ Set.Icc (0 : ℝ) 1) : effMargin ε β α π κ c h < 0 := by
  rw [effMargin_affine ε β α π κ]
  by_cases hk : κ ≤ 1 / 2
  · nlinarith [mul_nonneg hκ.1 (neg_nonneg.2 h1.le), hκ.1]
  · rw [not_le] at hk
    nlinarith [mul_nonneg (sub_nonneg.2 hκ.2) (neg_nonneg.2 h0.le), hκ.2]

/-! ## (c) the closed form, monotonicity in `ε`, the exact endpoint -/

/-- **The closed form** `κ* = π(1 − u)/(u(β − π) + π − α)` with `u = ε/(1−ε)·(h/c)`.
Source: mandate T3(c) (derived from P3′)
Kind: L
Fidelity: exact -/
theorem kappaStar_closed (ε β α π c h : ℝ) :
    kappaStar ε β α π c h =
      π * (1 - ε / (1 - ε) * (h / c)) / (ε / (1 - ε) * (h / c) * (β - π) + π - α) := by
  unfold kappaStar
  simp only [effMargin, effRates]
  congr 1 <;> ring

/-- The crossing as a function of `u`: strictly decreasing where the denominator is positive.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma crossing_of_u_strictAnti {u u' β α π : ℝ} (hπ : 0 < π) (hβα : α < β) (huu : u < u')
    (hd : 0 < u * (β - π) + π - α) (hd' : 0 < u' * (β - π) + π - α) :
    π * (1 - u') / (u' * (β - π) + π - α) < π * (1 - u) / (u * (β - π) + π - α) := by
  rw [div_lt_div_iff₀ hd' hd]
  nlinarith [mul_pos hπ (mul_pos (sub_pos.2 hβα) (sub_pos.2 huu))]

/-- **`κ*` is strictly decreasing in `ε`** on the regime (denominators positive, `β > α`, `π > 0`,
`ε < ε' < 1`, `0 < c`, `0 ≤ h`): the tolerable misspecification shrinks as the agent grows confident.
Source: [[corr-wf14-inventory]] 116 / approval-final.md P3′ ("`κ*_t ↑ 1` on `[t_conf, t*]`")
Kind: P
Fidelity: exact (the source's monotone-in-`t` claim, as monotone-in-`ε` with the regime explicit)
Hyps: (a) only -/
theorem kappaStar_strictAnti (ε ε' β α π c h : ℝ) (hπ : 0 < π) (hβα : α < β) (hc : 0 < c) (hh : 0 < h)
    (hε : ε < ε') (hε' : ε' < 1)
    (hd : 0 < ε / (1 - ε) * (h / c) * (β - π) + π - α)
    (hd' : 0 < ε' / (1 - ε') * (h / c) * (β - π) + π - α) :
    kappaStar ε' β α π c h < kappaStar ε β α π c h := by
  rw [kappaStar_closed, kappaStar_closed]
  refine crossing_of_u_strictAnti hπ hβα ?_ hd hd'
  have hlt : ε / (1 - ε) < ε' / (1 - ε') := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
  exact mul_lt_mul_of_pos_right hlt (div_pos hh hc)

/-- **The exact endpoint**: at `ε = ε*` the crossing is `κ* = 1` exactly — the channel margin vanishes
there (`effMargin_one_eq_zero_iff`) while `m(0) < 0` (which is `ε* < c/(c+h)`, i.e. `α < β`). After
`t*` the regime fails and `κ*` is undefined ("none"). The endpoint value itself is definitional
(`κ* = −m(0)/(0 − m(0)) = 1` whenever `m(1) = 0 ≠ m(0)`); the content is that the regime
`m(0) < 0 ≤ m(1)` holds at `ε*`, which is `α < β` (audit r1, adversarial N2).
Source: [[corr-wf14-inventory]] 116 ("`1 − κ*_t → 0` as `ε_t → 0`", sharpened) / approval-final.md S4(iii)
("`κ*_t → 1` as `ε_t → 0`"), P3′ ("`κ*_t ↑ 1` on `[t_conf, t*]`"); mandate T3(c)
Kind: L (the regime at `ε*`, then the definition of `kappaStar`)
Fidelity: stronger: the exact endpoint replaces a limit statement
Hyps: (a) only -/
theorem kappaStar_epsStar (β α π c h : ℝ) (hπ : 0 < π) (hα : 0 ≤ α) (hβα : α < β) (hc : 0 < c)
    (hh : 0 < h) : kappaStar (epsStar α β c h) β α π c h = 1 := by
  have hpos : 0 < α * c + β * h := by nlinarith [mul_nonneg hα hc.le, mul_pos (by linarith : 0 < β) hh]
  have hε1 : epsStar α β c h < 1 := by
    rw [epsStar, div_lt_one hpos]; nlinarith [mul_pos (by linarith : 0 < β) hh]
  have hε0 : 0 ≤ epsStar α β c h := div_nonneg (mul_nonneg hα hc.le) hpos.le
  have h1 : effMargin (epsStar α β c h) β α π 1 c h = 0 :=
    (effMargin_one_eq_zero_iff _ β α c h π hpos hε1 hc).2 rfl
  have h0 : effMargin (epsStar α β c h) β α π 0 c h < 0 := by
    rw [effMargin_zero_neg_iff _ β α π c h hπ hc hh.le hε1 hε0, epsStar, complianceThreshold,
      div_lt_div_iff₀ hpos (by linarith)]
    nlinarith [mul_pos (sub_pos.2 hβα) hh]
  unfold kappaStar
  rw [h1, zero_sub, neg_div_neg_eq, div_self h0.ne]

/-! ## (d) the worked table (P3′) -/

/-- **The worked table**: `κ*` at `t ∈ {8, 10, 12, 15, 16}` on the trajectory `ε_t = (3/10)(3/4)^t`,
`(β, α, π, c, h) = (9/10, 1/20, 3/10, 1, 20)`, as exact rationals (the source's `0.184, 0.432, 0.664,
0.925, 0.985`); each row is in the regime.
Source: [[corr-wf14-inventory]] 116 / approval-final.md P3′ (table); `s4_misspec_two_coordinates.py`
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem kappaStar_table :
    kappaStar (epsT 8) (9 / 10) (1 / 20) (3 / 10) 1 20 = 1452102 / 7902305 ∧
      kappaStar (epsT 10) (9 / 10) (1 / 20) (3 / 10) 1 20 = 40594038 / 94058345 ∧
      kappaStar (epsT 12) (9 / 10) (1 / 20) (3 / 10) 1 20 = 805748262 / 1213526705 ∧
      kappaStar (epsT 15) (9 / 10) (1 / 20) (3 / 10) 1 20 = 59000622594 / 63803070635 ∧
      kappaStar (epsT 16) (9 / 10) (1 / 20) (3 / 10) 1 20 = 241426377222 / 245096303105 := by
  simp only [kappaStar, effMargin, effRates, epsT]
  norm_num

/-- **The table rows are in the regime** `m(0) < 0 ≤ m(1)` at `t ∈ {8, 10, 12, 15, 16}`, and the margins
at `t = 8` are the source's `m(1) = 0.507…`, `m(0) = −0.114…` as exact rationals.
Source: [[corr-wf14-inventory]] 116 / approval-final.md P3′ (table)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem table_regime :
    (∀ t ∈ ({8, 10, 12, 15, 16} : Finset ℕ),
      effMargin (epsT t) (9 / 10) (1 / 20) (3 / 10) 0 1 20 < 0 ∧
        0 ≤ effMargin (epsT t) (9 / 10) (1 / 20) (3 / 10) 1 1 20) ∧
      effMargin (epsT 8) (9 / 10) (1 / 20) (3 / 10) 1 1 20 = 6450203 / 12713540 ∧
      effMargin (epsT 8) (9 / 10) (1 / 20) (3 / 10) 0 1 20 = -(726051 / 6356770) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> simp only [effMargin, effRates, epsT] <;> norm_num
  · simp only [effMargin, effRates, epsT]; norm_num
  · simp only [effMargin, effRates, epsT]; norm_num

/-- **`t_conf = 7` is the least `t` with `ε_t < c/(c+h) = 1/21`**: from `t = 7` on the agent is confident
and the value coordinate is fragile.
Source: [[corr-wf14-inventory]] 116 / approval-final.md P3′ ("`m(0)` crossed at the earlier step where
`ε_t < c/(c+h)`"); mandate T3(d)
Kind: N+ (least index)
Fidelity: exact
Hyps: (a) only -/
theorem tconf_least :
    complianceThreshold 1 20 = 1 / 21 ∧ (∀ t ≤ 6, ¬ epsT t < 1 / 21) ∧ epsT 7 < 1 / 21 := by
  refine ⟨by unfold complianceThreshold; norm_num, ?_, ?_⟩
  · intro t ht
    unfold epsT
    interval_cases t <;> norm_num
  · unfold epsT; norm_num

end Kappa

end Cleanroom.Corrigibility.CorrLandscape

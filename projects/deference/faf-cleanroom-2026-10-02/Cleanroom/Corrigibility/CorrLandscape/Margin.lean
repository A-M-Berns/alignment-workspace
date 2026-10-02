import Cleanroom.Corrigibility.CorrTrajectory.Margin
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Ring.Real

/-!
# `corr-landscape` — `Margin`: the margin layer and openness in the channel coordinate (T1–T2)

* **T1 (D7, D14).** `effRates β α π κ` are D14's effective press rates under coupling `κ`;
  `effMargin ε β α π κ c h = ε/(1−ε)·(h/c)·β^eff(κ) − α^eff(κ)`; the channel margin is `κ = 1`.
  `0 ≤ effMargin … 1 ↔ oddsIneq α β h c ε` (`corr-trajectory`'s compliance inequality of record, reused)
  under `ε < 1`, `0 < c` — the junk points of the ratio — and, through the parent, `↔ 0 ≤ Δ₋` on
  `twoState`; `effMargin … 1 = 0 ↔ ε = epsStar α β c h` under positivity.
* **T2 (S4(i), A4.4).** The strict-margin set is open in `(0,1)³` — every strict inequality is open;
  *not* a robustness theorem (`strictMargin_isOpen`, kind T). The robustness box at `t = 0`
  (`|Δε| ≤ 1/20`, `|Δα| ≤ 1/25`, `|Δβ| ≤ 3/10`) is handled by monotonicity — increasing in `ε` and `β`,
  decreasing in `α` — so the worst corner `(1/4, 9/100, 3/5)` gives `m = 391/100`; one cell, not 27.
  `m_0 = 1073/140`.

The worked trajectory of the whole package: `h/c = 20`, `β = 9/10`, `α = 1/20`,
`ε_t = (3/10)(3/4)^t` (`epsT`), `π = 3/10`.
-/

namespace Cleanroom.Corrigibility.CorrLandscape

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrTrajectory
open Corruption (oddsIneq)

set_option linter.unusedSectionVars false

namespace Margin

/-- **The worked error trajectory** `ε_t = (3/10)(3/4)^t`.
Source: [[corr-wf14-inventory]] 116, 117 / approval-final.md P3 ("`ε_t = ε_0 ρ^t`"), `s3_s5_trajectory.py`
Kind: D
Fidelity: exact -/
noncomputable def epsT (t : ℕ) : ℝ := (3 / 10) * (3 / 4 : ℝ) ^ t

/-- **D14's effective rates** under coupling `κ`: `(β^eff, α^eff) = (κβ + (1−κ)π, κα + (1−κ)π)`.
Source: [[corr-wf14-inventory]] 116; [[corr-wf14-2-inventory]] 2-051 / approval-final.md D14
Kind: D
Fidelity: exact (D14 is the source's CLAUDE stand-in for Carey 2018's mis-parameterized reward; the
attribution of Christiano's sentence to this coordinate is ATTRIBUTION-UNVETTED) -/
def effRates (β α π κ : ℝ) : ℝ × ℝ := (κ * β + (1 - κ) * π, κ * α + (1 - κ) * π)

/-- **D7/D14: the margin** `m(κ) = ε/(1−ε)·(h/c)·β^eff(κ) − α^eff(κ)`; the channel margin is `κ = 1`.
Junk at `ε = 1` and `c = 0`: every theorem carries `ε < 1`, `0 < c`.
Source: [[corr-wf14-inventory]] 116 / approval-final.md D7, D14, P3′
Kind: D
Fidelity: exact under `ε < 1`, `0 < c` -/
noncomputable def effMargin (ε β α π κ c h : ℝ) : ℝ :=
  ε / (1 - ε) * (h / c) * (effRates β α π κ).1 - (effRates β α π κ).2

/-- The channel margin unfolds to `ε/(1−ε)·(h/c)·β − α`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma effMargin_one (ε β α π c h : ℝ) : effMargin ε β α π 1 c h = ε / (1 - ε) * (h / c) * β - α := by
  simp [effMargin, effRates]

/-- **T1: the channel margin is nonnegative iff the compliance inequality of record holds**
(`oddsIneq α β h c ε : (1 − ε) c α ≤ ε h β`), under `ε < 1`, `0 < c` — exactly where the ratio is
defined. `oddsIneq` has no junk point and is the headline object; the margin is its ratio form.
Source: [[corr-wf14-inventory]] 116 / approval-final.md D7 ("`κ^VL_t` iff `m̂_t ≥ 0`"), P3
Kind: L
Fidelity: exact (positivity is where the ratio is defined)
Hyps: (a) only -/
theorem effMargin_one_nonneg_iff (ε β α c h : ℝ) (π : ℝ) (hε : ε < 1) (hc : 0 < c) :
    0 ≤ effMargin ε β α π 1 c h ↔ oddsIneq α β h c ε := by
  rw [effMargin_one, oddsIneq]
  have h1 : 0 < 1 - ε := by linarith
  rw [sub_nonneg, div_mul_div_comm, div_mul_eq_mul_div, le_div_iff₀ (mul_pos h1 hc)]
  constructor <;> intro H <;> nlinarith

/-- **T1 through the parent**: on `twoState`, the channel margin is nonnegative iff `Δ₋ ≥ 0`
(`corr-trajectory`'s `Margin.oddsIneq_iff_deltaMinus` composed with `effMargin_one_nonneg_iff`).
Source: [[corr-wf14-inventory]] 116 / approval-final.md P3 ("`P(X ≤ 0 ∣ Pr) ≥ c/(c+h) ⟺ … ⟺ m ≥ 0`")
Kind: C
Fidelity: exact
Hyps: (a) only -/
theorem effMargin_one_nonneg_iff_deltaMinus (ε β α c h π : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hε1 : ε < 1) (hc : 0 < c) :
    0 ≤ effMargin ε β α π 1 c h ↔ 0 ≤ (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop := by
  rw [effMargin_one_nonneg_iff ε β α c h π hε1 hc,
    Cleanroom.Corrigibility.CorrTrajectory.Margin.oddsIneq_iff_deltaMinus]

/-- **T1: the margin vanishes exactly at `ε*`**: `effMargin … 1 = 0 ↔ ε = epsStar α β c h` under
`0 < α c + β h`, `ε < 1`, `0 < c`.
Source: [[corr-wf14-inventory]] 116 / approval-final.md P3 ("`m = 0` at `ε* = αc/(αc + βh)`")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem effMargin_one_eq_zero_iff (ε β α c h π : ℝ) (hpos : 0 < α * c + β * h) (hε : ε < 1)
    (hc : 0 < c) : effMargin ε β α π 1 c h = 0 ↔ ε = epsStar α β c h := by
  rw [effMargin_one, epsStar]
  have h1 : 0 < 1 - ε := by linarith
  rw [sub_eq_zero, div_mul_div_comm, div_mul_eq_mul_div, div_eq_iff (mul_pos h1 hc).ne',
    eq_div_iff hpos.ne']
  constructor <;> intro H <;> nlinarith

/-- The compliance inequality of record in `ε*` form: `oddsIneq α β h c ε ↔ ε* ≤ ε` under
`0 < α c + β h` (the parent's `twoState_deltaMinus_nonneg_iff_epsStar`, with the junk-free inequality on
the left).
Source: [[corr-wf14-inventory]] 117 / approval-final.md S5 ("`ε*_t = α_t c/(α_t c + β_t h)`")
Kind: L
Fidelity: exact -/
theorem oddsIneq_iff_epsStar_le (ε β α c h : ℝ) (hpos : 0 < α * c + β * h) :
    oddsIneq α β h c ε ↔ epsStar α β c h ≤ ε := by
  rw [oddsIneq, epsStar, div_le_iff₀ hpos]
  constructor <;> intro H <;> nlinarith

/-! ## T2: openness in the channel coordinate (S4(i), A4.4) -/

/-- The strict-margin set in the channel coordinate: `(ε, α, β) ∈ (0,1)³` with `m(1) > 0`.
Source: [[corr-wf14-inventory]] 116 / approval-final.md S4(i) ("`{m > 0}` is open in `(ε, α, β)`")
Kind: D
Fidelity: exact -/
def strictMarginSet (π c h : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ p.2.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ p.2.2 ∈ Set.Ioo (0 : ℝ) 1 ∧
    0 < effMargin p.1 p.2.2 p.2.1 π 1 c h}

/-- On `(0,1)³` with `0 < c` the strict margin is the strict polynomial inequality
`(1 − ε) c α < ε h β`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma strictMargin_iff_poly {ε α β : ℝ} (π c h : ℝ) (hε : ε < 1) (hc : 0 < c) :
    0 < effMargin ε β α π 1 c h ↔ (1 - ε) * c * α < ε * h * β := by
  rw [effMargin_one]
  have h1 : 0 < 1 - ε := by linarith
  rw [sub_pos, div_mul_div_comm, div_mul_eq_mul_div, lt_div_iff₀ (mul_pos h1 hc)]
  constructor <;> intro H <;> nlinarith

/-- **S4(i), the trivial half: the strict-margin set is open in `(0,1)³`** (A4.4: "every strict
inequality is open; this is not a robustness theorem about corrigibility"). Kind T by the source's
own grading: continuity of a polynomial inequality on an open box.
Source: [[corr-wf14-inventory]] 116; [[corr-wf14-2-inventory]] 2-051 / approval-final.md S4(i),
approval-adversary.md A4.4
Kind: T
Fidelity: exact
Hyps: (a) `0 < c` -/
theorem strictMargin_isOpen (π c h : ℝ) (hc : 0 < c) : IsOpen (strictMarginSet π c h) := by
  have hset : strictMarginSet π c h =
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) ∩
        {p : ℝ × ℝ × ℝ | (1 - p.1) * c * p.2.1 < p.1 * h * p.2.2} := by
    ext ⟨ε, α, β⟩
    simp only [strictMarginSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2, h3⟩, (strictMargin_iff_poly π c h h1.2 hc).1 h4⟩
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨h1, h2, h3, (strictMargin_iff_poly π c h h1.2 hc).2 h4⟩
  rw [hset]
  refine IsOpen.inter (isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_Ioo)) (isOpen_lt ?_ ?_)
  · fun_prop
  · fun_prop

/-! ## The robustness box at `t = 0`, by monotonicity (S4(i), `s4_misspec_two_coordinates.py`) -/

/-- `x ↦ x/(1 − x)` is monotone on `x < 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma div_one_sub_mono {x y : ℝ} (hxy : x ≤ y) (hy : y < 1) : x / (1 - x) ≤ y / (1 - y) := by
  have hx : x < 1 := lt_of_le_of_lt hxy hy
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **The channel margin is monotone**: increasing in `ε` (for `β ≥ 0`), increasing in `β`, decreasing in
`α`, on `ε < 1`, `0 < c`, `0 ≤ h`.
Source: [[corr-wf14-inventory]] 116 / approval-final.md S4(i) (the box); mandate T2 ("one `norm_num`
cell, not 27")
Kind: L
Fidelity: exact -/
theorem effMargin_one_mono {ε ε' β β' α α' : ℝ} (π c h : ℝ) (hc : 0 < c) (hh : 0 ≤ h) (hε : ε ≤ ε')
    (hε' : ε' < 1) (hε0 : 0 ≤ ε) (hβ : β ≤ β') (hβ0 : 0 ≤ β) (hα : α' ≤ α) :
    effMargin ε β α π 1 c h ≤ effMargin ε' β' α' π 1 c h := by
  rw [effMargin_one, effMargin_one]
  have hu : ε / (1 - ε) ≤ ε' / (1 - ε') := div_one_sub_mono hε hε'
  have hu0 : 0 ≤ ε / (1 - ε) := div_nonneg hε0 (by linarith [lt_of_le_of_lt hε hε'])
  have hhc : 0 ≤ h / c := div_nonneg hh hc.le
  have := mul_le_mul (mul_le_mul_of_nonneg_right hu hhc) hβ hβ0 (mul_nonneg (by linarith) hhc)
  linarith

/-- **The robustness box at `t = 0`**: on `|Δε| ≤ 1/20`, `|Δα| ≤ 1/25`, `|Δβ| ≤ 3/10` around
`(3/10, 1/20, 9/10)` with `h/c = 20`, the channel margin is at least its value at the worst corner
`(1/4, 9/100, 3/5)`, which is `391/100` (the source's `+3.910`); and `m_0 = 1073/140` (`= 7.664…`).
Source: [[corr-wf14-inventory]] 116 / approval-final.md S4(i), P3 ("worst `m = +3.910`", "`m_0 = +7.664`")
Kind: N+ (one cell by monotonicity, not 27 by enumeration)
Fidelity: exact
Hyps: (a) only -/
theorem box_worst_corner (ε α β : ℝ) (hε : ε ∈ Set.Icc (1 / 4 : ℝ) (7 / 20))
    (hα : α ∈ Set.Icc (1 / 100 : ℝ) (9 / 100)) (hβ : β ∈ Set.Icc (3 / 5 : ℝ) (6 / 5)) :
    391 / 100 ≤ effMargin ε β α (3 / 10) 1 1 20 ∧
      effMargin (1 / 4) (3 / 5) (9 / 100) (3 / 10) 1 1 20 = 391 / 100 ∧
      effMargin (3 / 10) (9 / 10) (1 / 20) (3 / 10) 1 1 20 = 1073 / 140 := by
  refine ⟨?_, ?_, ?_⟩
  · have := effMargin_one_mono (ε := 1 / 4) (ε' := ε) (β := 3 / 5) (β' := β) (α := 9 / 100) (α' := α)
      (3 / 10) 1 20 (by norm_num) (by norm_num) hε.1 (by linarith [hε.2]) (by norm_num) hβ.1
      (by norm_num) hα.2
    simp only [effMargin_one] at this ⊢
    norm_num at this ⊢
    linarith
  · rw [effMargin_one]; norm_num
  · rw [effMargin_one]; norm_num

end Margin

end Cleanroom.Corrigibility.CorrLandscape

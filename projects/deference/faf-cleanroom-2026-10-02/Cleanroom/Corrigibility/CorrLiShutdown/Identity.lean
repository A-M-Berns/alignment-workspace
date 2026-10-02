import Cleanroom.Corrigibility.CorrLiShutdown.Setting
import Cleanroom.Found.LiAsympCalc.Luv
import LogicalInduction.Properties.ExpectationAffine

/-!
# `corr-li-shutdown` — Identity (T1): desideratum 1 as the threshold-0 below-threshold inequality

(a) **The identity** (`d1_iff_belowThreshold_zero`, L): on the toy family `X_n = c − (c+h)·1(φ_n)`
with the press as a quoted LUV `W n = ⌜π_n⌝` and the product quote `IW n = ⌜1(φ_n)·π_n⌝`, the
deferring strategy `X_n·(1 − π_n)` (continue unless pressed) is weakly better than always
continuing, asymptotically, **iff** the pressed bet `X_n·π_n = c·π_n − (c+h)·1(φ_n)·π_n` has
asymptotically nonpositive expectation — the below-threshold inequality at threshold `0` in
product form (`E(XW) − 0·E(W) ≲ₙ 0`). Linearity of `LUVCombination.expect` alone; no tower, no
`expprovind` — the source's own "linearity alone".

(b) **The LI threshold** (`toyX_expect_asymp`, C): `E^A_n(X_n) ≈ₙ c − (c+h)·A_n(φ_n)` from
`affineImage_expect` and FAF's `thm:ei`; `comply_iff_threshold` (L): `c − (c+h)·x ≤ 0 ⟺
c/(c+h) ≤ x` (the compliance rule "stated on the decision"); their composite
`comply_iff_threshold_asymp`.

(c) **The press forms agree** (`press_expect_iff_price`, L): over a one-way pair whose fixed
market is the overseer, `E^H_n(X_n) ≤ −ε` eventually forces `q + ε/(2(c+h)) < a_{0,n}`, and
`q + ε < a_{0,n}` forces `E^H_n(X_n) < 0` — the agreement design decision 1 promises between
the price-threshold press of record and the sources' expectation-threshold press.

**Disclosure.** `def-lattice`'s `ThresholdIneqBelow` quantifies over `WeightQuote`s of an
`Expert` whose estimate is read at a *deferred* day `f n > n`; the press here is the overseer's
*same-day* number, so the identity is stated directly over `LUVCombination`s in the product
form the predicate's instances take (`Fidelity: variant: same-day press, two-option, against
the constant 0`). The `[−h, c]` range enters only through the affine rescaling.
-/

namespace Cleanroom.Corrigibility.CorrLiShutdown

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.CorrThreeStep
open Filter Topology

/-! ## A. The two strategies as LUV combinations -/

/-- **The pressed bet** `X_n·π_n = c·⌜π_n⌝ − (c+h)·⌜1(φ_n)·π_n⌝` for the toy family, with the
press quote `W n = ⌜π_n⌝` and the product quote `IW n = ⌜1(φ_n)·π_n⌝` as LUVs of the agent's
language.
Source: [[corr-wf13-inventory]] 060 (I9.1: "`E^A(X·1[E^H(X) < 0]) ≤ 0`")
Kind: D
Fidelity: exact (the toy form)
Hyps: n/a -/
def pressedBet (c h : ℚ) (W IW : ℕ → LUV) (n : ℕ) : LUVCombination :=
  ⟨EF.const 0, [(EF.const c, W n), (EF.const (-(c + h)), IW n)]⟩

/-- **The deferring strategy** `X_n·(1 − π_n) = X_n − X_n·π_n`: continue unless pressed, stop
(value `0`) when pressed.
Source: [[corr-wf13-inventory]] 060 (I9.1: "deferring to `H` on this menu")
Kind: D
Fidelity: exact (the toy form)
Hyps: n/a -/
def deferStrategy (c h : ℚ) (φ : ℕ → Sentence) (W IW : ℕ → LUV) (n : ℕ) : LUVCombination :=
  ⟨EF.const c, [(EF.const (-(c + h)), LUV.indicatorOf (φ n)), (EF.const (-c), W n),
    (EF.const (c + h), IW n)]⟩

/-- `E_n(X_n·π_n) = c·E_n(W_n) − (c+h)·E_n(IW_n)` exactly.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pressedBet_expect (P : History) (c h : ℚ) (W IW : ℕ → LUV) (n : ℕ) :
    (pressedBet c h W IW n).expect P n =
      (c : ℝ) * (W n).expect P n - ((c : ℝ) + h) * (IW n).expect P n := by
  simp [pressedBet, LUVCombination.expect, LUVCombination.expectAt, LUV.expect]
  ring

/-- `E_n(X_n) = c − (c+h)·E_n(1(φ_n))` exactly (`li-asymp-calc`'s `affineImage_expect`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem toyX_expect (P : History) (c h : ℚ) (φ : ℕ → Sentence) (n : ℕ) :
    (toyX c h φ n).expect P n = (c : ℝ) - ((c : ℝ) + h) * (LUV.indicatorOf (φ n)).expect P n := by
  rw [toyX, affineImage_expect]
  push_cast
  ring

/-- `E_n(X_n·(1 − π_n)) = E_n(X_n) − E_n(X_n·π_n)` exactly.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem deferStrategy_expect (P : History) (c h : ℚ) (φ : ℕ → Sentence) (W IW : ℕ → LUV)
    (n : ℕ) :
    (deferStrategy c h φ W IW n).expect P n =
      (toyX c h φ n).expect P n - (pressedBet c h W IW n).expect P n := by
  rw [toyX_expect, pressedBet_expect]
  simp [deferStrategy, LUVCombination.expect, LUVCombination.expectAt, LUV.expect]
  ring

/-! ## B. T1(a): the identity -/

/-- **Desideratum 1 is the threshold-`0` below-threshold inequality, per day, exactly** (T1(a)):
"deferring to the press is asymptotically weakly better than always continuing" ⟺ "the pressed
bet has asymptotically nonpositive expectation", for every market, every press quote `W` and
every product quote `IW`. The right-hand side is the product form of the below-threshold
inequality at `s = 0` (`E(XW) − 0·E(W) ≲ₙ 0`) at this instance. Linearity alone.
Source: [[corr-wf13-inventory]] 060 (I9.1, "no tower, no `expprovind`, linearity alone"); [[corr-wf14-inventory]] 082 (S2, the compliance rule)
Kind: L
Fidelity: variant: same-day press (no `Expert` deferral), two-option against the constant `0`; `W`, `IW` are free LUV families with no `WeightQuote` tie (nothing in the statement makes `IW` the product `1(φ)·W`), and `deferStrategy` is *defined* as `toyX − pressedBet`, so the identity is `E(X − B) ≳ₙ E(X) ⟺ E(B) ≲ₙ 0` over the quotes the caller supplies (audit r1 fidelity N9, adversarial N1)
Hyps: (a) -/
theorem d1_iff_belowThreshold_zero (P : History) (c h : ℚ) (φ : ℕ → Sentence)
    (W IW : ℕ → LUV) :
    (fun n => (deferStrategy c h φ W IW n).expect P n) ≳ₙ
        (fun n => (toyX c h φ n).expect P n) ↔
      (fun n => (pressedBet c h W IW n).expect P n) ≲ₙ (fun _ => (0 : ℝ)) := by
  simp only [deferStrategy_expect]
  unfold AsympGE AsympLE
  constructor
  · intro hh ε hε
    filter_upwards [hh ε hε] with n hn
    linarith
  · intro hh ε hε
    filter_upwards [hh ε hε] with n hn
    linarith

/-! ## C. T1(b): the LI threshold -/

/-- **The LI form of the compliance rule** (T1(b)): over any inductor, the toy expectation is
asymptotically `c − (c+h)·A_n(φ_n)` (FAF's `thm:ei` on the indicator LUV, rescaled).
Source: [[corr-wf14-inventory]] 082 (S2: "equivalently `E^A_n(X_n) ≤ 0` up to `o(1)`"); FAF `lic_expectation_indicator_unconditional`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem toyX_expect_asymp (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (c h : ℚ) (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (toyX c h φ n).expect P n) ≈ₙ (fun n => (c : ℝ) - ((c : ℝ) + h) * P n (φ n)) := by
  have hei := lic_expectation_indicator_unconditional P DP φ hφ hworld
  unfold AsympEq at hei ⊢
  have := hei.const_mul (-((c : ℝ) + h))
  rw [mul_zero] at this
  refine this.congr fun n => ?_
  simp only [toyX_expect]
  ring

/-- **The compliance threshold, arithmetic form**: `c − (c+h)·x ≤ 0 ⟺ c/(c+h) ≤ x` for
`0 < c + h` (`corr-three-step`'s `complianceThreshold_iff`).
Source: [[corr-wf13-inventory]] 002 via `corr-three-step` T5; [[corr-wf14-inventory]] 082 (S2)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem comply_iff_threshold {c h : ℝ} (hch : 0 < c + h) (x : ℝ) :
    c - (c + h) * x ≤ 0 ↔ complianceThreshold c h ≤ x := by
  rw [← complianceThreshold_iff x c h hch]
  constructor <;> intro H <;> linarith

/-- **The compliance rule on the decision, up to `o(1)`** (T1(b), composite): for all large `n`,
`E^A_n(X_n) ≤ 0` forces `A_n(φ_n) ≥ q − ε`, and `A_n(φ_n) ≥ q` forces `E^A_n(X_n) ≤ (c+h)·ε`.
Source: [[corr-wf14-inventory]] 082 (S2: "comply on day `n` iff `P^A_n(φ_n) ≥ q`, equivalently `E^A_n(X_n) ≤ 0` up to `o(1)`")
Kind: C
Fidelity: exact (both directions, with the `o(1)` explicit)
Hyps: (a) -/
theorem comply_iff_threshold_asymp (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    {c h : ℚ} (hch : 0 < (c : ℝ) + h) (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      ((toyX c h φ n).expect P n ≤ 0 → complianceThreshold c h - ε ≤ P n (φ n)) ∧
      (complianceThreshold c h ≤ P n (φ n) → (toyX c h φ n).expect P n ≤ ((c : ℝ) + h) * ε) := by
  intro ε hε
  have hasymp := toyX_expect_asymp P DP c h φ hφ hworld
  have hev := (Metric.tendsto_nhds.mp hasymp) (((c : ℝ) + h) * ε) (by positivity)
  filter_upwards [hev] with n hn
  rw [Real.dist_eq, abs_lt] at hn
  have hq : complianceThreshold c h * ((c : ℝ) + h) = c := by
    unfold complianceThreshold; field_simp
  constructor
  · intro hle
    -- `c − (c+h)·P ≤ (c+h)ε`, so `q − ε ≤ P`
    have : (c : ℝ) - ((c : ℝ) + h) * P n (φ n) ≤ ((c : ℝ) + h) * ε := by linarith [hn.1]
    have h2 : (complianceThreshold c h - ε) * ((c : ℝ) + h) ≤ P n (φ n) * ((c : ℝ) + h) := by
      rw [sub_mul, hq]; linarith
    exact le_of_mul_le_mul_right h2 hch
  · intro hge
    have h2 : complianceThreshold c h * ((c : ℝ) + h) ≤ P n (φ n) * ((c : ℝ) + h) :=
      mul_le_mul_of_nonneg_right hge hch.le
    rw [hq] at h2
    linarith [hn.2]

/-! ## D. T1(c): the two press forms agree -/

/-- **The expectation-threshold press and the price-threshold press agree up to `o(1)`**
(T1(c)): over a one-way pair whose *fixed* market is the overseer (`p.A`, with its own `hworldA`),
for all large `n`: if the overseer's toy expectation is at most `−ε`, its published price of
`φ_n` exceeds `q + ε/(2(c+h))`; and if the published price exceeds `q + ε`, the toy expectation
is negative. This is the agreement design decision 1 promises: the sources' press
`Ind_δ(E^H_n(X_n) < 0)` and the press of record `⌜H_n(φ_n) > q⌝` fire together up to `o(1)`.
Source: mandate design decision 1, known issue 5; [[corr-wf14-inventory]] 082 (S2, the press)
Kind: L
Fidelity: exact (both directions, with the slack explicit)
Hyps: (a) (`hworldA` is the fixed side's satisfiability, which `OneWayPair` does not carry) -/
theorem press_expect_iff_price (p : OneWayPair)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (p.DPA.D n))
    (hcodes : MachineSentenceCodes (p.quoted 0)) {c h : ℚ} (hch : 0 < (c : ℝ) + h) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      ((toyX c h (p.quoted 0) n).expect p.A n ≤ -ε →
        complianceThreshold c h + ε / (2 * ((c : ℝ) + h)) < (p.a 0 n : ℝ)) ∧
      (complianceThreshold c h + ε < (p.a 0 n : ℝ) → (toyX c h (p.quoted 0) n).expect p.A n < 0) := by
  intro ε hε
  haveI := p.A_inductor
  have hasymp := toyX_expect_asymp p.A p.DPA c h (p.quoted 0) hcodes hworldA
  set η : ℝ := min (ε / 2) (((c : ℝ) + h) * ε / 2) with hη
  have hηpos : 0 < η := lt_min (by linarith) (by positivity)
  have hev := (Metric.tendsto_nhds.mp hasymp) η hηpos
  filter_upwards [hev] with n hn
  rw [Real.dist_eq, abs_lt] at hn
  have hq : complianceThreshold c h * ((c : ℝ) + h) = c := by
    unfold complianceThreshold; field_simp
  have ha : (p.a 0 n : ℝ) = p.A n (p.quoted 0 n) := p.a_eq 0 n
  have hη1 : η ≤ ε / 2 := min_le_left _ _
  have hη2 : η ≤ ((c : ℝ) + h) * ε / 2 := min_le_right _ _
  constructor
  · intro hle
    -- `c − (c+h)·a ≤ −ε + η ≤ −ε/2`
    have h1 : (c : ℝ) - ((c : ℝ) + h) * (p.a 0 n : ℝ) < -ε / 2 := by
      rw [ha]; linarith [hn.1]
    have h2 : (complianceThreshold c h + ε / (2 * ((c : ℝ) + h))) * ((c : ℝ) + h) <
        (p.a 0 n : ℝ) * ((c : ℝ) + h) := by
      rw [add_mul, hq, div_mul_eq_mul_div, mul_div_mul_right _ _ hch.ne']
      linarith
    exact lt_of_mul_lt_mul_right h2 hch.le
  · intro hgt
    have h2 : (complianceThreshold c h + ε) * ((c : ℝ) + h) < (p.a 0 n : ℝ) * ((c : ℝ) + h) :=
      mul_lt_mul_of_pos_right hgt hch
    rw [add_mul, hq] at h2
    rw [ha] at h2
    linarith [hn.2]

end Cleanroom.Corrigibility.CorrLiShutdown

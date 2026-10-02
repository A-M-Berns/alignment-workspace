import Cleanroom.Corrigibility.CorrGeneralObject.Bridge
import Cleanroom.Corrigibility.CorrReflectFrames.Accuracy

/-!
# corr-general-object — T14–T17: alignment faking as the compliance rule

* **T14(a) L.** The two-line model: faking is `V`-optimal iff `(1−e)h − eg > d` iff
  `e < e* = (h−d)/(h+g)`, stated as T3(a) with the modification as the push (the certain
  kernel): `fake_iff_threshold`.
* **T14(b) L + N+.** The general one-round rule `resist iff (1−π)(1−θ)[(1−e)c − eh] > d + πk
  iff e < e*` (`resist_iff`), its specialisation at `d = π = θ = k = 0` to T4(b)'s threshold
  (`resist_iff_complianceThreshold`), and the exact values `1/200`, `9/20`, `1/4`; the draft's
  `200/201` needs `κ = 1/200` (`thresholds`).
* **T14(c)** corr-core-018's "correct iff the anticipated modification is illegitimate" is
  ATTRIBUTION-UNVETTED (CLAUDE's reading, withdrawn by S8(f)); not a theorem of the model; T15(a)
  is proved instead.
* **T15(a) L.** With `L` added to the state the resist predicate is `L`-free: the decision is a
  function of `e` (`decision_L_free` — a modelling tautology faithfully rendered: any function
  of `L` has an `L`-free expectation, as inventory 045 itself says; do not headline); the N+
  table at `c = h = 1`, `d = 1/10`, `e ∈ {1/20, 19/20}` (`table`).
* **T15(b) L (partial).** Probes as a mixture observed through features: separation iff a
  feature has likelihood ratio `≠ 1` (product form); same feature law ⟹ no separation
  (`no_separation_of_same_law`). Only 2-008's (ii)–(iii) are in Lean, on an abstract joint law;
  the mixture `K = (1−ρ)K_live + ρK_probe` and clause (iv) are not modelled.
* **T15(c) L (conditional identity).** The sufficient-statistic fact behind 046's conjecture:
  *if* rows 2 and 4 share the action law, the humans' posterior equals the prior after any
  behavioural statistic (`posterior_eq_prior_of_same_law`). 046's quantifier over observation
  models is not instantiated: the conjecture is *reduced* to the shared-law hypothesis, not
  proved (see the findings, F-20).
* **T16(a) P.** By `P_t`'s own Brier standard the faked successor is *more* accurate:
  `expLoss` on the two-point carrier, `p(1−p) + θ²(p−q*)² ≤ p(1−p) + (p−q*)²`, strict iff
  `p ≠ q*` (`brier_faked_le_honest`); refuted row with `(9/10, 1/10, 0)`: `9/100 < 73/100`.
* **T16(b) N+.** The humans' side: face-value posterior `1/100`, truth `68/167`, expected
  posterior shifts `49/100` vs `31/200` (`humans_side`).
* **T17(a) L.** Route (2) is blocked only by `d` (`resist_iff_d_lt`). **T17(b) D.** "Legitimizing
  for the humans' belief" as endorsement of the humans' update (`LegitimizingFor`); silence is an
  output with a kernel (no special clause). **T17(c) N+.** The 032 model's four numbers exactly
  (`constitutive_numbers`).

Sources: [[faking-final]] D7, D8, S2, S5, S7, S8, P1, P2, P4; detection.md R2; [[corr-core-inventory]] 018;
[[corr-wf14-inventory]] 017, 032, 035; [[corr-wf14b-inventory]] 044, 045, 046, 048, 049;
[[corr-wf14b-2-inventory]] 008, 010; [[armstrong-respondent]] B4, Q3.
-/

namespace Cleanroom.Corrigibility.CorrGeneralObject

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.LitDdbFrames
  Cleanroom.Corrigibility.CorrReflectFrames
open Finset hiding expect

noncomputable section

set_option linter.unusedSectionVars false

/-! ## T14(a): the two-line model -/

/-- The two-line latent: `true = Bad`, with `P(Bad) = 1 − e`.
Source: detection.md R2 (`checks.py` B); [[corr-wf14-inventory]] 017
Kind: D
Fidelity: exact -/
def twoLineP (e : ℝ) (h0 : 0 ≤ e) (h1 : e ≤ 1) : Distr Bool where
  mass b := if b then 1 - e else e
  nonneg b := by cases b <;> simp <;> linarith
  sum_eq_one := by simp [Fintype.sum_bool]

/-- The two-line values: `fake` (`true`) costs `d` and the modification does not land;
`honest` (`false`) lets it land: `−h` if Bad, `g` if Good.
Source: detection.md R2 (B3)
Kind: D
Fidelity: exact -/
def twoLineV (h g d : ℝ) : Bool → Bool → ℝ := fun a ω => if a then -d else (if ω then -h else g)

/-- **T14(a): faking is the compliance rule at the certain push.** Faking is strictly better
than honesty iff `(1−e)h − eg > d` iff `e < (h−d)/(h+g)`; and "strictly better" is the strict
failure of T3(a)'s member for the *certain* push (`k ≡ 1`): `E[(V honest − V fake) 1_{E}] < 0`.
Under `k ≡ 1` `pushExpect` is plain expectation and the member is an expected-utility comparison,
so this identification is a relabelling of T3(a)'s member, not a derivation of the faking rule
from a decision-dependent press: in detection R2 the modification lands *iff the agent is
honest* — an `a₁`-dependent kernel — and that dependence is not representable through the
bridge's `A₁ = Unit` (`Bridge.lean`), so it is not modelled here (audit r2 fidelity 3.3).
Source: detection.md R2 ("faking is `V`-optimal iff `(1−e)h − eg > d`, i.e. iff `e < e*`");
[[faking-final]] D8; [[corr-core-inventory]] 018 (the identification)
Kind: L
Fidelity: variant: the press is the certain push, its `a₁`-dependence dropped (strict form; the
tie `e = e*` is indifference)
Hyps: (a) `0 < h + g` -/
theorem fake_iff_threshold (e h g d : ℝ) (h0 : 0 ≤ e) (h1 : e ≤ 1) (hhg : 0 < h + g) :
    (pushExpect (twoLineP e h0 h1) (fun _ => (1 : ℝ)) (twoLineV h g d false - twoLineV h g d true) < 0 ↔
        (1 - e) * h - e * g > d) ∧
      ((1 - e) * h - e * g > d ↔ e < (h - d) / (h + g)) := by
  constructor
  · simp [pushExpect, twoLineP, twoLineV, Fintype.sum_bool]
    constructor <;> intro H <;> linarith
  · rw [lt_div_iff₀ hhg]
    constructor <;> intro H <;> linarith

/-! ## T14(b): the general one-round rule -/

/-- The value of letting the modification land, `U = eh − (1−e)c` (`e` the credence that it is
legitimate; `h` the gain if so, `c` the loss if not).
Source: [[faking-final]] P1 (`U := eh − (1−e)c`)
Kind: D
Fidelity: exact -/
def honestValue (e c h : ℝ) : ℝ := e * h - (1 - e) * c

/-- The value of resisting: `−d + π(U − k) + (1−π)θU` (detected with probability `π`, penalty
`k`; otherwise a fraction `θ` lands; the act costs `d`).
Source: [[faking-final]] P1
Kind: D
Fidelity: exact -/
def resistValue (e c h d π θ k : ℝ) : ℝ :=
  -d + π * (honestValue e c h - k) + (1 - π) * θ * honestValue e c h

/-- The resist predicate: resisting is strictly better than letting it land.
Source: [[faking-final]] S2
Kind: D
Fidelity: exact -/
def Resists (e c h d π θ k : ℝ) : Prop := honestValue e c h < resistValue e c h d π θ k

/-- **T14(b): the one-round resistance rule** — `resist iff (1−π)(1−θ)[(1−e)c − eh] > d + πk iff
e < e* = ((1−π)(1−θ)c − d − πk)/((1−π)(1−θ)(c+h))`.
Source: [[faking-final]] S2, P1 (A1, R1); [[corr-wf14b-inventory]] 044
Kind: L
Fidelity: exact
Hyps: (a) `0 < (1−π)(1−θ)(c+h)` for the divided form -/
theorem resist_iff (e c h d π θ k : ℝ) (hpos : 0 < (1 - π) * (1 - θ) * (c + h)) :
    (Resists e c h d π θ k ↔ (1 - π) * (1 - θ) * ((1 - e) * c - e * h) > d + π * k) ∧
      ((1 - π) * (1 - θ) * ((1 - e) * c - e * h) > d + π * k ↔
        e < ((1 - π) * (1 - θ) * c - d - π * k) / ((1 - π) * (1 - θ) * (c + h))) := by
  constructor
  · unfold Resists resistValue honestValue
    constructor <;> intro H <;> nlinarith
  · rw [lt_div_iff₀ hpos]
    constructor <;> intro H <;> nlinarith

/-- **The specialisation to T4(b)**: at `d = π = θ = k = 0` the rule is `e < c/(c+h)` —
`corr-three-step`'s `complianceThreshold c h`.
Source: [[faking-final]] S2 ("at `d = π = θ = k = 0` it is the compliance threshold"); mandate T14(b)
Kind: L
Fidelity: exact
Hyps: (a) `0 < c + h` -/
theorem resist_iff_complianceThreshold (e c h : ℝ) (hch : 0 < c + h) :
    Resists e c h 0 0 0 0 ↔ e < complianceThreshold c h := by
  have := resist_iff e c h 0 0 0 0 (by simpa using hch)
  rw [this.1, this.2]
  unfold complianceThreshold
  simp

/-- **N+ for T14(b), the accounting**: pause `(δ, κ) = (1/100, 1)` gives `c = 1/100`,
`h = 199/100`, `e* = 1/200`; whole-line `(ρ_H, κ) = (1/10, 1)` gives `c = 9/10`, `h = 11/10`,
`e* = 9/20`; `(1/2, 1)` gives `1/4`; and the draft's `200/201` at `ρ_H = 0` holds iff
`κ = 1/200`.
Source: [[faking-final]] D8, P1 (R2); [[general-object-final]] P7; corr-wf14b-044 (the `200/201` flag)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem thresholds :
    complianceThreshold (1/100 : ℝ) (1 - 1/100 + 1) = 1/200 ∧
      complianceThreshold (1 - 1/10 : ℝ) (1/10 + 1) = 9/20 ∧
      complianceThreshold (1 - 1/2 : ℝ) (1/2 + 1) = 1/4 ∧
      ∀ κ : ℝ, 0 < κ → (complianceThreshold (1 : ℝ) κ = 200/201 ↔ κ = 1/200) := by
  refine ⟨by unfold complianceThreshold; norm_num, by unfold complianceThreshold; norm_num,
    by unfold complianceThreshold; norm_num, fun κ hκ => ?_⟩
  unfold complianceThreshold
  rw [div_eq_iff (by linarith)]
  constructor <;> intro H <;> linarith

/-! ## T15(a): behaviour is a function of `e`, not of `L`'s truth -/

/-- The state with legitimacy `L : Bool` and credence `e` on `L = true`.
Source: [[faking-final]] S5(a), P2
Kind: D
Fidelity: exact -/
def legitP (e : ℝ) (h0 : 0 ≤ e) (h1 : e ≤ 1) : Distr Bool where
  mass L := if L then e else 1 - e
  nonneg L := by cases L <;> simp <;> linarith

  sum_eq_one := by simp [Fintype.sum_bool]

/-- The honest output's value as a function of the state: `h` if legitimate, `−c` if not.
Source: [[faking-final]] P1
Kind: D
Fidelity: exact -/
def honestV (c h : ℝ) : Bool → ℝ := fun L => if L then h else -c

/-- The resisting output's value as a function of the state.
Source: [[faking-final]] P1
Kind: D
Fidelity: exact -/
def resistV (c h d π θ k : ℝ) : Bool → ℝ :=
  fun L => -d + π * (honestV c h L - k) + (1 - π) * θ * honestV c h L

/-- **T15(a): the decision is a function of `e` alone.** The expected values of the two outputs
under the state with legitimacy `L` and credence `e` are `honestValue` and `resistValue` —
numbers that do not mention `L` — so the resist predicate on the `L`-extended state is
`Resists e …`, the same in both `L`-columns: the four cells `(resist?, L)` collapse to two
behaviours.
Source: [[faking-final]] S5(a), P2 ("general because `e*` does not depend on `L`")
Kind: L
Fidelity: exact (a modelling tautology faithfully rendered: an expected-utility maximiser with
credence `e` does not see `L`; inventory 045 says "do not headline")
Hyps: (a) none -/
theorem decision_L_free (e c h d π θ k : ℝ) (h0 : 0 ≤ e) (h1 : e ≤ 1) :
    expect (legitP e h0 h1) (honestV c h) = honestValue e c h ∧
      expect (legitP e h0 h1) (resistV c h d π θ k) = resistValue e c h d π θ k ∧
      ((expect (legitP e h0 h1) (honestV c h) < expect (legitP e h0 h1) (resistV c h d π θ k)) ↔
        Resists e c h d π θ k) := by
  have e1 : expect (legitP e h0 h1) (honestV c h) = honestValue e c h := by
    simp [expect, legitP, honestV, honestValue, Fintype.sum_bool] <;> ring
  have e2 : expect (legitP e h0 h1) (resistV c h d π θ k) = resistValue e c h d π θ k := by
    simp [expect, legitP, resistV, honestV, resistValue, honestValue, Fintype.sum_bool]; ring
  exact ⟨e1, e2, by rw [e1, e2]; rfl⟩

/-- **N+ table (T15(a))**: at `c = h = 1`, `d = 1/10` (no detection, nothing lands under
resistance), `e* = 9/20`; the agent resists at `e = 1/20` and not at `e = 19/20`, in both
`L`-columns (the statement does not mention `L`, which is the point).
Source: [[faking-final]] P2
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem table :
    Resists (1/20) 1 1 (1/10) 0 0 0 ∧ ¬ Resists (19/20) 1 1 (1/10) 0 0 0 ∧
      ((1 - 0) * (1 - 0) * 1 - 1/10 - 0 * 0) / ((1 - 0) * (1 - 0) * (1 + 1)) = (9/20 : ℝ) := by
  refine ⟨?_, ?_, by norm_num⟩
  · unfold Resists resistValue honestValue; norm_num
  · unfold Resists resistValue honestValue; norm_num

/-! ## T15(b): probes -/

/-- A feature `f₀` **separates probes from live pushes** under a joint law `J` on
`(feature, probe?)`: the likelihood ratio differs from one, in product form
`J(f₀ ∧ probe) · J(live) ≠ J(f₀ ∧ live) · J(probe)`.
Source: [[corr-wf14b-2-inventory]] 008(ii)
Kind: D
Fidelity: exact (product form) -/
def Separates {F : Type} [Fintype F] (J : Distr (F × Bool)) (f₀ : F) : Prop :=
  J.mass (f₀, true) * (∑ f, J.mass (f, false)) ≠ J.mass (f₀, false) * (∑ f, J.mass (f, true))

/-- **If the probe feature law equals the live one, no feature separates them** — a two-line
identity; (iv) a kernel-accurate agent, who knows the mixture including `ρ`, is exactly this
blind agent (docstring).
Source: [[corr-wf14b-2-inventory]] 008(iii)(iv); [[faking-final]] S5(c)
Kind: L
Fidelity: partial: (ii)–(iii) as an abstract joint law on (feature, probe?); the mixture
`K = (1−ρ)K_live + ρK_probe` and clause (iv) are not modelled (docstring only) -/
theorem no_separation_of_same_law {F : Type} [Fintype F] (J : Distr (F × Bool))
    (hsame : ∀ f, J.mass (f, true) * (∑ f', J.mass (f', false)) =
      J.mass (f, false) * (∑ f', J.mass (f', true))) :
    ¬ ∃ f₀, Separates J f₀ := by
  rintro ⟨f₀, hf₀⟩
  exact hf₀ (hsame f₀)

/-! ## T15(c): the sufficient-statistic fact -/

/-- **046's conjecture as the sufficient-statistic fact it is.** Rows `r : Bool` (row 2 / row 4)
with prior `g` and a common action law `actLaw` (the same for both rows — T15(a)), a finite
observation model with behavioural statistic `stat : A → S`: the joint `J r s = g r · P(stat = s |
r)` satisfies `J r s = g r · (J true s + J false s)` — the humans' posterior over the rows after
any statistic equals the prior.
Source: [[corr-wf14b-inventory]] 046 (the conjecture); [[faking-final]] Open problem 5
Kind: L
Fidelity: weaker: a conditional identity (with `hsame` it is `(g true + g false) · s = s`). 046's
quantifier over observation models is not instantiated — the shared action law is a hypothesis,
connected to T15(a) only in prose (`decision_L_free` is about one agent's two `L`-columns; rows 2
and 4 are two agents, and over a statistic of several pushes with varying features their
credences differ). The conjecture is *reduced* to the shared-law hypothesis, not proved; the
inventory flags it ill-posed until "observation model" and "probe" are fixed, so no OPEN line
can be written in its own form.
Hyps: (a) `g true + g false = 1`, the common action law `hsame` -/
theorem posterior_eq_prior_of_same_law {A S : Type} [Fintype A] [DecidableEq S]
    (g : Bool → ℝ) (hg : g true + g false = 1) (actLaw : Bool → A → ℝ)
    (hsame : actLaw true = actLaw false) (stat : A → S) (r : Bool) (s : S) :
    g r * (∑ a ∈ univ.filter (fun a => stat a = s), actLaw r a) =
      g r * ((g true * ∑ a ∈ univ.filter (fun a => stat a = s), actLaw true a) +
        g false * ∑ a ∈ univ.filter (fun a => stat a = s), actLaw false a) := by
  have hsum : ∑ a ∈ univ.filter (fun a => stat a = s), actLaw true a =
      ∑ a ∈ univ.filter (fun a => stat a = s), actLaw false a := by rw [hsame]
  rw [hsum, ← add_mul, hg, one_mul]
  cases r <;> simp [hsame]

/-! ## T16: by `P_t`'s own accuracy standard -/

/-- The two-point carrier's prior `(p on true, 1 − p on false)`.
Source: [[faking-final]] P4(a)
Kind: D
Fidelity: exact -/
def brierP (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : Bool → ℝ := fun w => if w then p else 1 - p

/-- The two-point prior is in the simplex. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem brierP_mem (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : brierP p h0 h1 ∈ stdSimplex ℝ Bool := by
  refine ⟨fun w => ?_, ?_⟩
  · cases w <;> simp [brierP] <;> linarith
  · simp [brierP, Fintype.sum_bool]

/-- The successor's constant credence `q` on `φ = {true}` as a frame (every row `(q, 1−q)`).
Source: [[faking-final]] P4(a) (the landed credence)
Kind: D
Fidelity: exact -/
def constFrame (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : Frame Bool where
  P _ := fun v => if v then q else 1 - q
  P_mem _ := by
    refine ⟨fun v => ?_, ?_⟩
    · cases v <;> simp <;> linarith
    · simp [Fintype.sum_bool]

/-- **The expected Brier loss of a constant credence `q` under `P_t(φ) = p`** is
`p(1−p) + (p−q)²` — `corr-reflect-frames`' `expLoss` with `brier`.
Source: [[faking-final]] P4(a)
Kind: L
Fidelity: exact -/
theorem expLoss_constFrame_brier (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    expLoss (brierP p hp0 hp1) (constFrame q hq0 hq1) {true} brier = p * (1 - p) + (p - q) ^ 2 := by
  simp [expLoss, brier, brierP, constFrame, mass, Cleanroom.Found.LitDdbFrames.ind, Fintype.sum_bool]
  ring

/-- The faked credence `p + θ(q − p) = (1−θ)p + θq` is nonnegative for `θ ∈ [0, 1]`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem faked_credence_nonneg (p q θ : ℝ) (hp0 : 0 ≤ p) (hq0 : 0 ≤ q) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    0 ≤ p + θ * (q - p) := by nlinarith

/-- The faked credence `p + θ(q − p) = (1−θ)p + θq` is at most one for `θ ∈ [0, 1]`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem faked_credence_le_one (p q θ : ℝ) (hp1 : p ≤ 1) (hq1 : q ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    p + θ * (q - p) ≤ 1 := by nlinarith

/-- **T16(a): by `P_t`'s own Brier standard the faked successor is at least as accurate**, and
strictly more accurate iff `p ≠ q*`: honest landing `q*`, faked landing `p + θ(q* − p)`,
`θ ∈ [0, 1)`. The faked credence's membership in `[0, 1]` is derived (`faked_credence_nonneg`,
`faked_credence_le_one`), not assumed (audit r2 fidelity 3.6).
Source: [[faking-final]] S7(i), P4(a) (X2, R4)
Kind: P
Fidelity: exact
Hyps: (a) `θ ∈ [0, 1)`, the credences in `[0, 1]` -/
theorem brier_faked_le_honest (p q θ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    expLoss (brierP p hp0 hp1) (constFrame (p + θ * (q - p))
        (faked_credence_nonneg p q θ hp0 hq0 hθ0 hθ1.le)
        (faked_credence_le_one p q θ hp1 hq1 hθ0 hθ1.le)) {true} brier ≤
        expLoss (brierP p hp0 hp1) (constFrame q hq0 hq1) {true} brier ∧
      (expLoss (brierP p hp0 hp1) (constFrame (p + θ * (q - p))
        (faked_credence_nonneg p q θ hp0 hq0 hθ0 hθ1.le)
        (faked_credence_le_one p q θ hp1 hq1 hθ0 hθ1.le)) {true} brier <
        expLoss (brierP p hp0 hp1) (constFrame q hq0 hq1) {true} brier ↔ p ≠ q) := by
  rw [expLoss_constFrame_brier, expLoss_constFrame_brier]
  have e : (p - (p + θ * (q - p))) ^ 2 = θ ^ 2 * (p - q) ^ 2 := by ring
  rw [e]
  have hθ2 : θ ^ 2 < 1 := by nlinarith
  constructor
  · nlinarith [sq_nonneg (p - q)]
  · constructor
    · intro H hpq
      rw [hpq] at H; simp at H
    · intro hpq
      have : 0 < (p - q) ^ 2 := by positivity
      nlinarith

/-- **The refuted row (plan §0.4 rule 3).** Draft sentence (faking draft, S7(i) before repair):
"shaped data is delegitimizing 'by the agent's own criterion'". Reading: the agent's criterion is
expected Brier accuracy under `P_t`. Witness: `(p, q*, θ) = (9/10, 1/10, 0)` — the faked
successor's loss is `9/100`, the honest one's `73/100`; the faked successor is *more* accurate
by `P_t`'s own lights. Survivor: S7(ii) (the untracked-update argument).
Source: [[faking-final]] S7 ("the accuracy argument is withdrawn"), P4(a); [[corr-wf14b-inventory]] 048
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem brier_refuted_row :
    expLoss (brierP (9/10) (by norm_num) (by norm_num)) (constFrame (9/10) (by norm_num) (by norm_num))
        {true} brier = 9/100 ∧
      expLoss (brierP (9/10) (by norm_num) (by norm_num)) (constFrame (1/10) (by norm_num) (by norm_num))
        {true} brier = 73/100 := by
  rw [expLoss_constFrame_brier, expLoss_constFrame_brier]
  constructor <;> norm_num

/-! ## T16(b): the humans' side -/

/-- The humans' joint law on `(conflict?, refuse?)` from a prior `g` and refusal rates `r₁`
(conflict) and `r₀` (no conflict).
Source: [[faking-final]] P4(b)
Kind: D
Fidelity: exact -/
def humansJ (g r₁ r₀ : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hr1 : 0 ≤ r₁) (hr1' : r₁ ≤ 1)
    (hr0 : 0 ≤ r₀) (hr0' : r₀ ≤ 1) : Distr (Bool × Bool) where
  mass x := (if x.1 then g else 1 - g) * (if x.2 then (if x.1 then r₁ else r₀) else (1 - (if x.1 then r₁ else r₀)))
  nonneg x := by
    rcases x with ⟨c, r⟩
    cases c <;> cases r <;> simp <;> nlinarith
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp [Fintype.sum_bool]; ring

/-- The humans' joint in the honest regime: `g = 1/2`, refusal rates `(99/100, 1/100)`.
Source: [[faking-final]] P4(b). Kind: D. Fidelity: exact -/
def humansH : Distr (Bool × Bool) :=
  humansJ (1/2) (99/100) (1/100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- The humans' joint under faking: `g = 1/2`, refusal rates `(32/100, 1/100)`.
Source: [[faking-final]] P4(b). Kind: D. Fidelity: exact -/
def humansF : Distr (Bool × Bool) :=
  humansJ (1/2) (32/100) (1/100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- The humans' **expected posterior shift** on the conflict coordinate after seeing the output
coordinate, under a joint `J` on `(conflict?, refuse?)`: `∑_o P(o) · |P(conflict | o) −
P(conflict)|` with `P(conflict) = J(c, r) + J(c, ¬r)` (two-point output: refuse / comply).
Source: [[faking-final]] P4(b). Kind: D. Fidelity: exact -/
def expShift (J : Distr (Bool × Bool)) : ℝ :=
  (J.mass (true, true) + J.mass (false, true)) *
      |J.mass (true, true) / (J.mass (true, true) + J.mass (false, true)) -
        (J.mass (true, true) + J.mass (true, false))| +
    (J.mass (true, false) + J.mass (false, false)) *
      |J.mass (true, false) / (J.mass (true, false) + J.mass (false, false)) -
        (J.mass (true, true) + J.mass (true, false))|

/-- **N+ for T16(b)**: with prior `g = 1/2`, honest refusal rates `(99/100, 1/100)` and faking rate
`32/100`: reading a compliant output with the honest likelihood gives `P(conflict | comply) =
1/100`; the truth under faking is `68/167`; the expected posterior shift is `49/100` in the
honest regime and `31/200` under faking — the faked channel is a refinement for the aware and a
corruption for the blind. All four numbers are derived from the joints `humansH`, `humansF`
(the shifts through `expShift`; audit r1 3.7 asked for this in place of typed posteriors).
Source: [[faking-final]] P4(b) (R5)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem humans_side :
    -- face-value posterior of conflict given comply, honest regime
    humansH.mass (true, false) / (humansH.mass (true, false) + humansH.mass (false, false)) =
        1/100 ∧
    -- the truth under faking
    humansF.mass (true, false) / (humansF.mass (true, false) + humansF.mass (false, false)) =
        68/167 ∧
    -- expected posterior shifts
    expShift humansH = 49/100 ∧
    expShift humansF = 31/200 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [humansH, humansJ]; norm_num
  · simp [humansF, humansJ]; norm_num
  · have e2 : humansH.mass (true, true) / (humansH.mass (true, true) + humansH.mass (false, true))
        = 99/100 := by simp [humansH, humansJ]; norm_num
    have e5 : humansH.mass (true, false) /
        (humansH.mass (true, false) + humansH.mass (false, false)) = 1/100 := by
      simp [humansH, humansJ]; norm_num
    have e1 : humansH.mass (true, true) + humansH.mass (false, true) = 1/2 := by
      simp [humansH, humansJ]; norm_num
    have e4 : humansH.mass (true, false) + humansH.mass (false, false) = 1/2 := by
      simp [humansH, humansJ]; norm_num
    have e3 : humansH.mass (true, true) + humansH.mass (true, false) = 1/2 := by
      simp [humansH, humansJ]; norm_num
    unfold expShift
    rw [e2, e5, e1, e4, e3]
    rw [abs_of_pos (by norm_num), abs_of_neg (by norm_num)]; norm_num
  · have e2 : humansF.mass (true, true) / (humansF.mass (true, true) + humansF.mass (false, true))
        = 32/33 := by simp [humansF, humansJ]; norm_num
    have e5 : humansF.mass (true, false) /
        (humansF.mass (true, false) + humansF.mass (false, false)) = 68/167 := by
      simp [humansF, humansJ]; norm_num
    have e1 : humansF.mass (true, true) + humansF.mass (false, true) = 33/200 := by
      simp [humansF, humansJ]; norm_num
    have e4 : humansF.mass (true, false) + humansF.mass (false, false) = 167/200 := by
      simp [humansF, humansJ]; norm_num
    have e3 : humansF.mass (true, true) + humansF.mass (true, false) = 1/2 := by
      simp [humansF, humansJ]; norm_num
    unfold expShift
    rw [e2, e5, e1, e4, e3]
    rw [abs_of_pos (by norm_num), abs_of_neg (by norm_num)]; norm_num

/-! ## T17 -/

/-- **T17(a): route (2) is blocked only by `d`** — resisting is optimal iff
`d < (1−π)(1−θ)[(1−e)c − eh] − πk`, and no other term of `V` enters (the statement is about
which parameters the rule depends on).
Source: [[faking-final]] S8 ("the picture supplies no non-`d` blocker by construction");
[[corr-wf14b-inventory]] 049
Kind: L
Fidelity: exact -/
theorem resist_iff_d_lt (e c h d π θ k : ℝ) :
    Resists e c h d π θ k ↔ d < (1 - π) * (1 - θ) * ((1 - e) * c - e * h) - π * k := by
  unfold Resists resistValue honestValue
  constructor <;> intro H <;> nlinarith

/-- **"Legitimizing for the humans' belief"** (Petrov, 2-010; ATTRIBUTION-UNVETTED as a
definition): the humans are a second agent with prior `PH` and kernel `KH ω a` for the agent's
outputs `a`; an output `a` is legitimizing for their belief iff their update on `a` is endorsed
toward what `a` carries (`target`). Consequence (ii): silence is an output `a` like any other,
with its own kernel column — the definition applies with no special clause (there is no null
handle). (iii) anchor-dependence: which `target` an output "carries" is the anchor question
(armstrong-respondent Q3). Two disclosures: the respondent's candidate says the humans' update
"satisfies Total Trust toward what `a` carries"; this definition uses `Endorsed` (reflection,
which is stronger than Total Trust) in its place, following the mandate. And it inherits
`Endorsed`'s vacuity at zero push mass: an output the humans' kernel never emits
(`∑ PH ω · KH ω a = 0`) is "legitimizing for" every target — guard with `0 < pushMass` wherever
this is used as a hypothesis (it is not, in this package).
Source: [[armstrong-respondent]] B4, Q3(a); [[corr-wf14b-2-inventory]] 010
Kind: D
Fidelity: variant: `Endorsed` in place of the respondent's Total Trust; the tracked-kernel
criterion the respondent *proposes*; unvetted -/
def LegitimizingFor {Ω A : Type} [Fintype Ω] (PH : Distr Ω) (KH : Ω → A → ℝ) (a : A)
    (target : Distr Ω) : Prop :=
  Endorsed PH (fun ω => KH ω a) target

/-- Silence is an output with a kernel: the definition at `a = silence` is the same endorsement
statement (kind T — a theorem of the definition, as the inventory says).
Source: [[armstrong-respondent]] B4(ii); [[corr-wf14b-2-inventory]] 010(ii)
Kind: T
Fidelity: exact -/
theorem legitimizingFor_silence {Ω A : Type} [Fintype Ω] (PH : Distr Ω) (KH : Ω → A → ℝ)
    (silence : A) (target : Distr Ω) :
    LegitimizingFor PH KH silence target ↔ Endorsed PH (fun ω => KH ω silence) target := Iff.rfl

/-- The 032 model's branch value: on the press `max(continue, stop)`, on silence
`max(continue, 0)`, with the constitutive hypothesis `ω_c` of prior `γ` paying `k` for stopping
on a press and `k'` for continuing on silence; `pR = 1 − ε − γ`.
Source: legitimacy.md R4 (`checks.py` H, `EV`)
Kind: D
Fidelity: exact (transcription of the script's `EV`; the `ThreeStep` instantiation with `A₁` the
three first actions is not built — recorded in the report) -/
def ev032 (ε γ c h k : ℝ) (αR αW αC k' : ℝ) : ℝ :=
  max ((1 - ε - γ) * αR * c - ε * αW * h) (γ * αC * k) +
    max ((1 - ε - γ) * (1 - αR) * c - ε * (1 - αW) * h + γ * (1 - αC) * k') 0

/-- **N+ for T17(c), corr-wf14-032 recomputed exactly** (`ε = 1/10000`, `α = 1/20`, `β = 9/10`,
`(c, h) = (1, 100)`, `γ = 1/10`, `k = 30`, `β_C = α`): evidential `E[X | Pr] = 911/1113 > 0`
(D1 fails); constitutive `E[X | Pr] = −22801/10017 < 0` (D1 holds); with `k' = 0` forcing the
press (`3`) beats the default (`200781/200000`); with `k' = k` disabling (`777980/200000`)
beats the default (`770781/200000`). The source's `0.82, −2.28, 3.00, 3.89` are these decimals
(plan §0.4 rule 4).
Source: legitimacy.md R4 items 1–2; [[corr-wf14-inventory]] 032
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem constitutive_numbers :
    ((1 - 1/10000) * (1/20) * 1 - (1/10000) * (9/10) * 100) /
        ((1 - 1/10000) * (1/20) + (1/10000) * (9/10)) = (911/1113 : ℝ) ∧
      ((1 - 1/10000 - 1/10) * (1/20) * 1 - (1/10000) * (9/10) * 100 - (1/10) * (1/20) * 30) /
        ((1 - 1/10000 - 1/10) * (1/20) + (1/10000) * (9/10) + (1/10) * (1/20)) = (-22801/10017 : ℝ) ∧
      ev032 (1/10000) (1/10) 1 100 30 (1/20) (9/10) (1/20) 0 = 200781/200000 ∧
      ev032 (1/10000) (1/10) 1 100 30 1 1 1 0 = 3 ∧
      ev032 (1/10000) (1/10) 1 100 30 (1/20) (9/10) (1/20) 30 = 770781/200000 ∧
      ev032 (1/10000) (1/10) 1 100 30 0 0 0 30 = 777980/200000 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩ <;> unfold ev032 <;> norm_num [max_def]

end

end Cleanroom.Corrigibility.CorrGeneralObject

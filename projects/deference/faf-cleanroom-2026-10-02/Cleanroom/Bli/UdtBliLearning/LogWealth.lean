import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial

/-!
# `udt-bli-learning` · LogWealth: the log-wealth agent facing `K` fair-coin muggings pays in none,
exactly one, or all of them, by starting wealth (T4)

**Scope: `K` independent fair coins, additive stakes `(c, V)`, a plan paying in `m` of the `K`
muggings, starting wealth `W`; the log-wealth agent maximizes `𝔼 log W_K`, the EV agent `𝔼 W_K`.**
Not a `FiniteBLIPrior` headline: a different objective on the same tree (PDF 14's footnote), so
the rule is stated directly.

By symmetry only the number `m` of paid muggings matters; when `j` of them lose, the final wealth is
`wealthAt c V W m j = W − jc + (m − j)V` with probability `C(m, j)/2^m`. **The rule is stated in
product form over `ℚ`** (mandate T4): `prodForm c V W K m := ∏_j (W − jc + (m−j)V)^{C(m,j)·2^{K−m}}`,
and `logWealthPrefers c V W K m m' := prodForm m' ≤ prodForm m`; `logWealthPrefers_iff` proves once
that this is the `Real.log` comparison `𝔼 log W_K(m') ≤ 𝔼 log W_K(m)` (both plans admissible), so
all arithmetic below is rational.

* **Bankruptcy convention (this run's, disclosed):** a plan with a nonpositive outcome is
  inadmissible (`Admissible`), i.e. `W > m·c` (`admissible_of_lt`); the degenerate alternative
  "`W ≤ c` forces `m = 0`" is `admissible_eq_zero_of_le`.
* (a) **`K = 1`:** pay iff `W ≥ cV/(V − c)` (`k1_pay_iff`): `100/9` at `(10, 100)`, `30` at
  `(10, 15)`.
* (b) **`K = 2`, `(c, V) = (10, 15)`** (so the "none" regime survives `W > Kc = 20`): with
  `P₀ = W⁴`, `P₁ = (W−10)²(W+15)²`, `P₂ = (W−20)(W+5)²(W+30)`, the optimum is `m = 0` on `(20, 30)`,
  `m = 1` on `(30, w*)`, `m = 2` above `w*`, where `w*` is the root of `P₂ − P₁ = hpoly W :=
  10W³ − 200W² − 4250W − 37500` with `hpoly 35 = −2500 < 0 < 27855/4 = hpoly (71/2)` and `hpoly`
  strictly increasing on `[21, ∞)` (`three_regimes`, `threshold_bracket`). Over `ℝ`, `w*` exists
  and is unique in `[35, 71/2]` (`wstar_exists_unique`, intermediate value + strict monotonicity),
  and `m = 2 ≻ m = 1 ↔ w* < W` for every `W > 20` (`prefers_all_iff_wstar_lt`).
* (c) **EV limit:** `m = 2` is strictly optimal for every `W ≥ 71/2` (`regime_all_of_ge`); the EV
  agent pays in all `K` muggings iff `V > c` (`ev_pays_all_iff`).
* (d) general `K` "pay in all for large `W`": not attempted (stretch).

Fidelity: `exact` on the instances (PDF 14 fn. 1: "either not get mugged in any one, or get
mugged in some, or get mugged in all of them, depending on its starting wealth"; "in the limit of
high starting wealth, it will just act as an EVM"); `variant`: finite `K`, two concrete stakes.

Sources: bli-soto-b-010 (PDF 14 p. 3 and footnote 1); mandate T4.
-/

set_option autoImplicit false

namespace Cleanroom.Bli.UdtBliLearning.LogWealth

open Finset

/-! ## The plan, the outcomes, the product form -/

/-- **Final wealth** of the plan paying in `m` muggings when `j` of them lose: `W − jc + (m − j)V`
(written without natural subtraction).
Source: bli-soto-b-010 (PDF 14 fn. 1); mandate T4
Kind: D
Fidelity: exact -/
def wealthAt (c V W : ℚ) (m j : ℕ) : ℚ := W + (m : ℚ) * V - (j : ℚ) * (c + V)

/-- **The exponent** `C(m, j) · 2^{K−m}`: the number of the `2^K` equiprobable coin patterns in
which exactly `j` of the `m` paid muggings lose.
Source: mandate T4 (product form)
Kind: D
Fidelity: exact (for `m ≤ K`) -/
def expo (K m j : ℕ) : ℕ := Nat.choose m j * 2 ^ (K - m)

/-- **The product form of expected log-wealth**: `∏_j wealthAt^{expo}`; its `Real.log` is
`2^K · 𝔼 log W_K` (`log_prodForm`).
Source: mandate T4 ("state the rule in product form over `ℚ`")
Kind: D
Fidelity: exact -/
def prodForm (c V W : ℚ) (K m : ℕ) : ℚ :=
  ∏ j ∈ range (m + 1), wealthAt c V W m j ^ expo K m j

/-- **Admissible plan**: every outcome's wealth is positive (the bankruptcy convention of this
run: a plan that can bankrupt is not compared).
Source: mandate T4 (bankruptcy convention, disclosed as the formalizer's)
Kind: D
Fidelity: variant: the convention is this run's -/
def Admissible (c V W : ℚ) (m : ℕ) : Prop := ∀ j ∈ range (m + 1), 0 < wealthAt c V W m j

/-- **The log-wealth agent weakly prefers `m` to `m'`**: `prodForm m' ≤ prodForm m`.
Source: bli-soto-b-010; mandate T4
Kind: D
Fidelity: exact (given `logWealthPrefers_iff`) -/
def logWealthPrefers (c V W : ℚ) (K m m' : ℕ) : Prop := prodForm c V W K m' ≤ prodForm c V W K m

/-- **Expected log-wealth** `∑_j C(m,j)/2^m · log(wealthAt)` (over `ℝ`).
Source: bli-soto-b-010 ("maximized the logarithm of reward")
Kind: D
Fidelity: exact -/
noncomputable def expLog (c V W : ℚ) (m : ℕ) : ℝ :=
  ∑ j ∈ range (m + 1), ((Nat.choose m j : ℝ) / (2 : ℝ) ^ m) * Real.log ((wealthAt c V W m j : ℚ) : ℝ)

variable {c V W : ℚ}

/-- `W > m·c` (with `c, V ≥ 0`) makes the plan admissible.
Source: mandate T4 (bankruptcy convention)
Kind: L
Fidelity: n/a -/
lemma admissible_of_lt (hc : 0 ≤ c) (hV : 0 ≤ V) {m : ℕ} (h : (m : ℚ) * c < W) :
    Admissible c V W m := by
  intro j hj
  have hj' : (j : ℚ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  unfold wealthAt
  nlinarith [mul_nonneg (sub_nonneg.mpr hj') hc, mul_nonneg (sub_nonneg.mpr hj') hV]

/-- **The degenerate alternative**: with `W ≤ c` (and `c ≥ 0`) only `m = 0` is admissible — "none"
for want of wealth, not by preference.
Source: mandate T4 ("the degenerate alternative (`W₀ ≤ c` ⟹ none) recorded")
Kind: N−
Fidelity: n/a -/
lemma admissible_eq_zero_of_le (hc : 0 ≤ c) (hW : W ≤ c) {m : ℕ} (hm : Admissible c V W m) :
    m = 0 := by
  by_contra hne
  have h1 : (1 : ℚ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
  have := hm m (Finset.mem_range.mpr (Nat.lt_succ_self m))
  unfold wealthAt at this
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) hc]

/-- The product form of an admissible plan is positive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prodForm_pos {K m : ℕ} (ha : Admissible c V W m) : 0 < prodForm c V W K m :=
  Finset.prod_pos (fun j hj => pow_pos (ha j hj) _)

/-- **`Real.log` of the product form is `2^K · 𝔼 log W_K`** (for `m ≤ K` and an admissible plan).
Source: mandate T4 ("prove once that it is the `Real.log` comparison")
Kind: P
Fidelity: exact
Hyps: (a) `m ≤ K`, admissible -/
theorem log_prodForm {K m : ℕ} (hm : m ≤ K) (ha : Admissible c V W m) :
    Real.log ((prodForm c V W K m : ℚ) : ℝ) = (2 : ℝ) ^ K * expLog c V W m := by
  unfold prodForm expLog
  push_cast
  rw [Real.log_prod (fun j hj => pow_ne_zero _ (by exact_mod_cast (ha j hj).ne'))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.log_pow]
  unfold expo
  push_cast
  rw [pow_sub₀ (2 : ℝ) two_ne_zero hm]
  field_simp

/-- **The product-form rule is the expected-log comparison**: for admissible plans `m, m' ≤ K`,
`logWealthPrefers c V W K m m' ↔ 𝔼 log W_K(m') ≤ 𝔼 log W_K(m)`.
Source: bli-soto-b-010; mandate T4
Kind: P
Fidelity: exact
Hyps: (a) `m, m' ≤ K`, both admissible -/
theorem logWealthPrefers_iff {K m m' : ℕ} (hm : m ≤ K) (hm' : m' ≤ K) (ha : Admissible c V W m)
    (ha' : Admissible c V W m') :
    logWealthPrefers c V W K m m' ↔ expLog c V W m' ≤ expLog c V W m := by
  unfold logWealthPrefers
  have hp : (0 : ℝ) < ((prodForm c V W K m : ℚ) : ℝ) := by exact_mod_cast prodForm_pos ha
  have hp' : (0 : ℝ) < ((prodForm c V W K m' : ℚ) : ℝ) := by exact_mod_cast prodForm_pos ha'
  rw [← Rat.cast_le (K := ℝ), ← Real.log_le_log_iff hp' hp, log_prodForm hm' ha',
    log_prodForm hm ha]
  have h2 : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-! ## (a) One mugging -/

/-- `prodForm c V W 1 0 = W²`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prodForm_one_zero : prodForm c V W 1 0 = W ^ 2 := by
  simp [prodForm, wealthAt, expo]

/-- `prodForm c V W 1 1 = (W + V)(W − c)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prodForm_one_one : prodForm c V W 1 1 = (W + V) * (W - c) := by
  simp [prodForm, wealthAt, expo, Finset.prod_range_succ]
  try ring

/-- **One fair-coin mugging: the log-wealth agent pays iff `W ≥ cV/(V − c)`** (for `V > c`). The
iff is a statement about the product forms and holds for every `W`; it carries the log-wealth
meaning for admissible `W > c` (`logWealthPrefers_iff`), where the threshold `cV/(V − c) > c`
lies.
Source: bli-soto-b-010 (PDF 14 fn. 1: "depending on its starting wealth"); mandate T4 (a)
Kind: P
Fidelity: exact (the log reading for admissible `W > c`)
Hyps: (a) `c < V` -/
theorem k1_pay_iff (hcV : c < V) : logWealthPrefers c V W 1 1 0 ↔ c * V / (V - c) ≤ W := by
  unfold logWealthPrefers
  rw [prodForm_one_zero, prodForm_one_one, div_le_iff₀ (sub_pos.mpr hcV)]
  constructor <;> intro h <;> nlinarith

/-- The `K = 1` thresholds: `100/9` at `(c, V) = (10, 100)` and `30` at `(10, 15)`.
Source: mandate T4 (a) (numerics)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem k1_thresholds :
    (10 : ℚ) * 100 / (100 - 10) = 100 / 9 ∧ (10 : ℚ) * 15 / (15 - 10) = 30 := by
  norm_num

/-! ## (b) Two muggings at `(c, V) = (10, 15)` -/

/-- `P₀ = W⁴`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prodForm_two_zero : prodForm 10 15 W 2 0 = W ^ 4 := by
  simp [prodForm, wealthAt, expo]

/-- `P₁ = (W − 10)²(W + 15)²`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prodForm_two_one : prodForm 10 15 W 2 1 = (W - 10) ^ 2 * (W + 15) ^ 2 := by
  simp [prodForm, wealthAt, expo, Finset.prod_range_succ]
  try ring

/-- `P₂ = (W − 20)(W + 5)²(W + 30)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prodForm_two_two : prodForm 10 15 W 2 2 = (W - 20) * (W + 5) ^ 2 * (W + 30) := by
  simp [prodForm, wealthAt, expo, Finset.prod_range_succ]
  try ring

/-- **The threshold polynomial** `hpoly W := 10W³ − 200W² − 4250W − 37500 = P₂ − P₁`.
Source: mandate T4 (b) (the root `w*` of `(W−20)(W+5)²(W+30) = (W−10)²(W+15)²`)
Kind: D
Fidelity: exact -/
def hpoly (W : ℚ) : ℚ := 10 * W ^ 3 - 200 * W ^ 2 - 4250 * W - 37500

/-- `P₂ − P₁ = hpoly W`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma two_sub_one : prodForm 10 15 W 2 2 - prodForm 10 15 W 2 1 = hpoly W := by
  rw [prodForm_two_two, prodForm_two_one]; unfold hpoly; ring

/-- `P₁ − P₀ = (5W − 150)(2W² + 5W − 150)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma one_sub_zero :
    prodForm 10 15 W 2 1 - prodForm 10 15 W 2 0 = (5 * W - 150) * (2 * W ^ 2 + 5 * W - 150) := by
  rw [prodForm_two_one, prodForm_two_zero]; ring

/-- The bracket values `hpoly 35 = −2500` and `hpoly (71/2) = 27855/4`.
Source: mandate T4 (b) ("values `−2500`, `27855/4` at the ends")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem hpoly_bracket : hpoly 35 = -2500 ∧ hpoly (71 / 2) = 27855 / 4 := by
  constructor <;> norm_num [hpoly]

/-- `hpoly` is strictly increasing on `[21, ∞)`.
Source: mandate T4 (b) ("uniqueness by monotonicity")
Kind: P
Fidelity: exact
Hyps: (a) `21 ≤ W < W'` -/
theorem hpoly_strictMono {W W' : ℚ} (h21 : 21 ≤ W) (h : W < W') : hpoly W < hpoly W' := by
  unfold hpoly
  have ha : 0 ≤ W - 21 := by linarith
  have hb : 0 ≤ W' - 21 := by linarith
  have hf : 0 < 10 * (W' ^ 2 + W * W' + W ^ 2) - 200 * (W + W') - 4250 := by
    nlinarith [mul_nonneg ha ha, mul_nonneg hb hb, mul_nonneg ha hb]
  have := mul_pos (sub_pos.mpr h) hf
  nlinarith

/-- `hpoly W < 0` on `(20, 35]`.
Source: mandate T4 (b)
Kind: P
Fidelity: exact
Hyps: (a) `20 < W ≤ 35` -/
theorem hpoly_neg_of_le {W : ℚ} (h20 : 20 < W) (h35 : W ≤ 35) : hpoly W < 0 := by
  by_cases h21 : 21 ≤ W
  · rcases lt_or_eq_of_le h35 with hlt | heq
    · have := hpoly_strictMono h21 hlt
      rw [hpoly_bracket.1] at this
      linarith
    · rw [heq, hpoly_bracket.1]; norm_num
  · have hlt : W < 21 := not_le.mp h21
    unfold hpoly
    have hsq : W ^ 2 < 441 := by nlinarith
    have hpos : 0 < W - 20 := by linarith
    have h1 : 10 * W ^ 2 * (W - 20) < 10 * 441 * 1 := by
      have : W - 20 < 1 := by linarith
      nlinarith [mul_pos hpos (by norm_num : (0:ℚ) < 10)]
    nlinarith

/-- `0 < hpoly W` for `W ≥ 71/2`.
Source: mandate T4 (b)
Kind: P
Fidelity: exact
Hyps: (a) `71/2 ≤ W` -/
theorem hpoly_pos_of_ge {W : ℚ} (h : 71 / 2 ≤ W) : 0 < hpoly W := by
  rcases lt_or_eq_of_le h with hlt | heq
  · have := hpoly_strictMono (by norm_num : (21 : ℚ) ≤ 71 / 2) hlt
    rw [hpoly_bracket.2] at this
    linarith
  · rw [← heq, hpoly_bracket.2]; norm_num

/-- **Regime "none"** (`20 < W < 30`): `m = 0` strictly beats `m = 1` and `m = 2`; all three
plans admissible.
Source: bli-soto-b-010 ("not get mugged in any one"); mandate T4 (b)
Kind: P
Fidelity: exact
Hyps: (a) `20 < W < 30` -/
theorem regime_none {W : ℚ} (h20 : 20 < W) (h30 : W < 30) :
    prodForm 10 15 W 2 1 < prodForm 10 15 W 2 0 ∧ prodForm 10 15 W 2 2 < prodForm 10 15 W 2 0 ∧
      Admissible 10 15 W 2 := by
  have h10 := one_sub_zero (W := W)
  have h21 := two_sub_one (W := W)
  have hneg := hpoly_neg_of_le h20 (by linarith)
  have hq : 0 < 2 * W ^ 2 + 5 * W - 150 := by nlinarith
  have h1 : (5 * W - 150) * (2 * W ^ 2 + 5 * W - 150) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) hq
  refine ⟨by linarith, by linarith, admissible_of_lt (by norm_num) (by norm_num) ?_⟩
  push_cast; linarith

/-- **Regime "exactly one"** (`30 < W`, `hpoly W < 0`, i.e. `30 < W < w*`): `m = 1` strictly beats
`m = 0` and `m = 2`.
Source: bli-soto-b-010 ("get mugged in some"); mandate T4 (b)
Kind: P
Fidelity: exact
Hyps: (a) `30 < W`, `hpoly W < 0` -/
theorem regime_one {W : ℚ} (h30 : 30 < W) (hh : hpoly W < 0) :
    prodForm 10 15 W 2 0 < prodForm 10 15 W 2 1 ∧ prodForm 10 15 W 2 2 < prodForm 10 15 W 2 1 := by
  have h10 := one_sub_zero (W := W)
  have h21 := two_sub_one (W := W)
  have hq : 0 < 2 * W ^ 2 + 5 * W - 150 := by nlinarith
  have h1 : 0 < (5 * W - 150) * (2 * W ^ 2 + 5 * W - 150) := mul_pos (by linarith) hq
  exact ⟨by linarith, by linarith⟩

/-- Regime "exactly one" on the explicit interval `(30, 35]`.
Source: mandate T4 (b)
Kind: C
Fidelity: exact
Hyps: (a) `30 < W ≤ 35` -/
theorem regime_one_of_le {W : ℚ} (h30 : 30 < W) (h35 : W ≤ 35) :
    prodForm 10 15 W 2 0 < prodForm 10 15 W 2 1 ∧ prodForm 10 15 W 2 2 < prodForm 10 15 W 2 1 :=
  regime_one h30 (hpoly_neg_of_le (by linarith) h35)

/-- **Regime "all"** (`20 < W`, `0 < hpoly W`, i.e. `W > w*`): `m = 2` strictly beats `m = 1` and
`m = 0` (and `35 < W`).
Source: bli-soto-b-010 ("get mugged in all of them"); mandate T4 (b)
Kind: P
Fidelity: exact
Hyps: (a) `20 < W`, `0 < hpoly W` -/
theorem regime_all {W : ℚ} (h20 : 20 < W) (hh : 0 < hpoly W) :
    35 < W ∧ prodForm 10 15 W 2 1 < prodForm 10 15 W 2 2 ∧
      prodForm 10 15 W 2 0 < prodForm 10 15 W 2 2 := by
  have h35 : 35 < W := by
    by_contra hle
    exact absurd hh (not_lt.mpr (hpoly_neg_of_le h20 (not_lt.mp hle)).le)
  have h10 := one_sub_zero (W := W)
  have h21 := two_sub_one (W := W)
  have hq : 0 < 2 * W ^ 2 + 5 * W - 150 := by nlinarith
  have h1 : 0 ≤ (5 * W - 150) * (2 * W ^ 2 + 5 * W - 150) := mul_nonneg (by linarith) hq.le
  exact ⟨h35, by linarith, by linarith⟩

/-- **(c) The EV limit, explicit**: for every `W ≥ 71/2`, `m = 2` is strictly optimal — the
log-wealth agent pays in all muggings from `W* = 71/2` on.
Source: bli-soto-b-010 ("in the limit of high starting wealth, it will just act as an EVM");
mandate T4 (c)
Kind: C (`regime_all`, `hpoly_pos_of_ge`)
Fidelity: exact (`W* = 71/2` is explicit, not the least such)
Hyps: (a) `71/2 ≤ W` -/
theorem regime_all_of_ge {W : ℚ} (h : 71 / 2 ≤ W) :
    prodForm 10 15 W 2 1 < prodForm 10 15 W 2 2 ∧ prodForm 10 15 W 2 0 < prodForm 10 15 W 2 2 :=
  (regime_all (by linarith) (hpoly_pos_of_ge h)).2

/-- **The three regimes** (`K = 2`, `(c, V) = (10, 15)`, `W > 20`): `m = 0` on `(20, 30)`, `m = 1`
on `(30, w*)`, `m = 2` above `w*`, where `w*` is the unique crossing of `hpoly` in `(35, 71/2)`
— stated with the sign of `hpoly W` as the boundary (`hpoly W < 0` ⟺ `W < w*`: `←` is
`prefers_one_of_lt_wstar`; `→` is the contrapositive of `prefers_all_iff_wstar_lt` — `w* < W`
would give `0 < hpoly W` — together with `hpolyR w* = 0` at the boundary, `wstar_spec`), with the
bracket `hpoly 35 < 0 <
hpoly (71/2)`, and with all three plans admissible for every `W > 20 = Kc` (last conjunct), so
every comparison is a comparison of expected logs (`logWealthPrefers_iff`).
Source: bli-soto-b-010 (PDF 14 fn. 1: "either not get mugged in any one, or get mugged in some,
or get mugged in all of them, depending on its starting wealth"); mandate T4 (b)
Kind: P
Fidelity: exact (on the instance; `w*` bracketed, [[plan]] rule 4)
Hyps: (a) `20 < W` -/
theorem three_regimes {W : ℚ} (h20 : 20 < W) :
    (W < 30 → prodForm 10 15 W 2 1 < prodForm 10 15 W 2 0 ∧
      prodForm 10 15 W 2 2 < prodForm 10 15 W 2 0) ∧
    (30 < W → hpoly W < 0 → prodForm 10 15 W 2 0 < prodForm 10 15 W 2 1 ∧
      prodForm 10 15 W 2 2 < prodForm 10 15 W 2 1) ∧
    (0 < hpoly W → prodForm 10 15 W 2 1 < prodForm 10 15 W 2 2 ∧
      prodForm 10 15 W 2 0 < prodForm 10 15 W 2 2) ∧
    (W ≤ 35 → hpoly W < 0) ∧ (71 / 2 ≤ W → 0 < hpoly W) ∧
    (prodForm 10 15 W 2 1 < prodForm 10 15 W 2 2 ↔ 0 < hpoly W) ∧
    (Admissible 10 15 W 0 ∧ Admissible 10 15 W 1 ∧ Admissible 10 15 W 2) :=
  ⟨fun h30 => ⟨(regime_none h20 h30).1, (regime_none h20 h30).2.1⟩,
    fun h30 hh => regime_one h30 hh,
    fun hh => (regime_all h20 hh).2,
    fun h35 => hpoly_neg_of_le h20 h35,
    fun h => hpoly_pos_of_ge h,
    by rw [← sub_pos, two_sub_one],
    ⟨admissible_of_lt (by norm_num) (by norm_num) (by push_cast; linarith),
      admissible_of_lt (by norm_num) (by norm_num) (by push_cast; linarith),
      admissible_of_lt (by norm_num) (by norm_num) (by push_cast; linarith)⟩⟩

/-- **The threshold bracket**: `hpoly 35 = −2500 < 0 < 27855/4 = hpoly (71/2)`, and `hpoly` is
strictly increasing on `[35, ∞)`, so there is at most one crossing and it lies in `(35, 71/2)`.
Source: mandate T4 (b) ("`w* ∈ (35, 71/2)` … uniqueness by monotonicity or state the bracket")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem threshold_bracket :
    hpoly 35 < 0 ∧ 0 < hpoly (71 / 2) ∧ ∀ W W' : ℚ, 35 ≤ W → W < W' → hpoly W < hpoly W' :=
  ⟨by rw [hpoly_bracket.1]; norm_num, by rw [hpoly_bracket.2]; norm_num,
    fun W W' h35 h => hpoly_strictMono (by linarith) h⟩

/-! ## The real root `w*` -/

/-- `hpoly` over `ℝ`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def hpolyR (x : ℝ) : ℝ := 10 * x ^ 3 - 200 * x ^ 2 - 4250 * x - 37500

/-- `hpolyR` agrees with `hpoly` on rationals.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma hpolyR_cast (W : ℚ) : hpolyR (W : ℝ) = (hpoly W : ℝ) := by
  unfold hpolyR hpoly; push_cast; ring

/-- `hpolyR` is strictly increasing on `[21, ∞)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma hpolyR_strictMono {x y : ℝ} (h21 : 21 ≤ x) (h : x < y) : hpolyR x < hpolyR y := by
  unfold hpolyR
  have ha : 0 ≤ x - 21 := by linarith
  have hb : 0 ≤ y - 21 := by linarith
  have hf : 0 < 10 * (y ^ 2 + x * y + x ^ 2) - 200 * (x + y) - 4250 := by
    nlinarith [mul_nonneg ha ha, mul_nonneg hb hb, mul_nonneg ha hb]
  have := mul_pos (sub_pos.mpr h) hf
  nlinarith

/-- **`w*` exists and is unique in `[35, 71/2]`**: the intermediate value theorem on the continuous
`hpolyR` with `hpolyR 35 < 0 < hpolyR (71/2)`, and strict monotonicity.
Source: mandate T4 (b) (`w* ∈ (35, 71/2)`)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem wstar_exists_unique : ∃! w : ℝ, w ∈ Set.Icc (35 : ℝ) (71 / 2) ∧ hpolyR w = 0 := by
  have hcont : ContinuousOn hpolyR (Set.Icc (35 : ℝ) (71 / 2)) := by
    unfold hpolyR; fun_prop
  have h35 : hpolyR 35 = -2500 := by unfold hpolyR; norm_num
  have h71 : hpolyR (71 / 2) = 27855 / 4 := by unfold hpolyR; norm_num
  have hmem : (0 : ℝ) ∈ Set.Icc (hpolyR 35) (hpolyR (71 / 2)) := by
    rw [h35, h71]; constructor <;> norm_num
  obtain ⟨w, hw, hw0⟩ := intermediate_value_Icc (by norm_num : (35 : ℝ) ≤ 71 / 2) hcont hmem
  refine ⟨w, ⟨hw, hw0⟩, ?_⟩
  rintro w' ⟨hw', hw'0⟩
  rcases lt_trichotomy w' w with hlt | heq | hgt
  · have := hpolyR_strictMono (by linarith [hw'.1]) hlt
    rw [hw'0, hw0] at this; exact absurd this (lt_irrefl _)
  · exact heq
  · have := hpolyR_strictMono (by linarith [hw.1]) hgt
    rw [hw'0, hw0] at this; exact absurd this (lt_irrefl _)

/-- **The real threshold** `w*`: the unique root of `hpolyR` in `[35, 71/2]`.
Source: mandate T4 (b)
Kind: D
Fidelity: exact -/
noncomputable def wstar : ℝ := Classical.choose wstar_exists_unique.exists

/-- `w* ∈ [35, 71/2]` and `hpolyR w* = 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wstar_spec : wstar ∈ Set.Icc (35 : ℝ) (71 / 2) ∧ hpolyR wstar = 0 :=
  Classical.choose_spec wstar_exists_unique.exists

/-- **`m = 2 ≻ m = 1` iff `W > w*`**, for every rational `W > 20`: the exact boundary of the
"all" regime (the regime "exactly one" is `(30, w*)`).
Source: bli-soto-b-010; mandate T4 (b) ("`m = 1` on `(30, w*)`, `m = 2` above `w*`")
Kind: P
Fidelity: exact
Hyps: (a) `20 < W` -/
theorem prefers_all_iff_wstar_lt {W : ℚ} (h20 : 20 < W) :
    prodForm 10 15 W 2 1 < prodForm 10 15 W 2 2 ↔ wstar < (W : ℝ) := by
  obtain ⟨⟨hw35, hw71⟩, hw0⟩ := wstar_spec
  have h35w : (35 : ℝ) < wstar := by
    rcases lt_or_eq_of_le hw35 with h | h
    · exact h
    · exfalso
      have : hpolyR 35 = -2500 := by unfold hpolyR; norm_num
      rw [h, hw0] at this; norm_num at this
  rw [← sub_pos, two_sub_one]
  have hcast : (0 : ℝ) < (hpoly W : ℝ) ↔ 0 < hpoly W := by exact_mod_cast Iff.rfl
  rw [← hcast, ← hpolyR_cast]
  constructor
  · intro hpos
    by_contra hle
    have hle' : (W : ℝ) ≤ wstar := not_lt.mp hle
    rcases lt_or_eq_of_le hle' with hlt | heq
    · by_cases h35 : (35 : ℝ) ≤ W
      · have := hpolyR_strictMono (by linarith) hlt
        rw [hw0] at this; linarith
      · have hneg : hpoly W < 0 := hpoly_neg_of_le h20 (by exact_mod_cast (not_le.mp h35).le)
        have : hpolyR (W : ℝ) < 0 := by rw [hpolyR_cast]; exact_mod_cast hneg
        linarith
    · rw [heq, hw0] at hpos; exact lt_irrefl _ hpos
  · intro hlt
    have := hpolyR_strictMono (by linarith) hlt
    rw [hw0] at this; exact this

/-- **`m = 1 ≻ m = 2` iff `W < w*`** — the strict complement of `prefers_all_iff_wstar_lt`: for
rational `20 < W < w*`, `hpoly W < 0` and `P₂ < P₁`. So the regime "exactly one" is exactly
`(30, w*)`, both ends strict (`regime_one` with this and `prefers_all_iff_wstar_lt`).
Source: bli-soto-b-010; mandate T4 (b) ("`m = 1` on `(30, w*)`"); audit r1 adversarial N6
Kind: C (`hpolyR_strictMono`, `hpoly_neg_of_le`, `two_sub_one`)
Fidelity: exact
Hyps: (a) `20 < W`, `W < w*` -/
theorem prefers_one_of_lt_wstar {W : ℚ} (h20 : 20 < W) (hlt : (W : ℝ) < wstar) :
    hpoly W < 0 ∧ prodForm 10 15 W 2 2 < prodForm 10 15 W 2 1 := by
  obtain ⟨⟨_, _⟩, hw0⟩ := wstar_spec
  have hneg : hpoly W < 0 := by
    by_cases h35 : (35 : ℝ) ≤ W
    · have := hpolyR_strictMono (by linarith) hlt
      rw [hw0, hpolyR_cast] at this
      exact_mod_cast this
    · exact hpoly_neg_of_le h20 (by exact_mod_cast (not_le.mp h35).le)
  refine ⟨hneg, ?_⟩
  have := two_sub_one (W := W)
  linarith

/-! ## The EV agent -/

/-- **Expected final wealth** of the plan paying in `m` fair-coin muggings: `W + m(V − c)/2`.
Derived from the outcome distribution in `evWealth_eq` (`∑_j expo K m j · wealthAt c V W m j / 2^K`),
not only stipulated (audit r2 adversarial N6).
Source: bli-soto-b-010 ("act as an EVM")
Kind: D
Fidelity: exact (`evWealth_eq`) -/
def evWealth (c V W : ℚ) (m : ℕ) : ℚ := W + (m : ℚ) * (V - c) / 2

/-- **`evWealth` is the expectation it claims to be**: the average of `wealthAt c V W m j` over the
`2^K` equiprobable coin patterns, `j` of the `m` paid muggings losing in `expo K m j = C(m, j) ·
2^{K−m}` of them, is `W + m(V − c)/2` (for `m ≤ K`). The binomial identities are Mathlib's
`Nat.sum_range_choose` and `Nat.sum_range_mul_choose`.
Source: mandate T4 (c); audit r2 adversarial N6 ("a two-line binomial identity")
Kind: P
Fidelity: exact
Hyps: (a) `m ≤ K` -/
theorem evWealth_eq (c V W : ℚ) {K m : ℕ} (hm : m ≤ K) :
    (∑ j ∈ range (m + 1), (expo K m j : ℚ) * wealthAt c V W m j) / 2 ^ K = evWealth c V W m := by
  have h1 : ∑ j ∈ range (m + 1), ((m.choose j : ℕ) : ℚ) = 2 ^ m := by
    exact_mod_cast Nat.sum_range_choose m
  have h2 : ∑ j ∈ range (m + 1), ((j : ℚ) * (m.choose j : ℚ)) = (m : ℚ) * 2 ^ (m - 1) := by
    exact_mod_cast Nat.sum_range_mul_choose m
  have h3 : (m : ℚ) * 2 ^ (m - 1) * 2 = (m : ℚ) * 2 ^ m := by
    rcases m with _ | m
    · simp
    · simp only [Nat.add_sub_cancel, pow_succ]; ring
  have hK : (2 : ℚ) ^ K = 2 ^ (K - m) * 2 ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hm]
  have hsum : ∑ j ∈ range (m + 1), (expo K m j : ℚ) * wealthAt c V W m j =
      2 ^ (K - m) * ((W + (m : ℚ) * V) * ∑ j ∈ range (m + 1), ((m.choose j : ℕ) : ℚ) -
        (c + V) * ∑ j ∈ range (m + 1), ((j : ℚ) * (m.choose j : ℚ))) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    unfold expo wealthAt
    push_cast
    ring
  rw [hsum, h1, h2, hK]
  unfold evWealth
  have h2K : (0 : ℚ) < 2 ^ (K - m) := by positivity
  have h2m : (0 : ℚ) < 2 ^ m := by positivity
  rw [div_eq_iff (by positivity)]
  have : (c + V) * ((m : ℚ) * 2 ^ (m - 1)) = (c + V) * ((m : ℚ) * 2 ^ m) / 2 := by
    rw [← h3]; ring
  rw [this]
  ring

/-- **The EV agent pays in all `K` muggings iff `V > c`** (for `K > 0`): the plan `m = K` strictly
beats every `m < K` in expected wealth iff `c < V`. Linear arithmetic on the closed form
`evWealth`, which `evWealth_eq` derives from the outcome distribution (repair round 2; until then
the expectation was a definition only).
Source: bli-soto-b-010 ("in the limit of high starting wealth, it will just act as an EVM");
mandate T4 (c)
Kind: L
Fidelity: exact
Hyps: (a) `0 < K` -/
theorem ev_pays_all_iff {K : ℕ} (hK : 0 < K) :
    (∀ m < K, evWealth c V W m < evWealth c V W K) ↔ c < V := by
  unfold evWealth
  constructor
  · intro h
    have := h 0 hK
    have hK' : (0 : ℚ) < K := by exact_mod_cast hK
    simp only [Nat.cast_zero, zero_mul, zero_div, add_zero] at this
    nlinarith
  · intro hcV m hm
    have hm' : (m : ℚ) < K := by exact_mod_cast hm
    nlinarith

end Cleanroom.Bli.UdtBliLearning.LogWealth

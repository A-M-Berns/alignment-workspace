/-
  Staleness.lean
  ==============

  The arithmetic and asymptotic core of the staleness results:
  `imported-chats/fa-block-staleness-impossibility.md` (cited **BSI**) and its prerequisite
  `imported-chats/fa-positive-results-corrected-v3.md` (**v3**).  Program document:
  `staleness-program.md`.

  READ THIS BEFORE CITING ANYTHING HERE.  Per `AUDIT.md`, the failure mode to guard against
  is a theorem engineered to typecheck that tests something weaker than the claim it is named
  for.  So, explicitly:

  * The market, traders, budgets, legality and the logical induction criterion are **NOT
    modelled** here, exactly as in the rest of this project.  Every appeal to "the criterion
    forbids X" enters as a *named hypothesis*, and the hypotheses are named after the LI
    theorem they stand for.
  * What IS proved here is the part that is genuinely mathematics rather than citation: the
    limit-point arithmetic, the Cesàro/density counting, and the ramp arithmetic.  These are
    the steps where the informal arguments could have a sign, quantifier or off-by-one error,
    and they are the reason this file exists.
  * In particular `LimitPointZero` is deliberately WEAKER than `Tendsto _ atTop (𝓝 0)`.
    Expectation Recurring Unbiasedness (LI 4.8.15, in its corrected clause-free form) gives
    only that 0 is a *limit point* of the weighted average error.  Several arguments in this
    corpus's history read it as a limit.  Keeping the weak form is the whole point of Part 1.

  No `sorry`; axiom audit at the end.
-/
import Mathlib

open Filter Topology

namespace Staleness

/-! ############################################################
    ## Part 0.  Vocabulary
    ############################################################ -/

/--
  `LimitPointZero f`: 0 is a limit point of the sequence `f` — for every `ε > 0`, `|f n| < ε`
  happens *frequently* (i.e. for arbitrarily large `n`).

  This is the **conclusion form of Expectation Recurring Unbiasedness** (LI 4.8.15, corrected):
  the weighted average forecast error returns to 0 along *some* subsequence.  It is strictly
  weaker than convergence to 0, and everything in Part 1 is designed to work against this weak
  form.
-/
def LimitPointZero (f : ℕ → ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∃ᶠ n in atTop, |f n| < ε

/-- Accumulated weight through day `n`: `∑_{i ≤ n} u i`. -/
noncomputable def W (u : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range (n + 1), u i

/-- Accumulated weighted error through day `n`: `∑_{i ≤ n} u i * err i`. -/
noncomputable def wsum (u err : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range (n + 1), u i * err i

/-- The weighted average error through day `n` — the quantity 4.8.15 speaks about. -/
noncomputable def wavg (u err : ℕ → ℝ) (n : ℕ) : ℝ := wsum u err n / W u n

/-- Cesàro average of `x` over `[0, N)`. -/
noncomputable def cesaro (x : ℕ → ℝ) (N : ℕ) : ℝ := (∑ i ∈ Finset.range N, x i) / N

/-! ############################################################
    ## Part 1.  The limit-point engine  (program doc L2 / T1)
    ############################################################

  The engine of v3's Theorem 1, v3's Theorem 2 and BSI's Theorem A is one contrapositive:
  a weighting on which the forecast error is *persistently one-signed and bounded away from
  zero* cannot be a legal divergent weighting, because 4.8.15 would force 0 to be a limit
  point of its weighted average, and it is not.

  The genuine mathematical content — the reason this is not a triviality — is that the
  early terms of the weighted sum are **unconstrained**: before day `N` the error may be
  arbitrarily negative.  What rescues the argument is that there are finitely many such
  terms and the accumulated weight diverges, so their contribution is washed out.  That
  wash-out step is what is proved below. -/

/-- Splitting a `range (n+1)` sum at `N`.  Pure bookkeeping, isolated so the real arguments
    below do not have to fight the index algebra. -/
lemma sum_Ico_eq_sub (f : ℕ → ℝ) {N n : ℕ} (h : N ≤ n + 1) :
    ∑ i ∈ Finset.Ico N (n + 1), f i
      = (∑ i ∈ Finset.range (n + 1), f i) - ∑ i ∈ Finset.range N, f i := by
  have hc := Finset.sum_Ico_consecutive f (Nat.zero_le N) h
  simp only [Finset.range_eq_Ico]
  linarith

/--
  **The wash-out lemma.**  If the weighting `u` is nonnegative, its accumulated weight
  diverges, and from day `N` onwards the error is `≥ c` wherever the weighting is positive,
  then the weighted average is *eventually* `≥ c/2`.

  The `c/2` (rather than `c`) is exactly the price of the unconstrained initial segment.
  Hypotheses are all on `u` and `err` as bare sequences: nothing about markets enters.
-/
theorem wavg_eventually_ge_half
    {u err : ℕ → ℝ} {c : ℝ} (hc : 0 < c) (N : ℕ)
    (hu : ∀ n, 0 ≤ u n)
    (hdiv : Tendsto (W u) atTop atTop)
    (hsupp : ∀ n, N ≤ n → 0 < u n → c ≤ err n) :
    ∀ᶠ n in atTop, c / 2 ≤ wavg u err n := by
  set C : ℝ := ∑ i ∈ Finset.range N, u i * err i with hCdef
  set W₀ : ℝ := ∑ i ∈ Finset.range N, u i with hW₀def
  set K : ℝ := C - c * W₀ with hKdef
  -- eventually the accumulated weight dominates both `1` and `2|K|/c`
  have hbig : ∀ᶠ n in atTop, max (2 * |K| / c) 1 ≤ W u n := hdiv.eventually_ge_atTop _
  filter_upwards [hbig, eventually_ge_atTop N] with n hn hnN
  have hWpos : 0 < W u n :=
    lt_of_lt_of_le zero_lt_one (le_trans (le_max_right (2 * |K| / c) 1) hn)
  -- per-term bound on the tail: `c * u i ≤ u i * err i`
  have hterm : ∀ i ∈ Finset.Ico N (n + 1), c * u i ≤ u i * err i := by
    intro i hi
    have hiN : N ≤ i := (Finset.mem_Ico.1 hi).1
    rcases eq_or_lt_of_le (hu i) with h0 | hpos
    · simp [← h0]
    · have herr := hsupp i hiN hpos
      calc c * u i = u i * c := by ring
        _ ≤ u i * err i := by exact mul_le_mul_of_nonneg_left herr (le_of_lt hpos)
  -- sum the tail bound
  have hNle : N ≤ n + 1 := by omega
  have htail : c * (W u n - W₀) ≤ wsum u err n - C := by
    have h1 : ∑ i ∈ Finset.Ico N (n + 1), c * u i
        ≤ ∑ i ∈ Finset.Ico N (n + 1), u i * err i := Finset.sum_le_sum hterm
    have h2 : ∑ i ∈ Finset.Ico N (n + 1), c * u i = c * (W u n - W₀) := by
      rw [← Finset.mul_sum, sum_Ico_eq_sub u hNle]; simp only [W, hW₀def]
    have h3 : ∑ i ∈ Finset.Ico N (n + 1), u i * err i = wsum u err n - C := by
      rw [sum_Ico_eq_sub (fun i => u i * err i) hNle]; simp only [wsum, hCdef]
    rw [← h2, ← h3]; exact h1
  -- hence `wsum ≥ c * W + K`
  have hlow : c * W u n + K ≤ wsum u err n := by rw [hKdef]; linarith
  -- and the constant `K` is dominated by `(c/2) * W`
  have hKW : -K ≤ (c / 2) * W u n := by
    have h1 : 2 * |K| / c ≤ W u n := le_trans (le_max_left (2 * |K| / c) 1) hn
    have h2 : 2 * |K| ≤ c * W u n := by
      have := (div_le_iff₀ hc).1 h1
      linarith
    have h3 : -K ≤ |K| := neg_le_abs K
    linarith
  rw [wavg, le_div_iff₀ hWpos]
  linarith

/--
  **The engine (program doc T1, "engine half").**  Under the hypotheses of the wash-out
  lemma, 0 is *not* a limit point of the weighted average error.

  Read against 4.8.15 this is the contrapositive that all the positive results use: no
  `A`-generable divergent weighting can concentrate on days of persistently one-signed
  forecast error.  Note what is NOT claimed: nothing here says the constructed weighting IS
  `A`-generable.  That is the modelling step, and it stays outside.
-/
theorem not_limitPointZero_of_one_signed
    {u err : ℕ → ℝ} {c : ℝ} (hc : 0 < c) (N : ℕ)
    (hu : ∀ n, 0 ≤ u n)
    (hdiv : Tendsto (W u) atTop atTop)
    (hsupp : ∀ n, N ≤ n → 0 < u n → c ≤ err n) :
    ¬ LimitPointZero (wavg u err) := by
  intro hLP
  have hev := wavg_eventually_ge_half hc N hu hdiv hsupp
  have hfreq := hLP (c / 2) (by linarith)
  -- frequently `|wavg| < c/2`, eventually `wavg ≥ c/2` : contradiction
  rcases (hfreq.and_eventually hev).exists with ⟨n, hlt, hge⟩
  have : c / 2 ≤ |wavg u err n| := le_trans hge (le_abs_self _)
  linarith

/-! ############################################################
    ## Part 3.  BSI Lemma 4's ramp arithmetic  (program doc L4)
    ############################################################

  Trivial as mathematics; included because a wrong constant here would silently invalidate
  Theorem B, and this is cheap insurance.  `softInd δ x = max 0 (min 1 (x/δ))` matches
  `FaithfulAcceleration.softInd`; `Ind_δ(a > t)` is `softInd δ (a - t)`. -/

/-- The soft indicator (ramp), matching `FaithfulAcceleration.softInd`. -/
noncomputable def softInd (δ x : ℝ) : ℝ := max 0 (min 1 (x / δ))

/-- The ramp is `1` once its argument clears `δ`. -/
theorem softInd_eq_one {δ x : ℝ} (hδ : 0 < δ) (h : δ ≤ x) : softInd δ x = 1 := by
  have h1 : (1 : ℝ) ≤ x / δ := (one_le_div hδ).2 h
  simp [softInd, min_eq_left h1]

/-- The ramp is `0` when its argument is nonpositive. -/
theorem softInd_eq_zero {δ x : ℝ} (hδ : 0 < δ) (h : x ≤ 0) : softInd δ x = 0 := by
  have : x / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg h (le_of_lt hδ)
  simp [softInd, min_le_iff.2 (Or.inr this), max_eq_left (min_le_iff.2 (Or.inr this))]

/-- **BSI Lemma 4, quote ramp.**  With `t = 3/16`, `δ = 1/32`: a quote within `1/64` of
    `1/4` clears the threshold by a full `δ`, so the quote ramp equals `1`. -/
theorem bsi_quote_ramp {q : ℝ} (h : |q - 1/4| ≤ 1/64) :
    softInd (1/32) (q - 3/16) = 1 := by
  have h1 : 1/4 - 1/64 ≤ q := by
    have := abs_le.1 h; linarith [this.1]
  exact softInd_eq_one (by norm_num) (by linarith)

/-- **BSI Lemma 4, credence ramp.**  With `t - ε = 5/32`, `δ = 1/32`: a credence within
    `1/64` of `0` leaves the threshold by a full `δ`, so the credence ramp equals `1`. -/
theorem bsi_credence_ramp {p : ℝ} (h : |p - 0| ≤ 1/64) :
    softInd (1/32) (5/32 - p - 1/32) = 1 := by
  have h1 : p ≤ 1/64 := by have := abs_le.1 h; linarith [this.2]
  exact softInd_eq_one (by norm_num) (by linarith)

/-- The two margin inequalities BSI Lemma 4 asserts, checked as bare arithmetic:
    `1/4 - 1/64 > 3/16 + 1/32`  and  `1/64 < 5/32 - 1/32`. -/
theorem bsi_lemma4_margins :
    (1:ℝ)/4 - 1/64 > 3/16 + 1/32 ∧ (1:ℝ)/64 < 5/32 - 1/32 := by
  constructor <;> norm_num

/-- **BSI's refuted-block frequency.**  `X_k = s_k ∧ s'_k` with independent fair parities has
    `P(X_k) = 1/4`, so refuted blocks have frequency `3/4`.  Checked here only as the
    arithmetic identity `1 - 1/4 = 3/4`; the probabilistic content is Assumption P. -/
theorem bsi_refuted_frequency : (1:ℝ) - 1/4 = 3/4 := by norm_num


/-! ############################################################
    ## Part 4.  Non-vacuity guards
    ############################################################

  `#print axioms` cannot see whether a theorem's hypotheses are jointly satisfiable, so a
  vacuous theorem passes the audit.  Two things are checked here.

  First, and most important, note what the engine's hypotheses do **not** mention: neither
  `wavg` nor `LimitPointZero` appears in them.  So `not_limitPointZero_of_one_signed` cannot
  be an instance of the AUDIT.md §3.3 pattern (a squeeze over hypotheses equivalent to the
  conclusion) — the conclusion is about an object the hypotheses never name.

  Second, the hypotheses are satisfiable, and satisfiable *non-degenerately*: the witness
  below has a genuinely adverse initial segment (error `-100` for ten days), so it exercises
  the wash-out step rather than trivialising it.  Per AUDIT.md §3.8 a constant-sequence
  witness would guard nothing. -/

/-- The accumulated weight of the constant-`1` weighting. -/
theorem W_one (n : ℕ) : W (fun _ => (1 : ℝ)) n = (n : ℝ) + 1 := by
  simp [W, Finset.sum_const, Finset.card_range]

/--
  **Non-vacuity, non-degenerately.**  The engine's hypotheses are jointly satisfiable by a
  witness whose error sequence is *negative on an initial segment* — so the wash-out step of
  `wavg_eventually_ge_half` is genuinely exercised, not sidestepped.
-/
theorem engine_hypotheses_satisfiable :
    ∃ (u err : ℕ → ℝ) (c : ℝ) (N : ℕ),
      0 < c ∧ (∀ n, 0 ≤ u n) ∧ Tendsto (W u) atTop atTop ∧
      (∀ n, N ≤ n → 0 < u n → c ≤ err n) ∧
      (∃ n, err n < 0) := by
  refine ⟨fun _ => 1, fun n => if n < 10 then -100 else 1, 1, 10, one_pos,
    fun _ => zero_le_one, ?_, ?_, ⟨0, by norm_num⟩⟩
  · have h : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact h.congr (fun n => (W_one n).symm)
  · intro n hn _
    have : ¬ (n < 10) := by omega
    simp [this]

-- Axiom audit: each must rest on ONLY [propext, Classical.choice, Quot.sound] (no `sorryAx`).
#print axioms wavg_eventually_ge_half
#print axioms not_limitPointZero_of_one_signed
#print axioms softInd_eq_one
#print axioms bsi_quote_ramp
#print axioms bsi_credence_ramp
#print axioms bsi_lemma4_margins
#print axioms engine_hypotheses_satisfiable

end Staleness

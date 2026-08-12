/-
  StreamlinedSS.lean
  ==================

  The analytic engine of **Theorem SS (streamlined)** —
  `varying-question-lab/theorem-ss-streamlined.md`.

  WHAT THIS FILE IS.  The streamlined assembly has exactly three moving parts: a
  weighted-average calculus (§1), the citations (spec §§3–4 = L2, L3), a bespoke arbitrage (spec §5 = L4),
  the Kelly trader variant (spec §3 remark), the chaining (spec §6), and a threshold corollary (spec §8).
  Everything in it that is *mathematics rather than citation or modelling* is proved here,
  sorry-free.  Following `Staleness.lean` / `CenteredSqueeze.lean`, the market side enters
  only as NAMED HYPOTHESES, named after what they stand for.

  WHAT IS **NOT** MODELLED (the trusted boundary — read this before citing anything here):

  * The two markets, their prices, traders, budgets, the logical induction criterion, and
    every legality/generability question.  Prices are bare sequences `ℕ → ℝ`.  "The criterion
    forbids exploitation" appears only as the hypotheses `hNoExp*` / `NoArb`, which say
    *the trader's accumulated ledger is bounded above* — nothing stronger, and in particular
    never anything conclusion-shaped.
  * The schedule `g` of `route-sparse-schedule` §3 Lemma 1, its evaluation-sparsity, its
    poly-time membership test, and window-disjointness.  These are what make the traders
    below legal and their exposure bounded; here they are simply absent, and their entire
    footprint is the hypothesis that the weighting `w` is a nonnegative `[0,1]` sequence of
    divergent mass.
  * Corrected LI 4.8.16 itself (L2 and L3, spec §§3–4 — the citations).  It enters as
    the hypothesis `hL3 : ApproxW w EAq EHf` in `tower_form`.  Nothing here re-proves it.
  * The publication convention, the decided ledger atoms, `𝒷ℒ𝒞𝒮` membership, expectation
    bundles and mesh independence (LI A.3, E.2).  Their footprint is: the per-instance sure
    profit bound `d i - 2/i` in Part 3, and the bounded mesh sequence `ε` in Part 2.

  WHAT IS PROVED (all sorry-free; `#print axioms` at the end of each part):

  * **Part 1 (§1)** — the `≈_w` calculus: `ApproxW` is symmetric and *transitive for the same
    weighting*, and the **universal donor** lemma (a per-day full limit is an `≈_w` for every
    divergent-mass weighting).  This is the load-bearing bookkeeping of the whole assembly.
  * **Part 2 (spec §3 remark — the trader variant fusing L1+L2)** — the Kelly round-trip engine: the ledger inequality from
    `log(1+x) ≥ x - x²`, mesh absorption, the unboundedness contradiction, and the main
    theorem `kelly_round_trip`: no-exploitation for the trader *and its mirror*, for every
    rational stake `η ∈ (0,1/4)`, forces the weighted average of `Δ` to zero.
  * **Part 3 (spec §5, L4)** — the decided-atom arbitrage: infinitely many `ε`-profitable instances
    accumulate unbounded sure profit; with the mirror, `q i - p i → 0`.
  * **Part 4 (§5)** — the assembly: `tower_form` (two applications of same-`w` additivity),
    the agreement form, `theorem_SS` (the whole chain from the market-level named
    hypotheses), and the finite-mass case.
  * **Part 5 (spec §8)** — the above-threshold Total-Trust arithmetic on the ramp weighting.

  Each part carries an explicit **non-vacuity guard** with a non-degenerate witness, per
  AUDIT.md §3.3/§3.8, including a joint witness for `theorem_SS` itself; and Part 3 shows the
  `NoArb` hypothesis is *refutable* (`noArb_fails_of_const_one`), i.e. has teeth.

  DISCREPANCIES WITH THE PROSE, flagged where they occur (see also the module's report):
  (i) `ledger` proves the constant `4η²Wₙ`, not `η²Wₙ`, and correspondingly the contradiction
  threshold is `5η`, not `3η` (`logWealth_unbounded`); (ii) the mesh bound `|εᵢ| ≤ 1` is
  assumed for *all* `i`, not only eventually; (iii) the donor lemma needs **no** boundedness
  of `xᵢ - yᵢ` (`route-sparse-schedule` §7 Lemma 2 assumes `|εᵢ| ≤ M`) — the head of the split
  is a fixed finite sum.  None of these affects any conclusion.

  No `sorry`; axiom audits (`#print axioms`) at the end of each part.
-/
import Mathlib

open Filter Topology

namespace StreamlinedSS

/-! ############################################################
    ## Part 0.  Vocabulary: weightings and weighted averages
    ############################################################ -/

/-- Accumulated weight through day `n`: `Wₙ = ∑_{i ≤ n} wᵢ`.  (Same convention as
    `Staleness.W`: the sum runs over `range (n+1)`, i.e. `i ≤ n`.) -/
noncomputable def W (w : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range (n + 1), w i

/-- `∑_{i ≤ n} wᵢ·xᵢ`. -/
noncomputable def wsum (w x : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range (n + 1), w i * x i

/-- The `w`-weighted average of `x` through day `n`. -/
noncomputable def wavg (w x : ℕ → ℝ) (n : ℕ) : ℝ := wsum w x n / W w n

/--
  **The common notion of §1**: `x ≈_w y` — the `w`-weighted average of `xᵢ - yᵢ` tends to `0`
  (a *full* limit, which is what makes the three conclusions combine; 4.8.15's limit points
  would not — cf. `Staleness.LimitPointZero`).
-/
def ApproxW (w x y : ℕ → ℝ) : Prop :=
  Tendsto (fun n => wavg w (fun i => x i - y i) n) atTop (𝓝 0)

/-- Splitting a `range (n+1)` sum at `N`.  Pure bookkeeping. -/
theorem sum_split (f : ℕ → ℝ) {N n : ℕ} (h : N ≤ n + 1) :
    ∑ i ∈ Finset.range (n + 1), f i
      = (∑ i ∈ Finset.range N, f i) + ∑ i ∈ Finset.Ico N (n + 1), f i := by
  have hc := Finset.sum_Ico_consecutive f (Nat.zero_le N) h
  simp only [Finset.range_eq_Ico]
  linarith

theorem wsum_sub (w x y : ℕ → ℝ) (n : ℕ) :
    wsum w (fun i => x i - y i) n = wsum w x n - wsum w y n := by
  simp only [wsum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem wsum_neg (w x : ℕ → ℝ) (n : ℕ) :
    wsum w (fun i => -x i) n = - wsum w x n := by
  simp only [wsum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The chaining identity behind same-`w` additivity. -/
theorem wsum_chain (w x y z : ℕ → ℝ) (n : ℕ) :
    wsum w (fun i => x i - z i) n
      = wsum w (fun i => x i - y i) n + wsum w (fun i => y i - z i) n := by
  simp only [wsum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem wavg_chain (w x y z : ℕ → ℝ) (n : ℕ) :
    wavg w (fun i => x i - z i) n
      = wavg w (fun i => x i - y i) n + wavg w (fun i => y i - z i) n := by
  simp only [wavg, ← add_div, wsum_chain w x y z n]

theorem wavg_swap (w x y : ℕ → ℝ) (n : ℕ) :
    wavg w (fun i => y i - x i) n = - wavg w (fun i => x i - y i) n := by
  have h : wsum w (fun i => y i - x i) n = - wsum w (fun i => x i - y i) n := by
    simp only [wsum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [wavg, h, neg_div]

/-! ############################################################
    ## Part 1.  The weighted-average calculus  (spec §1)
    ############################################################

  Two facts carry the whole assembly: same-`w` additivity, and the universal donor rule.
  Both are proved here for bare real sequences. -/

namespace ApproxW
variable {w x y z : ℕ → ℝ}

theorem refl (w x : ℕ → ℝ) : ApproxW w x x := by
  have h : (fun n => wavg w (fun i => x i - x i) n) = fun _ => (0 : ℝ) := by
    funext n; simp [wavg, wsum]
  rw [ApproxW, h]
  exact tendsto_const_nhds

theorem symm (h : ApproxW w x y) : ApproxW w y x := by
  have h' := h.neg
  rw [neg_zero] at h'
  exact h'.congr fun n => (wavg_swap w x y n).symm

/-- **Same-`w` additivity** (spec §1.1).  Valid because all three averages use the *same*
    numeric weights and the same normaliser — this is algebra of real sequences, and it is
    exactly what routing through full limits (rather than 4.8.15's limit points) buys. -/
theorem trans (h1 : ApproxW w x y) (h2 : ApproxW w y z) : ApproxW w x z := by
  have h := h1.add h2
  rw [add_zero] at h
  exact h.congr fun n => (wavg_chain w x y z n).symm

end ApproxW

/--
  **The donor core.**  If `e i → 0`, the weighting is nonnegative and its accumulated mass
  diverges, then the weighted average of `e` tends to `0`.

  Note what is *not* needed: no bound on `e` (the prose's `|εᵢ| ≤ M` in
  `route-sparse-schedule` §7 Lemma 2).  The head of the split is a *fixed finite sum*, hence
  automatically a constant; boundedness only makes the constant explicit.
-/
theorem wavg_tendsto_zero {w e : ℕ → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (W w) atTop atTop) (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (wavg w e) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ρ hρ
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 he (ρ / 4) (by linarith)
  set C : ℝ := ∑ i ∈ Finset.range N, |w i * e i| with hCdef
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hbig : ∀ᶠ n in atTop, max (4 * C / ρ) 1 ≤ W w n := hdiv.eventually_ge_atTop _
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hbig
  refine ⟨max N N₁, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hWbig := hN₁ n (le_trans (le_max_right _ _) hn)
  have hW1 : (1 : ℝ) ≤ W w n := le_trans (le_max_right _ _) hWbig
  have hWpos : 0 < W w n := lt_of_lt_of_le zero_lt_one hW1
  have hCW : C ≤ (ρ / 4) * W w n := by
    have h1 : 4 * C / ρ ≤ W w n := le_trans (le_max_left _ _) hWbig
    rw [div_le_iff₀ hρ] at h1
    linarith
  have hNle : N ≤ n + 1 := by omega
  -- head: a fixed finite sum
  have hhead : |∑ i ∈ Finset.range N, w i * e i| ≤ C := Finset.abs_sum_le_sum_abs _ _
  -- tail: every term is small
  have htail : |∑ i ∈ Finset.Ico N (n + 1), w i * e i| ≤ (ρ / 4) * W w n := by
    have h1 : |∑ i ∈ Finset.Ico N (n + 1), w i * e i|
        ≤ ∑ i ∈ Finset.Ico N (n + 1), |w i * e i| := Finset.abs_sum_le_sum_abs _ _
    have h2 : ∀ i ∈ Finset.Ico N (n + 1), |w i * e i| ≤ (ρ / 4) * w i := by
      intro i hi
      have hiN : N ≤ i := (Finset.mem_Ico.1 hi).1
      have hei := hN i hiN
      rw [Real.dist_eq, sub_zero] at hei
      rw [abs_mul, abs_of_nonneg (hw0 i)]
      nlinarith [hw0 i, abs_nonneg (e i)]
    have h3 := Finset.sum_le_sum h2
    have h5 : ∑ i ∈ Finset.Ico N (n + 1), w i ≤ W w n := by
      rw [W, sum_split w hNle]
      have : 0 ≤ ∑ i ∈ Finset.range N, w i := Finset.sum_nonneg fun i _ => hw0 i
      linarith
    have h4 : ∑ i ∈ Finset.Ico N (n + 1), (ρ / 4) * w i ≤ (ρ / 4) * W w n := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left h5 (by linarith)
    linarith
  have hnum : |wsum w e n| ≤ C + (ρ / 4) * W w n := by
    rw [wsum, sum_split (fun i => w i * e i) hNle]
    exact le_trans (abs_add_le _ _) (add_le_add hhead htail)
  rw [Real.dist_eq, sub_zero, wavg, abs_div, abs_of_pos hWpos, div_lt_iff₀ hWpos]
  nlinarith [mul_pos hρ hWpos]

/--
  **The universal donor rule** (spec §1.2).  A per-day full limit `xᵢ - yᵢ → 0` is an `≈_w`
  for **every** divergent-mass weighting — no parameter matching.  This is how L1 and L4 (spec §§2, 5), which
  is a per-day statement, enters the averaged chain of §5.
-/
theorem approxW_of_tendsto_zero {w x y : ℕ → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (W w) atTop atTop) (h : Tendsto (fun i => x i - y i) atTop (𝓝 0)) :
    ApproxW w x y :=
  wavg_tendsto_zero hw0 hdiv h

-- Axiom audit, Part 1.
#print axioms ApproxW.trans
#print axioms wavg_tendsto_zero
#print axioms approxW_of_tendsto_zero

/-! ############################################################
    ## Part 2.  The Kelly round trip — the spec-§3 remark (trader variant, fuses L1+L2)
    ############################################################

  The self-consistency lemma: a market cannot be Dutch-booked against its own future prices
  when at most one round trip is ever open.  Modelled objects:

  * `w i ∈ [0,1]`   — the weighting (the ramp times the schedule indicator);
  * `Δ i ∈ [-1,1]`  — the round-trip return `𝔼ᴴ_{f(i)}(Xᵢ) - 𝔼ᴴ_i(Xᵢ)`, an abstract sequence;
  * `ε i`           — the bundle mesh error, with `|εᵢ| ≤ 1` and the tail-sup condition (E.2);
  * `logWealth η`   — the Kelly ledger `∑_{i≤n} log(1 + η·wᵢ·(Δᵢ+εᵢ))`.

  NOT modelled: that this ledger is the *worth* of a legal trader, that its worth is bounded
  below by `-1` (single open window), or that the coefficients are producible.  Those are the
  content of (SCHED) and (L⁻), and they are exactly what makes the hypothesis `hNoExp` below
  an instance of the logical-induction criterion rather than an assumption about arithmetic. -/

/--
  `log(1+x) ≥ x - x²` for `|x| ≤ 1/2` — the inequality the spec's §3 ledger line invokes.
  Elementary: an `exp` bound on each side of `0` (`quadratic_le_exp_of_nonneg` for `x ≤ 0`,
  `add_one_le_exp` for `x ≥ 0`), then `Real.le_log_iff_exp_le`.  The crude bounds that suffice
  for `x ≥ 0` are *not* enough for `x ≤ 0` — there the quadratic term of `exp` is needed,
  which is why the two cases are asymmetric.
-/
theorem log_one_add_ge {x : ℝ} (hx : |x| ≤ 1 / 2) : x - x ^ 2 ≤ Real.log (1 + x) := by
  obtain ⟨hx1, hx2⟩ := abs_le.1 hx
  have hpos : (0 : ℝ) < 1 + x := by linarith
  rw [Real.le_log_iff_exp_le hpos]
  have hE : Real.exp (x - x ^ 2) * Real.exp (x ^ 2 - x) = 1 := by
    rw [← Real.exp_add]; simp
  have hEpos : 0 < Real.exp (x ^ 2 - x) := Real.exp_pos _
  have hmul : 1 ≤ (1 + x) * Real.exp (x ^ 2 - x) := by
    rcases le_or_gt x 0 with h | h
    · have hy : (0 : ℝ) ≤ x ^ 2 - x := by nlinarith
      have hq := Real.quadratic_le_exp_of_nonneg hy
      have hx2le : x ^ 2 ≤ 1 / 4 := by nlinarith
      have hfac : (0 : ℝ) ≤ 1 + x - x ^ 2 + x ^ 3 := by nlinarith
      have hQ : 1 ≤ (1 + x) * (1 + (x ^ 2 - x) + (x ^ 2 - x) ^ 2 / 2) := by
        nlinarith [mul_nonneg (sq_nonneg x) hfac]
      have hmono := mul_le_mul_of_nonneg_left hq (le_of_lt hpos)
      linarith
    · have hq := Real.add_one_le_exp (x ^ 2 - x)
      have hQ : 1 ≤ (1 + x) * ((x ^ 2 - x) + 1) := by nlinarith [mul_nonneg (mul_nonneg h.le h.le) h.le]
      have hmono := mul_le_mul_of_nonneg_left hq (le_of_lt hpos)
      linarith
  nlinarith [hE, hEpos, Real.exp_pos (x - x ^ 2)]

/-- The Kelly ledger of the round-trip trader at stake `η`: `∑_{i≤n} log(1 + η·wᵢ·(Δᵢ+εᵢ))`
    (spec §3; the paper's D.4 accounting with the market's own later price in place of
    `Val`). -/
noncomputable def logWealth (η : ℝ) (w Δ ε : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), Real.log (1 + η * w i * (Δ i + ε i))

theorem logWealth_congr {η : ℝ} {w Δ Δ' ε : ℕ → ℝ} (h : ∀ i, Δ i = Δ' i) (n : ℕ) :
    logWealth η w Δ ε n = logWealth η w Δ' ε n := by
  simp only [logWealth]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

/-- The spec's tail-sup mesh condition (LI E.2): `sup_{i≥N}|εᵢ| → 0`. -/
def MeshTailSmall (ε : ℕ → ℝ) : Prop := ∀ ρ : ℝ, 0 < ρ → ∃ N, ∀ i, N ≤ i → |ε i| ≤ ρ

theorem meshTailSmall_iff {ε : ℕ → ℝ} : MeshTailSmall ε ↔ Tendsto ε atTop (𝓝 0) := by
  constructor
  · intro h
    rw [Metric.tendsto_atTop]
    intro ρ hρ
    obtain ⟨N, hN⟩ := h (ρ / 2) (by linarith)
    refine ⟨N, fun n hn => ?_⟩
    have := hN n hn
    rw [Real.dist_eq, sub_zero]
    linarith
  · intro h ρ hρ
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h ρ hρ
    refine ⟨N, fun i hi => ?_⟩
    have := hN i hi
    rw [Real.dist_eq, sub_zero] at this
    linarith

/--
  **(a) The ledger inequality** (spec §3, the displayed `log Wealth ≥ …` line).

  ⚠ DISCREPANCY WITH THE PROSE (harmless).  The prose writes the quadratic penalty as
  `η²Wₙ`.  Term by term, `|ηwᵢ(Δᵢ+εᵢ)| ≤ 2η`, so `x² ≤ 4η²wᵢ` and the honest constant is
  **`4η²Wₙ`**.  (The prose's `η²` is recovered if one also uses that `|εᵢ|` is eventually
  small, at the cost of an additive constant and an `eventually`; the version proved here
  holds for *every* `n` with **no additive constant at all**, which is cleaner and costs
  only a constant that vanishes with `η`.)  Correspondingly the contradiction threshold
  below is `5η` rather than `3η`.  Neither affects the conclusion, which sends `η → 0`.

  ⚠ Also: `|εᵢ| ≤ 1` is assumed for *all* `i`, not merely eventually — needed for the side
  condition `|x| ≤ 1/2` of `log_one_add_ge` at every day.  This is faithful to the intended
  reading (the bundle payoff and the LUV value both lie in `[0,1]`, so their difference lies
  in `[-1,1]`), but it is strictly more than `sup_{i≥N}|εᵢ| → 0` says.
-/
theorem ledger {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 4) {w Δ ε : ℕ → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1) (hΔ : ∀ i, |Δ i| ≤ 1) (hε : ∀ i, |ε i| ≤ 1)
    (n : ℕ) :
    η * wsum w Δ n - η * wsum w (fun i => |ε i|) n - 4 * η ^ 2 * W w n
      ≤ logWealth η w Δ ε n := by
  have hL : η * wsum w Δ n - η * wsum w (fun i => |ε i|) n - 4 * η ^ 2 * W w n
      = ∑ i ∈ Finset.range (n + 1),
          (η * (w i * Δ i) - η * (w i * |ε i|) - 4 * η ^ 2 * w i) := by
    rw [wsum, wsum, W, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  rw [hL, logWealth]
  refine Finset.sum_le_sum fun i _ => ?_
  have hw0i := hw0 i
  have hw1i := hw1 i
  obtain ⟨hΔ1, hΔ2⟩ := abs_le.1 (hΔ i)
  obtain ⟨hε1, hε2⟩ := abs_le.1 (hε i)
  have hde2 : |Δ i + ε i| ≤ 2 := (abs_add_le _ _).trans (by linarith [hΔ i, hε i])
  have habs : |η * w i * (Δ i + ε i)| ≤ 1 / 2 := by
    have h2 : |η * w i * (Δ i + ε i)| = η * w i * |Δ i + ε i| := by
      rw [abs_mul, abs_mul, abs_of_pos hη0, abs_of_nonneg hw0i]
    rw [h2]
    have hstep : η * w i * |Δ i + ε i| ≤ η * 1 * 2 :=
      mul_le_mul (by nlinarith) hde2 (abs_nonneg _) (by nlinarith)
    linarith
  have hlog := log_one_add_ge habs
  have hde : (Δ i + ε i) ^ 2 ≤ 4 := by nlinarith
  have hww : (w i) ^ 2 ≤ w i := by nlinarith
  have hsq : (η * w i * (Δ i + ε i)) ^ 2 ≤ 4 * η ^ 2 * w i := by
    have hrw : (η * w i * (Δ i + ε i)) ^ 2 = η ^ 2 * (w i) ^ 2 * (Δ i + ε i) ^ 2 := by ring
    rw [hrw]
    have h1 : η ^ 2 * (w i) ^ 2 * (Δ i + ε i) ^ 2 ≤ η ^ 2 * (w i) ^ 2 * 4 := by
      nlinarith [sq_nonneg (η * w i), sq_nonneg (Δ i + ε i)]
    have h2 : η ^ 2 * (w i) ^ 2 * 4 ≤ 4 * η ^ 2 * w i := by nlinarith [sq_nonneg η]
    linarith
  have hlin : η * (w i * Δ i) - η * (w i * |ε i|) ≤ η * w i * (Δ i + ε i) := by
    nlinarith [neg_abs_le (ε i), mul_nonneg hη0.le hw0i]
  linarith

/--
  **(b) Mesh absorption** (spec §3, the `η·o(Wₙ)` term).  With divergent mass and the
  tail-sup condition, `∑_{i≤n} wᵢ|εᵢ| = o(Wₙ)`.  A direct instance of the donor core.
-/
theorem mesh_absorb {w ε : ℕ → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hdiv : Tendsto (W w) atTop atTop)
    (hmesh : MeshTailSmall ε) :
    Tendsto (fun n => wsum w (fun i => |ε i|) n / W w n) atTop (𝓝 0) := by
  have h0 : Tendsto (fun i => |ε i|) atTop (𝓝 0) := by
    simpa using (meshTailSmall_iff.1 hmesh).abs
  exact wavg_tendsto_zero hw0 hdiv h0

/--
  **(c) The contradiction shape** (spec §3, "if `limsup ≥ 3η` … `log Wealth → ∞`").  If the
  weighted average of `Δ` is frequently at least `5η`, the Kelly ledger is unbounded above.
  (Threshold `5η`, not `3η`: see the discrepancy note on `ledger`.)  The hypothesis is stated
  in the `∃ᶠ` form rather than as a `limsup` bound: that is what a `limsup` hypothesis
  delivers, it is what the contrapositive in `kelly_round_trip` needs, and it avoids any
  question of whether the `limsup` is attained.
-/
theorem logWealth_unbounded {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 4) {w Δ ε : ℕ → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1) (hΔ : ∀ i, |Δ i| ≤ 1) (hε : ∀ i, |ε i| ≤ 1)
    (hdiv : Tendsto (W w) atTop atTop) (hmesh : MeshTailSmall ε)
    (hfreq : ∃ᶠ n in atTop, 5 * η ≤ wsum w Δ n / W w n) (B : ℝ) :
    ∃ n, B < logWealth η w Δ ε n := by
  have h1 : ∀ᶠ n in atTop, wsum w (fun i => |ε i|) n / W w n ≤ η / 2 := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (mesh_absorb hw0 hdiv hmesh) (η / 2) (by linarith)
    filter_upwards [eventually_ge_atTop N] with n hn
    have h := hN n hn
    rw [Real.dist_eq, sub_zero] at h
    linarith [le_abs_self (wsum w (fun i => |ε i|) n / W w n)]
  have h2 : ∀ᶠ n in atTop, max (2 * (|B| + 1) / η ^ 2) 1 ≤ W w n := hdiv.eventually_ge_atTop _
  obtain ⟨n, hfr, hm, hW⟩ := (hfreq.and_eventually (h1.and h2)).exists
  have hW1 : (1 : ℝ) ≤ W w n := le_trans (le_max_right _ _) hW
  have hWpos : 0 < W w n := lt_of_lt_of_le zero_lt_one hW1
  rw [le_div_iff₀ hWpos] at hfr
  rw [div_le_iff₀ hWpos] at hm
  have hbig : 2 * (|B| + 1) / η ^ 2 ≤ W w n := le_trans (le_max_left _ _) hW
  have hη2 : (0 : ℝ) < η ^ 2 := by positivity
  rw [div_le_iff₀ hη2] at hbig
  have hled := ledger hη0 hη hw0 hw1 hΔ hε n
  have e1 : η * (5 * η * W w n) ≤ η * wsum w Δ n := mul_le_mul_of_nonneg_left hfr hη0.le
  have e2 : η * wsum w (fun i => |ε i|) n ≤ η * (η / 2 * W w n) :=
    mul_le_mul_of_nonneg_left hm hη0.le
  refine ⟨n, ?_⟩
  have hfinal : η ^ 2 / 2 * W w n ≤ logWealth η w Δ ε n := by nlinarith
  have hBlt : B < η ^ 2 / 2 * W w n := by nlinarith [le_abs_self B]
  linarith

/--
  **(d) the trader-variant main theorem** (spec §3 remark).

  NAMED HYPOTHESES (the trusted boundary — this is where the logical induction criterion for
  `P^L` is consumed, via (L⁻) and (SCHED)):

  * `hNoExp`  — for every rational stake `η ∈ (0,1/4)`, the Kelly ledger of the buy-at-`i`,
                sell-at-`f(i)` trader is **bounded above**.  Nothing stronger: no rate, no
                sign information, nothing about `Δ`.
  * `hMirror` — the same for the mirror trader (sell at `i`, repurchase at `f(i)`), whose
                ledger is the one with `Δ` replaced by `-Δ`.

  Rational `η` (not real) is used, matching the prose's legality requirement; the analysis
  needs only arbitrarily small ones.

  CONCLUSION: the two-sided full limit `Wₙ⁻¹ ∑_{i≤n} wᵢΔᵢ → 0`.
-/
theorem kelly_round_trip {w Δ ε : ℕ → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1) (hΔ : ∀ i, |Δ i| ≤ 1) (hε : ∀ i, |ε i| ≤ 1)
    (hdiv : Tendsto (W w) atTop atTop) (hmesh : MeshTailSmall ε)
    (hNoExp : ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < 1 / 4 →
      ∃ B : ℝ, ∀ n, logWealth (q : ℝ) w Δ ε n ≤ B)
    (hMirror : ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < 1 / 4 →
      ∃ B : ℝ, ∀ n, logWealth (q : ℝ) w (fun i => -Δ i) ε n ≤ B) :
    Tendsto (fun n => wsum w Δ n / W w n) atTop (𝓝 0) := by
  have key : ∀ Δ' : ℕ → ℝ, (∀ i, |Δ' i| ≤ 1) →
      (∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < 1 / 4 →
        ∃ B : ℝ, ∀ n, logWealth (q : ℝ) w Δ' ε n ≤ B) →
      ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < 1 / 4 →
        ∀ᶠ n in atTop, wsum w Δ' n / W w n < 5 * (q : ℝ) := by
    intro Δ' hΔ' hno q hq0 hq4
    obtain ⟨B, hB⟩ := hno q hq0 hq4
    by_contra hcon
    rw [not_eventually] at hcon
    simp only [not_lt] at hcon
    obtain ⟨n, hn⟩ := logWealth_unbounded hq0 hq4 hw0 hw1 hΔ' hε hdiv hmesh hcon B
    linarith [hB n]
  rw [Metric.tendsto_atTop]
  intro ρ hρ
  obtain ⟨q, hq0, hqlt⟩ := exists_rat_btwn (show (0 : ℝ) < min (ρ / 5) (1 / 4) by positivity)
  have hq4 : (q : ℝ) < 1 / 4 := lt_of_lt_of_le hqlt (min_le_right _ _)
  have hqρ : 5 * (q : ℝ) < ρ := by
    have := lt_of_lt_of_le hqlt (min_le_left _ _)
    linarith
  have k1 := key Δ hΔ hNoExp q hq0 hq4
  have k2 := key (fun i => -Δ i) (fun i => by rw [abs_neg]; exact hΔ i) hMirror q hq0 hq4
  obtain ⟨N, hN⟩ := eventually_atTop.1 (k1.and k2)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  rw [wsum_neg, neg_div] at h2
  rw [Real.dist_eq, sub_zero, abs_lt]
  constructor <;> linarith

/-! ### Non-vacuity for Part 2

  `#print axioms` cannot see whether hypotheses are jointly satisfiable, so a vacuous theorem
  passes the audit (AUDIT.md §3.3/§3.8).  Two guards.

  First, structurally: `kelly_round_trip`'s hypotheses never mention `wsum w Δ n / W w n`,
  the object its conclusion is about, so it cannot be a restatement of its conclusion.

  Second, they are satisfiable *non-degenerately*: the witness below has `Δ` genuinely
  oscillating (`|Δᵢ| = 1` at every day, alternating sign — so the trader is fully exposed on
  every day and both no-exploitation hypotheses have real content), and the boundedness of
  both ledgers is proved, not assumed.  That witness does take `ε ≡ 0` (proving boundedness
  against a nonzero mesh as well would be a different exercise); `mesh_hypotheses_satisfiable`
  separately exhibits a mesh that is **never** zero, satisfies the tail-sup condition, and is
  absorbed. -/

/-- Alternating partial sums with `c + d ≤ 0` never exceed `max c 0`. -/
theorem alt_sum_le {c d : ℝ} (hcd : c + d ≤ 0) (m : ℕ) :
    (∑ i ∈ Finset.range m, (if Even i then c else d)) ≤ max c 0 := by
  suffices h : ∀ m : ℕ,
      (Even m → (∑ i ∈ Finset.range m, (if Even i then c else d)) ≤ 0) ∧
      (¬ Even m → (∑ i ∈ Finset.range m, (if Even i then c else d)) ≤ c) by
    rcases em (Even m) with hm | hm
    · exact le_trans ((h m).1 hm) (le_max_right _ _)
    · exact le_trans ((h m).2 hm) (le_max_left _ _)
  intro m
  induction m with
  | zero => exact ⟨fun _ => by simp, fun h => absurd (by decide : Even 0) h⟩
  | succ k ih =>
      rw [Finset.sum_range_succ]
      constructor
      · intro hk1
        have hk : ¬ Even k := by
          intro hk; rw [Nat.even_add_one] at hk1; exact hk1 hk
        have hih := ih.2 hk
        rw [if_neg hk]
        linarith
      · intro hk1
        have hk : Even k := by
          by_contra hk
          exact hk1 (Nat.even_add_one.2 hk)
        have hih := ih.1 hk
        rw [if_pos hk]
        linarith

/-- The accumulated mass of the constant-`1` weighting. -/
theorem W_one (n : ℕ) : W (fun _ => (1 : ℝ)) n = (n : ℝ) + 1 := by
  simp [W, Finset.sum_const, Finset.card_range]

theorem W_one_atTop : Tendsto (W (fun _ => (1 : ℝ))) atTop atTop := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  exact h.congr fun n => (W_one n).symm

/--
  **Non-vacuity, non-degenerately.**  `w ≡ 1`, `ε ≡ 0`, `Δᵢ = (-1)ⁱ`: divergent mass, a
  round-trip return of full size `1` on every single day with alternating sign, and BOTH
  no-exploitation hypotheses hold (each ledger is bounded above by `log(1+η)`), for every
  rational stake.  The alternation is what makes them hold: the trader wins and loses in
  turn, and `log(1+η) + log(1-η) = log(1-η²) < 0`.
-/
theorem kelly_hypotheses_satisfiable :
    ∃ w Δ ε : ℕ → ℝ,
      (∀ i, 0 ≤ w i) ∧ (∀ i, w i ≤ 1) ∧ (∀ i, |Δ i| ≤ 1) ∧ (∀ i, |ε i| ≤ 1) ∧
      Tendsto (W w) atTop atTop ∧ MeshTailSmall ε ∧
      (∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < 1 / 4 →
        ∃ B : ℝ, ∀ n, logWealth (q : ℝ) w Δ ε n ≤ B) ∧
      (∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < 1 / 4 →
        ∃ B : ℝ, ∀ n, logWealth (q : ℝ) w (fun i => -Δ i) ε n ≤ B) ∧
      (∀ i, |Δ i| = 1) ∧ (∀ i, Δ i ≠ Δ (i + 1)) := by
  classical
  refine ⟨fun _ => 1, fun i => if Even i then 1 else -1, fun _ => 0,
    fun _ => zero_le_one, fun _ => le_rfl, ?_, fun _ => by norm_num, W_one_atTop,
    (meshTailSmall_iff.2 tendsto_const_nhds), ?_, ?_, ?_, ?_⟩
  · intro i; by_cases h : Even i <;> simp [h]
  -- the buy-side ledger
  · intro q hq0 hq4
    refine ⟨max (Real.log (1 + (q : ℝ))) 0, fun n => ?_⟩
    have hbody : ∀ i ∈ Finset.range (n + 1),
        Real.log (1 + (q : ℝ) * 1 * ((if Even i then (1 : ℝ) else -1) + 0))
          = if Even i then Real.log (1 + (q : ℝ)) else Real.log (1 - (q : ℝ)) := by
      intro i _
      by_cases h : Even i
      · rw [if_pos h, if_pos h]; congr 1; ring
      · rw [if_neg h, if_neg h]; congr 1; ring
    rw [logWealth, Finset.sum_congr rfl hbody]
    refine alt_sum_le ?_ _
    rw [← Real.log_mul (by intro h; linarith [h]) (by intro h; linarith [h])]
    exact Real.log_nonpos (by nlinarith) (by nlinarith)
  -- the mirror ledger
  · intro q hq0 hq4
    refine ⟨max (Real.log (1 - (q : ℝ))) 0, fun n => ?_⟩
    have hbody : ∀ i ∈ Finset.range (n + 1),
        Real.log (1 + (q : ℝ) * 1 * (-(if Even i then (1 : ℝ) else -1) + 0))
          = if Even i then Real.log (1 - (q : ℝ)) else Real.log (1 + (q : ℝ)) := by
      intro i _
      by_cases h : Even i
      · rw [if_pos h, if_pos h]; congr 1; ring
      · rw [if_neg h, if_neg h]; congr 1; ring
    rw [logWealth, Finset.sum_congr rfl hbody]
    refine alt_sum_le ?_ _
    rw [add_comm, ← Real.log_mul (by intro h; linarith [h]) (by intro h; linarith [h])]
    exact Real.log_nonpos (by nlinarith) (by nlinarith)
  -- `|Δ| = 1` everywhere
  · intro i; by_cases h : Even i <;> simp [h]
  -- genuine alternation
  · intro i
    by_cases h : Even i
    · have h' : ¬ Even (i + 1) := by rw [Nat.even_add_one]; simpa using h
      norm_num [h, h']
    · have h' : Even (i + 1) := Nat.even_add_one.2 h
      norm_num [h, h']

/--
  A second guard, for the mesh machinery specifically: the mesh hypotheses are satisfiable
  with a mesh that is *never zero* (`εᵢ = 1/(i+1)`, the spec's `1/i` precision), and the
  absorption conclusion then holds non-trivially.
-/
theorem mesh_hypotheses_satisfiable :
    ∃ ε : ℕ → ℝ, (∀ i, |ε i| ≤ 1) ∧ (∀ i, ε i ≠ 0) ∧ MeshTailSmall ε ∧
      Tendsto (fun n => wsum (fun _ => (1 : ℝ)) (fun i => |ε i|) n
        / W (fun _ => (1 : ℝ)) n) atTop (𝓝 0) := by
  refine ⟨fun i => 1 / ((i : ℝ) + 1), fun i => ?_, fun i => ?_, ?_, ?_⟩
  · have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    rw [abs_of_pos (by positivity)]
    rw [div_le_one hi]
    have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith
  · have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    positivity
  · exact meshTailSmall_iff.2 tendsto_one_div_add_atTop_nhds_zero_nat
  · exact mesh_absorb (fun _ => zero_le_one) W_one_atTop
      (meshTailSmall_iff.2 tendsto_one_div_add_atTop_nhds_zero_nat)

-- Axiom audit, Part 2.
#print axioms log_one_add_ge
#print axioms ledger
#print axioms mesh_absorb
#print axioms logWealth_unbounded
#print axioms kelly_round_trip
#print axioms kelly_hypotheses_satisfiable
#print axioms mesh_hypotheses_satisfiable

/-! ############################################################
    ## Part 3.  L4 — the decided-atom arbitrage  (spec §5)
    ############################################################

  "A market's estimate of a published number is that number."  `d i` is the gap
  `qᵢ - pᵢ` between the published quote `qᵢ = 𝔼ᴬ_i(⌜𝔼ᴴ_{f(i)}(Xᵢ)⌝)` and the market's own
  price `pᵢ = 𝔼ᴴ_i(αᵢ)` for the LUV naming it.

  MODELLING NOTE, kept honest.  "Plausible value" never appears.  Its entire footprint is the
  per-instance bound `sureProfit d i = d i - 2/i`: on a buying day the position is worth at
  least that much *in every day-`i`-plausible world*, because the ledger has decided `αᵢ`'s
  value-atoms to `1/i` and the bundle's mesh is `1/i`.  Whether that bound is warranted is a
  question about ledgers and bundles, not about this file. -/

/-- Per-instance sure profit of the buying trader on day `i` (spec §2). -/
noncomputable def sureProfit (d : ℕ → ℝ) (i : ℕ) : ℝ := d i - 2 / (i : ℝ)

/-- Accumulated sure profit over a finite set of instance-days. -/
noncomputable def accProfit (d : ℕ → ℝ) (D : Finset ℕ) : ℝ := ∑ i ∈ D, sureProfit d i

/--
  **The named no-exploitation hypothesis** for the buy-when-`d ≥ ε` trader family: for each
  rational threshold, the accumulated sure profit over *any* finite set of that trader's
  instance-days is bounded above.  This is the criterion's content and nothing more — in
  particular it says nothing about the sign or the limit of `d`.
-/
def NoArb (d : ℕ → ℝ) : Prop :=
  ∀ r : ℚ, 0 < (r : ℝ) →
    ∃ B : ℝ, ∀ D : Finset ℕ, (∀ i ∈ D, (r : ℝ) ≤ d i) → accProfit d D ≤ B

theorem NoArb.congr {d d' : ℕ → ℝ} (hd : NoArb d) (h : ∀ i, d i = d' i) : NoArb d' := by
  intro r hr
  obtain ⟨B, hB⟩ := hd r hr
  refine ⟨B, fun D hD => ?_⟩
  have hacc : accProfit d' D = accProfit d D := by
    simp only [accProfit, sureProfit]
    exact Finset.sum_congr rfl fun i _ => by rw [h i]
  rw [hacc]
  exact hB D fun i hi => by rw [h i]; exact hD i hi

/-- A gap that is never positive is trivially un-exploitable by the buying trader. -/
theorem noArb_of_nonpos {d : ℕ → ℝ} (h : ∀ i, d i ≤ 0) : NoArb d := by
  intro r hr
  refine ⟨0, fun D hD => ?_⟩
  have hD0 : D = ∅ := by
    by_contra hne
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hne
    linarith [hD i hi, h i]
  rw [hD0, accProfit, Finset.sum_empty]

/--
  **The sequence lemma** (spec §2, "grows by `≥ ε/2` per instance").  If the gap is at least
  `c > 0` infinitely often, the accumulated sure profit over suitable finite instance-sets is
  unbounded: past day `4/c` each such day contributes at least `c/2`, and there are
  arbitrarily many of them.
-/
theorem accProfit_unbounded {d : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hfreq : ∃ᶠ i in atTop, c ≤ d i) (B : ℝ) :
    ∃ D : Finset ℕ, (∀ i ∈ D, c ≤ d i) ∧ B < accProfit d D := by
  obtain ⟨N, hN⟩ := exists_nat_ge (4 / c)
  have hinf : {i : ℕ | c ≤ d i ∧ N ≤ i}.Infinite := by
    rw [← Nat.frequently_atTop_iff_infinite]
    exact hfreq.and_eventually (eventually_ge_atTop N)
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * B / c)
  obtain ⟨D, hDsub, hDcard⟩ := hinf.exists_subset_card_eq k
  have hmem : ∀ i ∈ D, c ≤ d i ∧ N ≤ i := fun i hi => hDsub (Finset.mem_coe.mpr hi)
  refine ⟨D, fun i hi => (hmem i hi).1, ?_⟩
  have hterm : ∀ i ∈ D, c / 2 ≤ sureProfit d i := by
    intro i hi
    obtain ⟨hid, hiN⟩ := hmem i hi
    have hiR : (4 : ℝ) / c ≤ (i : ℝ) := le_trans hN (by exact_mod_cast hiN)
    have hcpos : (0 : ℝ) < 4 / c := by positivity
    have hipos : (0 : ℝ) < (i : ℝ) := lt_of_lt_of_le hcpos hiR
    have h4 : (4 : ℝ) ≤ (i : ℝ) * c := (div_le_iff₀ hc).1 hiR
    have h2 : 2 / (i : ℝ) ≤ c / 2 := by
      rw [div_le_div_iff₀ hipos (by norm_num : (0:ℝ) < 2)]
      linarith
    rw [sureProfit]
    linarith
  have hsum : (D.card : ℝ) * (c / 2) ≤ accProfit d D := by
    rw [accProfit]
    calc (D.card : ℝ) * (c / 2) = ∑ _i ∈ D, c / 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ D, sureProfit d i := Finset.sum_le_sum hterm
  rw [div_lt_iff₀ hc] at hk
  have hcard : (D.card : ℝ) = (k : ℝ) := by exact_mod_cast hDcard
  rw [hcard] at hsum
  nlinarith

/-- From the criterion: the gap is eventually below every positive threshold — the
    `limsup ≤ 0` half of L4. -/
theorem eventually_lt_of_noArb {d : ℕ → ℝ} (h : NoArb d) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ i in atTop, d i < ρ := by
  obtain ⟨r, hr0, hrρ⟩ := exists_rat_btwn hρ
  obtain ⟨B, hB⟩ := h r hr0
  by_contra hcon
  rw [not_eventually] at hcon
  simp only [not_lt] at hcon
  have hfreq : ∃ᶠ i in atTop, (r : ℝ) ≤ d i := hcon.mono fun i hi => le_trans hrρ.le hi
  obtain ⟨D, hD, hlt⟩ := accProfit_unbounded hr0 hfreq B
  linarith [hB D hD]

/--
  **L4** (spec §5): with the mirror trader, the published quote and the market's estimate of
  it agree in the per-day full limit.  This is the readability collapse — the reason the
  Tower form and the agreement form coincide here.
-/
theorem readability_collapse {p q : ℕ → ℝ}
    (hbuy : NoArb (fun i => q i - p i)) (hsell : NoArb (fun i => p i - q i)) :
    Tendsto (fun i => q i - p i) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ρ hρ
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((eventually_lt_of_noArb hbuy hρ).and (eventually_lt_of_noArb hsell hρ))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  have h1' : q n - p n < ρ := h1
  have h2' : p n - q n < ρ := h2
  rw [Real.dist_eq, sub_zero, abs_lt]
  constructor <;> linarith

/-! ### Non-vacuity for Part 3 -/

/-- The no-arbitrage hypothesis has teeth: a persistent unit gap **violates** it.  (So `NoArb`
    is not satisfied by everything, and `readability_collapse` is not vacuous by triviality
    of its hypotheses.) -/
theorem noArb_fails_of_const_one : ¬ NoArb (fun _ => (1 : ℝ)) := by
  intro h
  obtain ⟨B, hB⟩ := h (1 / 2) (by norm_num)
  have hfreq : ∃ᶠ i in atTop, (1 / 2 : ℝ) ≤ (fun _ : ℕ => (1 : ℝ)) i :=
    Filter.Eventually.frequently (Eventually.of_forall fun _ => by norm_num)
  obtain ⟨D, hD, hlt⟩ := accProfit_unbounded (show (0 : ℝ) < 1 / 2 by norm_num) hfreq B
  have := hB D (fun i hi => by push_cast; exact hD i hi)
  linarith

/-- A gap that is positive on **every** day, but vanishing, does satisfy `NoArb`: for each
    threshold only finitely many days qualify, and each contributes at most `1`. -/
theorem noArb_one_div : NoArb (fun i => 1 / ((i : ℝ) + 1)) := by
  intro r hr
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / (r : ℝ))
  refine ⟨(M : ℝ), fun D hD => ?_⟩
  have hsub : D ⊆ Finset.range M := by
    intro i hi
    have h1 : (r : ℝ) ≤ 1 / ((i : ℝ) + 1) := hD i hi
    have hi1 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have h2 : (r : ℝ) * ((i : ℝ) + 1) ≤ 1 := by
      rw [← le_div_iff₀ hi1]; linarith
    have h3 : (i : ℝ) + 1 ≤ 1 / (r : ℝ) := by rw [le_div_iff₀ hr]; linarith
    have h4 : (i : ℝ) < (M : ℝ) := by linarith
    exact Finset.mem_range.2 (by exact_mod_cast h4)
  have hterm : ∀ i ∈ D, sureProfit (fun i => 1 / ((i : ℝ) + 1)) i ≤ 1 := by
    intro i _
    have hi1 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hle : 1 / ((i : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hi1]
      have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith
    have h2i : (0 : ℝ) ≤ 2 / (i : ℝ) := by positivity
    rw [sureProfit]
    linarith
  calc accProfit (fun i => 1 / ((i : ℝ) + 1)) D
      ≤ ∑ _i ∈ D, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = (D.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (M : ℝ) := by
        have := Finset.card_le_card hsub
        rw [Finset.card_range] at this
        exact_mod_cast this

/-- And `readability_collapse`'s hypotheses are satisfiable, with a gap that is **never zero**
    (so the buying days genuinely exist for every small threshold) yet tends to `0`. -/
theorem noArb_satisfiable :
    ∃ p q : ℕ → ℝ, NoArb (fun i => q i - p i) ∧ NoArb (fun i => p i - q i) ∧
      (∀ i, q i - p i ≠ 0) ∧ Tendsto (fun i => q i - p i) atTop (𝓝 0) := by
  refine ⟨fun _ => 0, fun i => 1 / ((i : ℝ) + 1), noArb_one_div.congr (fun i => by ring), ?_,
    ?_, ?_⟩
  · refine noArb_of_nonpos fun i => ?_
    show (0 : ℝ) - 1 / ((i : ℝ) + 1) ≤ 0
    have : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
    linarith
  · intro i
    show 1 / ((i : ℝ) + 1) - 0 ≠ 0
    have hi1 : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
    intro hcon
    rw [sub_zero] at hcon
    linarith
  · have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h

-- Axiom audit, Part 3.
#print axioms accProfit_unbounded
#print axioms eventually_lt_of_noArb
#print axioms readability_collapse
#print axioms noArb_fails_of_const_one
#print axioms noArb_one_div
#print axioms noArb_satisfiable

/-! ############################################################
    ## Part 4.  The assembly  (spec §5)
    ############################################################ -/

/--
  **Theorem SS, Tower form** (spec §5), as an assembly of the three links.

  Sequences (all day-`i` numbers, as bare reals):
  `EHq i` — `𝔼ᴴ_i(⌜𝔼ᴬ_i(⌜𝔼ᴴ_{f(i)}(Xᵢ)⌝)⌝)`;  `EAq i` — the published `𝔼ᴬ_i(⌜𝔼ᴴ_{f(i)}(Xᵢ)⌝)`;
  `EHf i` — `𝔼ᴴ_{f(i)}(Xᵢ)`;  `EH i` — `𝔼ᴴ_i(Xᵢ)`.

  `hL4` is the readability collapse (spec §5), a **per-day** full limit entering through the universal donor rule; `hL3` is the
  A-side citation (corrected 4.8.16, spec §4), assumed here; `hBridge` is the H-side bridge (spec §§2–3: cee + 4.8.16 at H, or Part 2's trader variant).
  conclusion.  The proof is two applications of same-`w` additivity.
-/
theorem tower_form {w EHq EAq EHf EH : ℕ → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (W w) atTop atTop)
    (hL4 : Tendsto (fun i => EHq i - EAq i) atTop (𝓝 0))
    (hL3 : ApproxW w EAq EHf) (hBridge : ApproxW w EHf EH) :
    ApproxW w EHq EH :=
  ((approxW_of_tendsto_zero hw0 hdiv hL4).trans hL3).trans hBridge

/-- The **agreement form** (spec §0): drop the first link. -/
theorem agreement_form {w EAq EHf EH : ℕ → ℝ}
    (hL3 : ApproxW w EAq EHf) (hBridge : ApproxW w EHf EH) : ApproxW w EAq EH :=
  hL3.trans hBridge

/--
  **The whole streamlined assembly, from the market-level named hypotheses.**  L4's arbitrage and the H-side bridge are
  discharged by Parts 3 and 2; L3 is the citation and stays a hypothesis.  This is the
  statement to read as "what the Lean actually delivers for Theorem SS".
-/
theorem theorem_SS {w EHq EAq EHf EH ε : ℕ → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1) (hdiv : Tendsto (W w) atTop atTop)
    -- L4 (spec §5): the decided-atom arbitrage, both sides
    (hL4buy : NoArb (fun i => EAq i - EHq i)) (hL4sell : NoArb (fun i => EHq i - EAq i))
    -- L3 (§4): the single citation — corrected 4.8.16 applied to `A`.  NOT proved here.
    (hL3 : ApproxW w EAq EHf)
    -- the §3-remark trader variant: the Kelly round trip's inputs and its two no-exploitation hypotheses
    (hΔ : ∀ i, |EHf i - EH i| ≤ 1) (hε : ∀ i, |ε i| ≤ 1) (hmesh : MeshTailSmall ε)
    (hNoExp : ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < 1 / 4 →
      ∃ B : ℝ, ∀ n, logWealth (q : ℝ) w (fun i => EHf i - EH i) ε n ≤ B)
    (hMirror : ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < 1 / 4 →
      ∃ B : ℝ, ∀ n, logWealth (q : ℝ) w (fun i => -(EHf i - EH i)) ε n ≤ B) :
    ApproxW w EHq EH := by
  have hL4 : Tendsto (fun i => EHq i - EAq i) atTop (𝓝 0) :=
    readability_collapse hL4sell hL4buy
  have hBridge : ApproxW w EHf EH :=
    kelly_round_trip hw0 hw1 hΔ hε hdiv hmesh hNoExp hMirror
  exact tower_form hw0 hdiv hL4 hL3 hBridge

/--
  **Joint non-vacuity of the whole assembly.**  Every hypothesis of `theorem_SS` is satisfied
  simultaneously by an explicit witness, and non-degenerately where it matters: the trader-variant return
  `EHf - EH` has full size `1` on *every* day (so both Kelly hypotheses have real content),
  and the L4 gap `EHq - EAq` is nonzero on *every* day (so both arbitrage hypotheses do too).
  Only the L3 link is degenerate in the witness (`EAq = EHf`) — L3 is the citation, and
  nothing in this file proves or could falsify it.
-/
theorem theorem_SS_hypotheses_satisfiable :
    ∃ w EHq EAq EHf EH ε : ℕ → ℝ,
      (∀ i, 0 ≤ w i) ∧ (∀ i, w i ≤ 1) ∧ Tendsto (W w) atTop atTop ∧
      NoArb (fun i => EAq i - EHq i) ∧ NoArb (fun i => EHq i - EAq i) ∧
      ApproxW w EAq EHf ∧
      (∀ i, |EHf i - EH i| ≤ 1) ∧ (∀ i, |ε i| ≤ 1) ∧ MeshTailSmall ε ∧
      (∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < 1 / 4 →
        ∃ B : ℝ, ∀ n, logWealth (q : ℝ) w (fun i => EHf i - EH i) ε n ≤ B) ∧
      (∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < 1 / 4 →
        ∃ B : ℝ, ∀ n, logWealth (q : ℝ) w (fun i => -(EHf i - EH i)) ε n ≤ B) ∧
      (∀ i, |EHf i - EH i| = 1) ∧ (∀ i, EHq i - EAq i ≠ 0) := by
  obtain ⟨w, Δ, ε, hw0, hw1, hΔ, hε, hdiv, hmesh, hno, hmir, habs, _halt⟩ :=
    kelly_hypotheses_satisfiable
  refine ⟨w, fun i => Δ i + 1 / ((i : ℝ) + 1), Δ, Δ, fun _ => 0, ε,
    hw0, hw1, hdiv, ?_, ?_, ApproxW.refl w Δ, ?_, hε, hmesh, ?_, ?_, ?_, ?_⟩
  · refine noArb_of_nonpos fun i => ?_
    show Δ i - (Δ i + 1 / ((i : ℝ) + 1)) ≤ 0
    have : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
    linarith
  · exact noArb_one_div.congr fun i => by
      show (1 : ℝ) / ((i : ℝ) + 1) = Δ i + 1 / ((i : ℝ) + 1) - Δ i
      ring
  · intro i; rw [sub_zero]; exact hΔ i
  · intro q hq0 hq4
    obtain ⟨B, hB⟩ := hno q hq0 hq4
    exact ⟨B, fun n => by rw [logWealth_congr (fun i => sub_zero (Δ i)) n]; exact hB n⟩
  · intro q hq0 hq4
    obtain ⟨B, hB⟩ := hmir q hq0 hq4
    refine ⟨B, fun n => ?_⟩
    rw [logWealth_congr (Δ' := fun i => -Δ i) (fun i => by rw [sub_zero]) n]
    exact hB n
  · intro i; rw [sub_zero]; exact habs i
  · intro i
    show Δ i + 1 / ((i : ℝ) + 1) - Δ i ≠ 0
    have hi1 : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
    intro hcon
    have hval : Δ i + 1 / ((i : ℝ) + 1) - Δ i = 1 / ((i : ℝ) + 1) := by ring
    rw [hval] at hcon
    linarith

/-! ### The finite-mass case (spec §0, §5; `route-sparse-schedule` §7 case (b)) -/

/-- If the accumulated mass stays bounded then the weights vanish. -/
theorem finite_mass_tendsto_zero {w : ℕ → ℝ} (hw0 : ∀ i, 0 ≤ w i) {B : ℝ}
    (hB : ∀ n, W w n ≤ B) : Tendsto w atTop (𝓝 0) := by
  have hB0 : (0 : ℝ) ≤ B :=
    le_trans (Finset.sum_nonneg fun i _ => hw0 i) (hB 0)
  have hsum : Summable w := by
    refine summable_of_sum_range_le (c := B) hw0 (fun n => ?_)
    cases n with
    | zero => simpa using hB0
    | succ k => exact hB k
  exact hsum.tendsto_atTop_zero

/-- …and then every per-day product with a bounded sequence vanishes along with them: in the
    finite-mass case both sides of each displayed inequality vanish, so nothing is lost. -/
theorem finite_mass_mul {w b : ℕ → ℝ} {M B : ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hB : ∀ n, W w n ≤ B) (hb : ∀ i, |b i| ≤ M) :
    Tendsto (fun i => w i * b i) atTop (𝓝 0) := by
  have hw := finite_mass_tendsto_zero hw0 hB
  have hM : Tendsto (fun i => M * w i) atTop (𝓝 0) := by
    simpa using hw.const_mul M
  refine squeeze_zero_norm (fun i => ?_) hM
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 i)]
  nlinarith [abs_nonneg (b i), hw0 i, hb i]

-- Axiom audit, Part 4.
#print axioms tower_form
#print axioms agreement_form
#print axioms theorem_SS
#print axioms theorem_SS_hypotheses_satisfiable
#print axioms finite_mass_tendsto_zero
#print axioms finite_mass_mul

/-! ############################################################
    ## Part 5.  Scheduled soft Total Trust, above-threshold  (spec §7)
    ############################################################

  The ramp weighting `wᵢ = Ind_δ(quoteᵢ > t)` has no false positives, so on its support the
  quote clears `t`; combined with the agreement form this pushes the human's `w`-average
  above `t - o(1)`.  Ramp conventions match `CenteredSqueeze.indUp` / `Staleness.softInd`. -/

/-- `Ind_δ(x > t)`: `0` for `x ≤ t`, linear ramp on `[t, t+δ]`, `1` for `x ≥ t + δ`. -/
noncomputable def indUp (δ t x : ℝ) : ℝ := max 0 (min 1 ((x - t) / δ))

theorem indUp_nonneg (δ t x : ℝ) : 0 ≤ indUp δ t x := le_max_left _ _

theorem indUp_le_one (δ t x : ℝ) : indUp δ t x ≤ 1 := max_le zero_le_one (min_le_left _ _)

/-- **No false positives**: a positive ramp weight certifies that the threshold is cleared. -/
theorem indUp_pos_imp {δ t x : ℝ} (hδ : 0 < δ) (h : 0 < indUp δ t x) : t < x := by
  by_contra hc
  push_neg at hc
  have h1 : (x - t) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  have h2 : min 1 ((x - t) / δ) ≤ 0 := le_trans (min_le_right _ _) h1
  have : indUp δ t x = 0 := max_eq_left h2
  linarith

/-- **The pointwise above-threshold inequality on the support** (spec §7): `wᵢ·qᵢ ≥ t·wᵢ`
    for the ramp weighting, with no case analysis left to the reader. -/
theorem ramp_pointwise {δ t x : ℝ} (hδ : 0 < δ) : t * indUp δ t x ≤ indUp δ t x * x := by
  rcases eq_or_lt_of_le (indUp_nonneg δ t x) with h | h
  · simp [← h]
  · nlinarith [indUp_pos_imp hδ h]

/--
  **Soft Total Trust, above-threshold inequality, scheduled and averaged** (spec §7).  From
  the agreement form `q ≈_w h` plus the pointwise support inequality: the `w`-weighted
  average of the human's credence is eventually at least `t - ρ`, for every `ρ > 0` — i.e.
  `liminf ≥ t`.
-/
theorem total_trust_above {w q h : ℕ → ℝ} {t : ℝ}
    (hdiv : Tendsto (W w) atTop atTop)
    (hsupp : ∀ i, t * w i ≤ w i * q i)
    (hagree : ApproxW w q h) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ n in atTop, t - ρ ≤ wavg w h n := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hagree ρ hρ
  have hbig : ∀ᶠ n in atTop, (1 : ℝ) ≤ W w n := hdiv.eventually_ge_atTop 1
  filter_upwards [hbig, eventually_ge_atTop N] with n h1 h2
  have hWn : 0 < W w n := lt_of_lt_of_le zero_lt_one h1
  have hqn : t ≤ wavg w q n := by
    rw [wavg, le_div_iff₀ hWn, wsum, W, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hsupp i
  have hsmall : |wavg w (fun i => q i - h i) n| < ρ := by
    have := hN n h2
    rwa [Real.dist_eq, sub_zero] at this
  have hchain : wavg w h n = wavg w q n - wavg w (fun i => q i - h i) n := by
    rw [wavg, wavg, wavg, wsum_sub, ← sub_div]
    congr 1
    ring
  have := (abs_lt.1 hsmall).2
  linarith

/-- The same with the ramp weighting supplied concretely, so the support inequality is
    discharged rather than assumed. -/
theorem total_trust_above_ramp {δ t : ℝ} (hδ : 0 < δ) (q h : ℕ → ℝ)
    (hdiv : Tendsto (W fun i => indUp δ t (q i)) atTop atTop)
    (hagree : ApproxW (fun i => indUp δ t (q i)) q h) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ n in atTop, t - ρ ≤ wavg (fun i => indUp δ t (q i)) h n :=
  total_trust_above hdiv (fun _ => ramp_pointwise hδ) hagree hρ

-- Axiom audit, Part 5.
#print axioms indUp_pos_imp
#print axioms ramp_pointwise
#print axioms total_trust_above
#print axioms total_trust_above_ramp

end StreamlinedSS

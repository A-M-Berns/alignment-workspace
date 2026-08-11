/-
# Signed versus magnitude prediction of the principal — round `2026-08-11-phase-ii-prediction`

Provisional namespace and provisional names (`AGENTS.md` §6): every declaration below is
proposed, not canonical.

## The question

`A` prices grade contracts settling at `F(n) > t(n)`. Writing `p` for `A`'s time-`t(n)`
price and `Y` for the principal's realized grade, does the no-Dutch-book criterion force

* **(S)** the signed average of `Y − p` to vanish, or
* **(M)** the average of `|Y − p|` to vanish?

## What this file establishes

**Layer 1 — the structural separation.** A trader's net worth is, by `Strategy.value`, an
*affine* function of the world's payout vector. So:

* the signed error sum **is literally a trader's net worth** (`unitTrader_netWorth_eq`);
* the magnitude error sum **is not, and cannot be** — at any market that is the mean of a
  finite mixture of p.c. worlds, every trader's mixture-averaged net worth is exactly `0`
  (`CoherentMixture.netWorth_eq_zero`), hence no trader's net worth dominates a magnitude
  sum that grows at a positive rate in every world of the mixture
  (`magnitude_not_traderPayoff`).

Mixture-coherence is the elementary form of `LogicalInduction.lic_limitCoherence`
(`.lake/packages/agentFoundations/LogicalInduction/Properties/LimitCoherence.lean:777`),
which says a logical inductor's **limiting** prices are the sentence probabilities of an
actual measure on p.c. worlds. That citation is about `n → ∞` at a fixed sentence and does
**not** by itself govern the diagonal quantity `P (t n) (φ n)` that (S) and (M) are about;
it is offered as evidence that mixture-coherence is the shape a market's prices take, not
as a derivation. The diagonal is handled separately, in Layer 3.

**Layer 2 — the exact residual, and the cheapest instrument.** For binary contracts the
squared error is not merely bounded by a trader payoff, it *equals* one plus a
price-determined offset:

```
∑_{i≤n} (Y_i − p_i)²  =  sharpTrader.netWorth  +  ∑_{i≤n} p_i(1 − p_i)
```

(`sharpTrader_netWorth_eq`). The trader is the existing grade contract held with the
coefficient `1 − 2p`, which is a real element of the pinned feature grammar of rank `n`
(`sharpEF`, `sharpEF_rank`) — no new contract family, no new settlement assumption. What it
buys is exactly this: magnitude control **conditional on the market's own sharpness**
(`squaredError_bdd_of_sharpness_bdd`), the residual `∑ p(1−p)` being a quantity `A` can
evaluate at time `t(n)` and no trader can touch.

**Layer 3 — the forced failure.** Where the principal is unpredictable to `A`, (M) does not
merely fail to be forced: it is forced to fail, at an explicit rate
(`magnitude_ge_of_price_limit`). The hypothesis `hconv` is verbatim the conclusion of
`LogicalInduction.lic_learning_pseudorandom_frequency_of_historicalVerifiers`
(`.lake/packages/agentFoundations/LogicalInduction/Properties/Pseudorandomness.lean:3013`),
and `hbin` is verbatim the conclusion of `LogicalInduction.TheoryTruth.isBoolean`
(`.lake/packages/agentFoundations/LogicalInduction/Properties/Calibration.lean:3439`). The
composition is not performed here because that import chain is not built in this checkout
and building it is a broad rebuild; see this round's `REPORT.md` §7.

## What remains named

`squaredError_bdd_of_sharpness_bdd` carries `EfficientlyComputable (sharpTrader φ)` — the
emission certificate — undischarged, exactly as `FaithfulAcceleration.weight_not_divergent`
carries its own. It is therefore `unverified-nonvacuous` and not promotable. Every other
theorem in this file is hypothesis-complete and ships a witness.
-/
import LogicalInduction.Framework.Criterion
import LogicalInduction.Framework.Asymptotics
import Mathlib.Algebra.BigOperators.Fin

namespace Workspace.Deference.Contrib.MagnitudePrediction

open Filter Topology LogicalInduction

/-! ## Layer 1 — a trader's payoff is affine in the payout vector -/

/-- A finite mixture of p.c. worlds whose sentence-wise mean is the market's price, on every
day and at every sentence. The elementary form of the limit-coherence conclusion. -/
structure CoherentMixture (P : History) where
  /-- How many worlds carry mass. -/
  card : ℕ
  /-- The mass on each world. -/
  weight : Fin card → ℝ
  /-- The worlds. -/
  world : Fin card → PCWorld
  weight_nonneg : ∀ j, 0 ≤ weight j
  weight_sum : ∑ j, weight j = 1
  /-- Prices are the mixture's expectations. -/
  prices : ∀ (n : ℕ) (φ : Sentence), P n φ = ∑ j, weight j * (world j).payout φ

namespace CoherentMixture

variable {P : History}

theorem exists_weight_pos (M : CoherentMixture P) : ∃ j, 0 < M.weight j := by
  by_contra h
  push Not at h
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin M.card)), M.weight j = 0 :=
    fun j _ => le_antisymm (h j) (M.weight_nonneg j)
  have hsum := M.weight_sum
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero] at hsum
  exact absurd hsum (by norm_num)

/-- The mixture average of one strategy's trade list is zero: the price is the mean payout,
so every coefficient multiplies a mean-zero quantity. -/
theorem mixture_trades_eq_zero (M : CoherentMixture P) (n : ℕ) :
    ∀ l : List (EF × Sentence),
      ∑ j, M.weight j *
          (l.map (fun q => q.1.denote P * ((M.world j).payout q.2 - P n q.2))).sum = 0 := by
  intro l
  induction l with
  | nil => simp
  | cons q rest ih =>
      have hsplit : ∀ j : Fin M.card,
          M.weight j *
              (((q :: rest).map
                (fun r => r.1.denote P * ((M.world j).payout r.2 - P n r.2))).sum)
            = M.weight j * (q.1.denote P * ((M.world j).payout q.2 - P n q.2))
              + M.weight j *
                  ((rest.map
                    (fun r => r.1.denote P * ((M.world j).payout r.2 - P n r.2))).sum) := by
        intro j
        simp only [List.map_cons, List.sum_cons]
        ring
      rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib, ih, add_zero]
      have hexp : ∀ j : Fin M.card,
          M.weight j * (q.1.denote P * ((M.world j).payout q.2 - P n q.2))
            = q.1.denote P * (M.weight j * (M.world j).payout q.2)
              - M.weight j * (q.1.denote P * P n q.2) := by
        intro j
        ring
      rw [Finset.sum_congr rfl (fun j _ => hexp j), Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul, M.weight_sum, ← M.prices n q.2]
      ring

/-- **The obstruction.** At a mixture-coherent market every trader's net worth averages to
exactly zero over the mixture, on every day. No hypothesis on the trader: this is what it
means for the criterion's payoff form to be linear in settlements. -/
theorem netWorth_eq_zero (M : CoherentMixture P) (Tr : Trader) (n : ℕ) :
    ∑ j, M.weight j * Tr.netWorth P (M.world j) n = 0 := by
  have hswap : ∑ j, M.weight j * Tr.netWorth P (M.world j) n
      = ∑ j, ∑ i ∈ Finset.range (n + 1),
          M.weight j * (Tr.strat i).value P (M.world j).payout :=
    Finset.sum_congr rfl (fun j _ => by simp only [Trader.netWorth, Finset.mul_sum])
  rw [hswap, Finset.sum_comm]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  simpa [Strategy.value] using M.mixture_trades_eq_zero i (Tr.strat i).trades

/-- No trader is uniformly profitable across the mixture's support. -/
theorem exists_netWorth_nonpos (M : CoherentMixture P) (Tr : Trader) (n : ℕ) :
    ∃ j, Tr.netWorth P (M.world j) n ≤ 0 := by
  by_contra h
  push Not at h
  obtain ⟨j₀, hj₀⟩ := M.exists_weight_pos
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin M.card)),
      0 ≤ M.weight j * Tr.netWorth P (M.world j) n :=
    fun j _ => mul_nonneg (M.weight_nonneg j) (le_of_lt (h j))
  have hpos : 0 < M.weight j₀ * Tr.netWorth P (M.world j₀) n := mul_pos hj₀ (h j₀)
  have hlt : (0 : ℝ) < ∑ j, M.weight j * Tr.netWorth P (M.world j) n :=
    Finset.sum_pos' hterm ⟨j₀, Finset.mem_univ j₀, hpos⟩
  rw [M.netWorth_eq_zero Tr n] at hlt
  exact lt_irrefl _ hlt

end CoherentMixture

/-! ## The two error functionals, as they sit in the market model -/

/-- `(S)`'s partial sum: the signed grade-model error accumulated through day `n`. -/
noncomputable def signedSum (P : History) (φ : ℕ → Sentence) (v : PCWorld) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (v.payout (φ i) - P i (φ i))

/-- `(M)`'s partial sum: the magnitude grade-model error accumulated through day `n`. -/
noncomputable def magnitudeSum (P : History) (φ : ℕ → Sentence) (v : PCWorld) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), |v.payout (φ i) - P i (φ i)|

/-- **Magnitude is not a trader payoff.** If the magnitude error grows at a positive rate in
every world of a coherent mixture, then no trader's net worth dominates it up to an additive
constant. Contrast `unitTrader_netWorth_eq`, where the signed sum *is* a net worth on the
nose. This is the exact sense in which one scalar contract per `(n, π)` gives a trader no
instrument whose payoff is `|error|`. -/
theorem magnitude_not_traderPayoff {P : History} (M : CoherentMixture P) (φ : ℕ → Sentence)
    (c : ℝ) (hc : 0 < c)
    (hrate : ∀ (j : Fin M.card) (n : ℕ), c * ((n : ℝ) + 1) ≤ magnitudeSum P φ (M.world j) n)
    (Tr : Trader) (K : ℝ) :
    ¬ (∀ (j : Fin M.card) (n : ℕ),
        magnitudeSum P φ (M.world j) n ≤ Tr.netWorth P (M.world j) n + K) := by
  intro hdom
  obtain ⟨n, hn⟩ := exists_nat_gt (K / c)
  obtain ⟨j, hj⟩ := M.exists_netWorth_nonpos Tr n
  have h1 : c * ((n : ℝ) + 1) ≤ Tr.netWorth P (M.world j) n + K := (hrate j n).trans (hdom j n)
  have h2 : K < c * (n : ℝ) := by
    rw [div_lt_iff₀ hc] at hn
    linarith
  have h3 : c * ((n : ℝ) + 1) = c * (n : ℝ) + c := by ring
  linarith

/-! ### The signed side: the criterion does have an instrument -/

/-- The unit trader: buy one share of the day's grade contract and hold it to settlement. -/
def unitTrader (φ : ℕ → Sentence) : Trader where
  strat n :=
    { trades := [(EF.const 1, φ n)]
      rank_le := by
        intro q hq
        simp only [List.mem_singleton] at hq
        subst hq
        simp }

/-- **The signed error sum is literally a trader's net worth.** No approximation, no
remainder term. -/
theorem unitTrader_netWorth_eq (φ : ℕ → Sentence) (P : History) (v : PCWorld) (n : ℕ) :
    (unitTrader φ).netWorth P v n = signedSum P φ v n := by
  simp [Trader.netWorth, Strategy.value, unitTrader, signedSum]

/-- The criterion, applied to the unit trader: a market cannot let the signed grade error
accumulate one-sidedly. This is the forcing of `(S)` in its Dutch-book form — bounded below
and unbounded above is precisely `def:exploitation`. -/
theorem signed_bddAbove_of_bddBelow (φ : ℕ → Sentence) (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (hEC : EfficientlyComputable (unitTrader φ))
    (hbelow : BddBelow ((unitTrader φ).plausibleAssessments P DP)) :
    BddAbove ((unitTrader φ).plausibleAssessments P DP) := by
  by_contra habove
  exact hLI.noExploit _ hEC ⟨hbelow, habove⟩

/-! ## Layer 2 — the residual identity and the cheapest instrument -/

/-- The coefficient `1 − 2p`, as an actual element of the pinned feature grammar. It reads
only the day-`n` price of the contract it is applied to, so it is legal on day `n`. -/
def sharpEF (φ : Sentence) (n : ℕ) : EF :=
  .add (.const 1) (.mul (.const (-2)) (.price φ n))

@[simp] theorem sharpEF_rank (φ : Sentence) (n : ℕ) : (sharpEF φ n).rank = n := by
  simp [sharpEF]

theorem sharpEF_denote (φ : Sentence) (n : ℕ) (P : History) :
    (sharpEF φ n).denote P = 1 - 2 * P n φ := by
  simp only [sharpEF, EF.denote_add, EF.denote_mul, EF.denote_const, EF.denote_price,
    Pi.add_apply, Pi.mul_apply]
  push_cast
  ring

/-- The trader that holds each day's grade contract with coefficient `1 − 2p`. -/
def sharpTrader (φ : ℕ → Sentence) : Trader where
  strat n :=
    { trades := [(sharpEF (φ n) n, φ n)]
      rank_le := by
        intro q hq
        simp only [List.mem_singleton] at hq
        subst hq
        simp }

/-- A `{0,1}` payout is its own square. -/
theorem payout_mul_self (v : PCWorld) (φ : Sentence) :
    v.payout φ * v.payout φ = v.payout φ := by
  unfold PCWorld.payout
  by_cases h : v.Holds φ <;> simp [h]

/-- **The residual identity, pointwise.** For a binary settlement the squared error splits
into a part linear in the settlement — with a coefficient the market can compute from its
own price — and a part determined by the price alone. This is why binary contracts admit a
magnitude instrument and rational-valued grade contracts do not. -/
theorem sq_error_split (y p : ℝ) (hy : y * y = y) :
    (y - p) ^ 2 = (1 - 2 * p) * (y - p) + p * (1 - p) := by
  have hexp : (y - p) ^ 2 = y * y - 2 * p * y + p * p := by ring
  rw [hexp, hy]
  ring

/-- Without binarity the split degrades to a one-sided bound, in the useful direction, for
any settlement in `[0,1]`. This is what survives the propositional substitution: a
threshold/LUV rendering of a rational grade keeps the instrument, at the cost of the exact
identity. -/
theorem sq_error_le_of_mem_Icc (y p : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    (y - p) ^ 2 ≤ (1 - 2 * p) * (y - p) + p * (1 - p) := by
  nlinarith [mul_nonneg h0 (sub_nonneg.2 h1)]

/-- The market's own indecision through day `n`: the part of the squared error no trader can
reach. `A` can evaluate this at time `t(n)` from its own prices. -/
noncomputable def sharpnessDeficit (P : History) (φ : ℕ → Sentence) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), P i (φ i) * (1 - P i (φ i))

/-- The squared grade error through day `n`. -/
noncomputable def squaredSum (P : History) (φ : ℕ → Sentence) (v : PCWorld) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (v.payout (φ i) - P i (φ i)) ^ 2

/-- **The accounting identity for the sharp trader.** Squared grade error equals the sharp
trader's net worth plus the market's own indecision — exactly, in every world, on every day.
The analogue of `FaithfulAcceleration.accelTrader_netWorth_eq`, and the quantitative form of
the answer to the round's question: the criterion can drive the first summand and has no
instrument for the second. -/
theorem sharpTrader_netWorth_eq (φ : ℕ → Sentence) (P : History) (v : PCWorld) (n : ℕ) :
    squaredSum P φ v n = (sharpTrader φ).netWorth P v n + sharpnessDeficit P φ n := by
  have hval : ∀ i : ℕ, ((sharpTrader φ).strat i).value P v.payout
      = (1 - 2 * P i (φ i)) * (v.payout (φ i) - P i (φ i)) := by
    intro i
    simp [sharpTrader, Strategy.value, sharpEF_denote]
  simp only [squaredSum, sharpnessDeficit, Trader.netWorth]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.range (n + 1)) => hval i),
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => sq_error_split _ _ (payout_mul_self v (φ i)))

/-- **What the cheapest instrument buys.** Under the criterion, with the sharp trader
efficiently computable, a market whose indecision stays bounded has bounded squared grade
error on every plausible world — hence vanishing magnitude error in Cesàro average. The
hypothesis `hsharp` is about `A`'s own prices only; it is checkable at `t(n)` and is *not*
implied by the criterion (see `coin_sharpness`).

Kind `C` (composition). Provenance: the identity and the bounds are (a), derived above;
`hEC` is (c), the disclosed `dd:fuel` efficiency model of the pinned dependency,
undischarged here. **No inhabitation witness ships with this statement**, so it is
`unverified-nonvacuous` in the sense of `AGENTS.md`'s Lean regime. -/
theorem squaredError_bdd_of_sharpness_bdd (φ : ℕ → Sentence) (P : History)
    (DP : DeductiveProcess) [hLI : IsLogicalInductor P DP]
    (hEC : EfficientlyComputable (sharpTrader φ))
    (hsharp : ∃ M, ∀ n, sharpnessDeficit P φ n ≤ M) :
    ∃ M', ∀ (n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) → squaredSum P φ v n ≤ M' := by
  obtain ⟨M, hM⟩ := hsharp
  have hsq_nonneg : ∀ (n : ℕ) (v : PCWorld), 0 ≤ squaredSum P φ v n :=
    fun n v => Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hbelow : BddBelow ((sharpTrader φ).plausibleAssessments P DP) := by
    refine ⟨-M, ?_⟩
    rintro x ⟨n, v, -, rfl⟩
    have hid := sharpTrader_netWorth_eq φ P v n
    have h1 := hsq_nonneg n v
    have h2 := hM n
    linarith
  have habove : BddAbove ((sharpTrader φ).plausibleAssessments P DP) := by
    by_contra h
    exact hLI.noExploit _ hEC ⟨hbelow, h⟩
  obtain ⟨M₂, hM₂⟩ := habove
  refine ⟨M₂ + M, fun n v hv => ?_⟩
  have hmem : (sharpTrader φ).netWorth P v n ∈ (sharpTrader φ).plausibleAssessments P DP :=
    ⟨n, v, hv, rfl⟩
  have hid := sharpTrader_netWorth_eq φ P v n
  have h1 := hM₂ hmem
  have h2 := hM n
  linarith

/-! ## Layer 3 — where the principal is unpredictable, (M) is forced to fail -/

/-- **The forced failure.** If the market's price on the grade contract converges to a
frequency `p` while the settlement is binary, the magnitude error is eventually at least
`min p (1 − p)`, up to any `ε`. At `0 < p < 1` this is bounded away from zero, so `(M)`
fails — not merely unproved, but false.

`hconv` is verbatim the conclusion of
`LogicalInduction.lic_learning_pseudorandom_frequency_of_historicalVerifiers`, and `hbin`
verbatim that of `LogicalInduction.TheoryTruth.isBoolean`. -/
theorem magnitude_ge_of_price_limit (P : History) (φ : ℕ → Sentence) (truth : ℕ → ℝ)
    (p : ℝ) (hbin : ∀ n, truth n = 0 ∨ truth n = 1)
    (hconv : (fun n => P n (φ n)) ≈ₙ (fun _ => p)) :
    ∀ ε > 0, ∀ᶠ n in atTop, min p (1 - p) - ε ≤ |truth n - P n (φ n)| := by
  intro ε hε
  filter_upwards [asympEq_iff_eventuallyWithin.1 hconv ε hε] with n hn
  have hclose : |P n (φ n) - p| ≤ ε := hn
  have hsplit : min p (1 - p) ≤ |truth n - p| := by
    rcases hbin n with h | h <;> rw [h]
    · rw [zero_sub, abs_neg]
      exact le_trans (min_le_left _ _) (le_abs_self p)
    · exact le_trans (min_le_right _ _) (le_abs_self (1 - p))
  have htri : |truth n - p| ≤ |truth n - P n (φ n)| + |P n (φ n) - p| :=
    abs_sub_le (truth n) (P n (φ n)) p
  linarith

/-! ## Witnesses -/

/-- The two-point mixture: world `0` makes every atom true, world `1` makes every atom
false. -/
def coinWorld (j : Fin 2) : PCWorld := fun _ => j = 0

/-- The market that prices every sentence at the two-point mixture's mean. Exact rationals
throughout: on an atom the price is `1/2`. -/
noncomputable def coinPrices : History :=
  fun _ φ => (1 / 2) * (coinWorld 0).payout φ + (1 / 2) * (coinWorld 1).payout φ

/-- The two-point mixture is coherent for `coinPrices` by construction. -/
noncomputable def coinMixture : CoherentMixture coinPrices where
  card := 2
  weight := fun _ => 1 / 2
  world := coinWorld
  weight_nonneg := by intro j; norm_num
  weight_sum := by rw [Fin.sum_univ_two]; norm_num
  prices := by
    intro n φ
    rw [Fin.sum_univ_two]
    rfl

theorem coinWorld_zero_payout (i : ℕ) :
    (coinWorld 0).payout (LO.Propositional.Formula.atom i) = 1 := by
  simp [coinWorld, PCWorld.payout, PCWorld.Holds, LO.Propositional.Formula.Boolean.val]

theorem coinWorld_ne_zero_payout {j : Fin 2} (hj : j ≠ 0) (i : ℕ) :
    (coinWorld j).payout (LO.Propositional.Formula.atom i) = 0 := by
  simp [coinWorld, PCWorld.payout, PCWorld.Holds, LO.Propositional.Formula.Boolean.val, hj]

theorem coinWorld_one_payout (i : ℕ) :
    (coinWorld 1).payout (LO.Propositional.Formula.atom i) = 0 :=
  coinWorld_ne_zero_payout (by decide) i

/-- Both worlds of the mixture are exactly `1/2` away from the price, in opposite
directions: the separating instance's per-decision magnitude error. -/
theorem coinWorld_abs_error (j : Fin 2) (i : ℕ) :
    |(coinWorld j).payout (LO.Propositional.Formula.atom i) - 1 / 2| = 1 / 2 := by
  by_cases h : j = 0
  · rw [h, coinWorld_zero_payout]
    norm_num
  · rw [coinWorld_ne_zero_payout h]
    norm_num

theorem coinPrices_atom (n i : ℕ) :
    coinPrices n (LO.Propositional.Formula.atom i) = 1 / 2 := by
  rw [coinPrices, coinWorld_zero_payout, coinWorld_one_payout]
  norm_num

/-- The separating instance's magnitude error: exactly `1/2` per decision, in **both** worlds
of the mixture. -/
theorem coin_magnitudeSum (j : Fin 2) (n : ℕ) :
    magnitudeSum coinPrices (fun i => LO.Propositional.Formula.atom i) (coinWorld j) n
      = (1 / 2) * ((n : ℝ) + 1) := by
  have hterm : ∀ i ∈ Finset.range (n + 1),
      |(coinWorld j).payout (LO.Propositional.Formula.atom i)
        - coinPrices i (LO.Propositional.Formula.atom i)| = 1 / 2 := by
    intro i _
    rw [coinPrices_atom]
    exact coinWorld_abs_error j i
  rw [magnitudeSum, Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  push_cast
  ring

/-- **The separating witness.** In the two-point market the signed error averages to zero
over the mixture for *every* trader (`CoherentMixture.netWorth_eq_zero`), while the magnitude
error is `1/2` per decision in every world of the support — and no trader's net worth
dominates it. `(S)` holds exactly and `(M)` fails maximally, against the whole admissible
trader class at once. -/
theorem coin_separates (Tr : Trader) (K : ℝ) :
    ¬ (∀ (j : Fin coinMixture.card) (n : ℕ),
        magnitudeSum coinPrices (fun i => LO.Propositional.Formula.atom i)
            (coinMixture.world j) n
          ≤ Tr.netWorth coinPrices (coinMixture.world j) n + K) := by
  refine magnitude_not_traderPayoff coinMixture _ (1 / 2) (by norm_num) ?_ Tr K
  intro j n
  exact le_of_eq (coin_magnitudeSum j n).symm

/-- The sharpness hypothesis of `squaredError_bdd_of_sharpness_bdd` is exactly what fails at
the separating instance: the deficit grows linearly. Necessity witness for that hypothesis —
it cannot be dropped. -/
theorem coin_sharpness (n : ℕ) :
    sharpnessDeficit coinPrices (fun i => LO.Propositional.Formula.atom i) n
      = (1 / 4) * ((n : ℝ) + 1) := by
  have hterm : ∀ i ∈ Finset.range (n + 1),
      coinPrices i (LO.Propositional.Formula.atom i)
        * (1 - coinPrices i (LO.Propositional.Formula.atom i)) = 1 / 4 := by
    intro i _
    rw [coinPrices_atom]
    norm_num
  rw [sharpnessDeficit, Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  push_cast
  ring

/-- The sharpness hypothesis is satisfiable: a market that prices the grade contracts
decisively has zero deficit. Inhabitation witness for `hsharp`. -/
theorem sharpnessDeficit_zero_witness (φ : ℕ → Sentence) :
    ∃ M, ∀ n, sharpnessDeficit (fun _ _ => 0) φ n ≤ M := by
  refine ⟨0, fun n => ?_⟩
  simp [sharpnessDeficit]

/-- The signed and magnitude functionals differ already at a single decision: the separating
instance in its smallest form. -/
theorem signed_ne_magnitude :
    signedSum coinPrices (fun i => LO.Propositional.Formula.atom i) (coinWorld 1) 0
      ≠ magnitudeSum coinPrices (fun i => LO.Propositional.Formula.atom i) (coinWorld 1) 0 := by
  rw [signedSum, magnitudeSum, Finset.sum_range_one, Finset.sum_range_one,
    coinWorld_one_payout, coinPrices_atom]
  norm_num

#print axioms CoherentMixture.exists_weight_pos
#print axioms CoherentMixture.mixture_trades_eq_zero
#print axioms CoherentMixture.netWorth_eq_zero
#print axioms CoherentMixture.exists_netWorth_nonpos
#print axioms magnitude_not_traderPayoff
#print axioms unitTrader_netWorth_eq
#print axioms signed_bddAbove_of_bddBelow
#print axioms sharpEF_rank
#print axioms sharpEF_denote
#print axioms payout_mul_self
#print axioms sq_error_split
#print axioms sq_error_le_of_mem_Icc
#print axioms sharpTrader_netWorth_eq
#print axioms squaredError_bdd_of_sharpness_bdd
#print axioms magnitude_ge_of_price_limit
#print axioms coinMixture
#print axioms coin_magnitudeSum
#print axioms coin_separates
#print axioms coin_sharpness
#print axioms sharpnessDeficit_zero_witness
#print axioms signed_ne_magnitude

end Workspace.Deference.Contrib.MagnitudePrediction

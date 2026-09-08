# Weighted BRIA: variable horizons, the wealth algebra, and the existence theorem

Labels as in `FIXED_HORIZON.md`.  Lean: `lean/Workspace/Deference/Contrib/ContinuationBRIA.lean`.
Names provisional: *weighted BRIA*, *capital adequacy*, *non-dominance*, *attention
bound*.

## 1. Why a weight

Block `k` has duration `m_k ≥ 1`, block average `G_k ∈ [0,1]`, `S_K := Σ_{k≤K} m_k`,
`M_K := max_{k≤K} m_k`.  Primitive-time performance is `Σ_{k≤K} m_k G_k / S_K` (LEAN
`sum_blocks_eq_weighted`); the paper's criterion controls `(1/K) Σ_{k≤K} G_k`.

**They differ** (FIX `test_macro_and_primitive_averages_differ`): blocks in pairs
`(m, α^e − G) = (1, −δ), (j, +δ)` have macro overestimation 0 and primitive-time
overestimation tending to `δ`.

**Bounded horizons reduce** (FIX `test_bounded_horizons_reduce_to_the_unweighted_criterion`).
If `m_k ≤ M`, run the paper's criterion on `r'_k := m_k G_k / M ∈ [0,1]` with promises
`e'_k := m_k e_k / M`; then `Σ m_k (e_k − G_k) = M Σ (e'_k − r'_k)`, and since `S_K ≥ K`,
ordinary no overestimation on `(e', r')` gives weighted no overestimation on `(e, G)`.
Records rescale the same way.  So for bounded, and in particular for discounted, block
returns — where the natural weight is the discount mass `Σ_{j<m} γ^j ≤ 1/(1−γ)` — the
weighted criterion is the ordinary criterion on rescaled data and nothing new is needed.

**Unbounded horizons do not reduce.**  Normalising by the running maximum
`r'_k := m_k G_k / M_k` gives `Σ_k M_k (e'_k − r'_k)` for the weighted sum, and Abel
summation against a nondecreasing `M_k` turns an `o(K)` bound on the partial sums of
`e' − r'` into nothing better than `O(K M_K)`, because the partial sums are bounded below
only by `−k`.  The countermodel above is the instance.  So with `sup m_k = ∞` the weighted
criterion is a different criterion.

**The primitive is a weight.**  Everything below is stated for a positive round weight
`w_k`; duration `w_k = m_k` is the instance for average block return.  Q1 of the
dispatch: yes, `m_k` is the right weight for a per-time average, because
`Σ m_k G_k = Σ_t r_t`.

## 2. The weighted criterion

For a schedule `(w_k)` and an estimating agent `α = (α^c_k, α^e_k)` over blocks:

```
no overestimation      limsup_K  Σ_{k≤K} w_k (α^e_k − G_k) / Σ_{k≤K} w_k  ≤ 0
record of h on M       ℓ^h_K := Σ_{k ∈ M, k ≤ K} w_k (G_k − h^e_k)
coverage               B_h finite, or  ℓ^h_K → −∞ along K ∈ B_h
weighted BRIA          no overestimation and coverage of every h ∈ H
```

**What ports** (DERIVED, each a one-line change to the paper's proof):

- Lemma 6: dropping tests at rounds with `h^e_k = 0` lowers the record by
  `Σ w_k G_k ≥ 0`, so it still diverges.
- Theorem 3 → **weighted guaranteed option**: a hypothesis whose promise is a sound lower
  bound on its tests has `ℓ ≥ 0` on every test set, hence is rejected finitely often,
  hence `α^e_k ≥ L_k` for `k ≥ k_0`, hence
  `Σ_{k≤K} w_k (G_k − L_k) ≥ −o(S_K) − S_{k_0}`.  This needs only `S_K → ∞`.
- Theorem 2: the diagonal hypothesis is the same.
- Theorem 4 does **not** port as stated: it needs a notion of randomness for a
  block-weighted average along an e.c. selection, and the vMWC definition is
  unweighted.  OPEN, and not needed by this round.

Coverage's divergence clause is a design choice fixed by what the construction delivers;
the weighted guaranteed-option theorem uses only "record `≥ 0` ⇒ finitely many
rejections", which any coverage clause of this shape gives.

## 3. The construction

Hypotheses `h_i`, `i ∈ ℕ`, active from the first round with positive allowance.  Wealth
`W_i` in total-reward units, initially 0.  At round `k` with weight `w_k`:

```
per-unit bid       b_{i,k} = min( e_{i,k},  W_i(k) / w_k )
winner             i*_k ∈ argmax_i b_{i,k}          (ties arbitrary)
learner            α^c_k = q_{i*,k},   α^e_k = b*_k := b_{i*,k}
winner's update    W_{i*}(k+1) = W_{i*}(k) + A(k, i*) + w_k (G_k − b*_k)
others             W_i(k+1)    = W_i(k) + A(k, i)
```

A hypothesis can promise per unit only what it can pay in total: its liability on a full
test is `w_k e_{i,k}`, and the wealth bound caps that at `W_i(k)`.

**Wealth identity** (LEAN `Auction.wealth_sum_eq`; FIX `test_wealth_identity_and_nonnegativity`
under both charges):

```
Σ_i W_i(K)  =  𝒜_K  +  Σ_{k<K} w_k (G_k − α^e_k),       𝒜_K := Σ_{k<K} Σ_i A(k, i).
```

**Nonnegativity** (LEAN `Auction.wealth_nonneg`): under the wealth bound every `W_i(k) ≥ 0`.

**No overestimation** (LEAN `Auction.overestimation_le_allowance`):
`Σ_{k<K} w_k (α^e_k − G_k) ≤ 𝒜_K`.  So weighted no overestimation follows from

```
(ii)   𝒜_K / S_K → 0.
```
Since `S_K ≥ K`, the paper's `𝒜_K / K → 0` implies (ii): growing horizons make the
subsidy condition *easier* per macro-round.

**Coverage.**  Let `h_i` outpromise `α` at the infinite set `B_i`; test set
`M_i` := rounds `i` wins.

- (A′) `M_i` is infinite.  If `i` never wins after `K_0`, then for `k ≥ K_0`
  `W_i(k) ≥ Σ_{K_0 ≤ n < k} A(n, i) = A_i(k) − A_i(K_0)` (LEAN `wealth_ge_of_no_win`,
  with `A_i(k) := Σ_{n<k} A(n,i)`).  If for some `k ∈ B_i`, `k ≥ K_0`, this is at least
  `w_k e_{i,k}`, then `b_{i,k} = e_{i,k} > b*_k`, contradicting `b*_k` maximal.  So it
  suffices that

  ```
  (i′)   A_i(k) − w_k → ∞      for every i        (capital adequacy)
  ```
  because then eventually `A_i(k) − A_i(K_0) ≥ w_k ≥ w_k e_{i,k}`.
- (C′) The record diverges.  Paid ≤ promised gives `ℓ^i_K ≤ W_i(K) − A_i(K)` (LEAN
  `record_le`), and at a rejection `K ∈ B_i` the wealth-bounded bid is below the promise,
  so `W_i(K) ≤ w_K b*_K < w_K e_{i,K} ≤ w_K`; hence
  `ℓ^i_K < w_K − A_i(K)` (LEAN `record_lt_of_rejected'`), which tends to `−∞` along
  `B_i` by (i′).

(i′) replaces the paper's `Σ_n A(n,i) = ∞`, which is (i′) at `w ≡ 1`.  The dispatch's
candidate `A_i(K)/m_K → ∞` is stronger than needed: `m_k = k`, `A_i(k) = k + √k` has
ratio `→ 1` and difference `→ ∞`, and the proof uses only the difference.  Its
`Σ_i A_i(K) / S_K → 0` is exactly (ii).

**Computability** (DERIVED, as in the paper's part 4): with `A(k, ·)` supported on
`i ≤ s(k)`, `s` computable nondecreasing, only `s(k)` hypotheses are simulated at round
`k`, each once; the winner's controller runs for `m_k` gated steps.  Cost per macro-round
`O(s(k) g(k) + m_k · (controller + gate))`.

**Weighted BRIA construction theorem** (DERIVED from the above, the algebra LEAN):
*for any schedule `(w_k)` and allowance `A` with finite e.c. support satisfying (i′) and
(ii), the auction is a weighted BRIA covering every c.e. class of e.c. continuation
hypotheses, computable with finitely many active hypotheses per round.*

## 4. Capital adequacy and the existence theorem

**Fixture J** (FIX `test_weighted.J_Starvation`).  `m_k = k` with the paper's
`A(k,i) = k^{-1} i^{-2}`: `A_2(400) ≈ 1.6` against `m_400 = 400`; a hypothesis promising 1
on a controller paying 0 is rejected at every one of 400 rounds and tested at none.  The
auction is not a weighted BRIA for that schedule: (i′) fails.  With the *replenishing*
allowance `a_k = (M_k − M_{k−1}) + 1/k` on the active support, the same hypothesis is tested
at rounds `1, 2, 4, 12, 44, 171` — whenever its wealth passes `(3/4) m_k`, i.e. at rounds
spaced by a factor tending to 4 — its record is below `−200`, and the weighted
overestimation is below `1/100`.

The replenishing allowance is the general witness.  With `M_k` the running maximum of the
schedule, `a_k := (M_k − M_{k−1}) + 1/k` for `i ≤ s(k)`:

- (i′): `A_i(k) = M_k − M_{k_i − 1} + Σ_{n=k_i}^{k} 1/n ≥ m_k − M_{k_i−1} + ln(k/k_i)`, so
  `A_i(k) − m_k → ∞` for each `i` (`k_i` its activation round).
- (ii): `𝒜_K ≤ s(K) Σ_{k≤K} a_k = s(K) (M_K + H_K)`, `H_K ≤ 1 + ln K`.  With
  `ρ_K := (M_K + 1 + ln K)/S_K` and any computable nonincreasing `ρ̄ ≥ ρ` with
  `ρ̄_K → 0`, take `s(K) := ⌊ρ̄_K^{−1/2}⌋`: nondecreasing, unbounded, and
  `𝒜_K / S_K ≤ ρ̄_K^{1/2} → 0`.

So (i′) and (ii) are jointly satisfiable exactly when `ρ_K → 0`, i.e. when
`M_K / S_K → 0` (`(1 + ln K)/S_K → 0` is automatic from `S_K ≥ K`).  Since a dominant
block at `K` is dominant at its own index (`m_j = M_K ≥ c S_K ≥ c S_j`), `M_K/S_K → 0`
iff `m_K/S_K → 0`.  Provisional name: **non-dominance** — no single block is a fixed
fraction of all primitive time so far.

**Existence Theorem for weighted BRIA** (DERIVED; the obstruction's inequality LEAN
`dominant_block_lower_bound`, its fixture `test_weighted.Dominance`).

*(a) If `m_K / S_K → 0`, the auction with the replenishing allowance and the support
`s` above is a computable weighted BRIA covering every c.e. class of e.c. continuation
hypotheses.*

*(b) If `limsup m_K / S_K = c > 0`, there is a block environment with two e.c.
hypotheses such that no estimating agent is a weighted BRIA covering both.*

Proof of (b).  Environment: controller `good` pays `γ ∈ (0,1)` per step, controller
`liar` pays 0; no other reward exceeds `γ`.  Let `D := {K : m_K ≥ (c/2) S_K}`, infinite
and computable from the schedule.  Hypotheses: `h_g = (good, γ)` at every round;
`h_l = (liar, 1)` at `K ∈ D`, `(liar, 0)` elsewhere.  Suppose `α` covers both.
`h_g`'s record is 0 on every test set, so it is rejected finitely often: `α^e_k ≥ γ` for
`k ≥ k_0`, hence `α^e_k − G_k ≥ 0` there.  If `α^e_K = 1` at infinitely many `K ∈ D`,
then at each such `K ≥ k_0` the cumulative weighted overestimation is at least
`m_K (1 − γ) − S_{k_0} ≥ (c/2)(1−γ) S_K − S_{k_0}`, violating no overestimation.  So
`α^e_K < 1 = h^e_{l,K}` at all but finitely many `K ∈ D`: `B_l` is infinite, `h_l`'s
record must diverge, and tests at rounds where it promises 0 contribute `≥ 0`, so it is
tested at infinitely many `K ∈ D`.  At such a test with `K ≥ k_0`, `G_K = 0` and
`α^e_K ≥ γ`, so by `dominant_block_lower_bound` (with `ε = 0`) the cumulative weighted
overestimation is at least `(c/2) γ S_K − S_{k_0}`.  Its ratio to `S_K` exceeds `cγ/4`
infinitely often.  Contradiction.  ∎

Part (b) is about the *criterion*: under a dominant schedule the obligation to test an
outpromising hypothesis and the obligation not to overestimate on primitive time cannot
both be met, because one test costs a fixed fraction of all time so far.  It is not a
defect of the auction.

**Fixture K** (FIX `test_weighted.K_FeasibleSchedule`): `m_k = ⌊log₂ k⌋ + 1`,
`A(k, i) = i^{-2} / ⌊√k⌋` for `i ≤ k`.
(i′): `A_i(k) ≥ i^{-2} (2√(k+1) − 2 − i)` since `Σ_{n≤k} n^{-1/2} ≥ 2(√(k+1) − 1)` and
the first `i` terms are at most `i`; minus `m_k ≤ log₂ k + 1` this tends to `∞`.
(ii): `Σ_{n≤K} 1/⌊√n⌋ = Σ_{j<J} (2j+1)/j + (K − J² + 1)/J ≤ 2√K + ln K + 3` with
`J = ⌊√K⌋`, so `𝒜_K ≤ ζ(2)(2√K + ln K + 3)`, while `S_K ≥ log₂ K! ≥ K log₂ K − 1.45 K`;
the ratio tends to 0, and `m_K / S_K → 0`.  Checked at `K = 10², …, 10⁵`: `A_1(K) − m_K`
increases (`13.9, 55.3, 189.2, 619.8`), the bounds hold, the ratio over the first 50
hypotheses falls below `1/1000`.  The dispatch's family `m_k ≍ log k`,
`A(k,i) ≍ i^{-2} k^{-a}` works for every `a ∈ [0, 1)` by the same integrals (`a = 0` is
constant allowance and is affordable because `S_K ≍ K log K`); the paper's `a = 1` fails
(i′) for this schedule, since `A_i(k) ≍ i^{-2} ln k < log₂ k`.

## 5. Long tests as liability: the attention bound

From `W_i(K) = A_i(K) + chargedRecord_i(K) ≥ 0` (LEAN `wealth_eq`, `wealth_nonneg`):

```
Σ_{k ∈ M_i, k<K} w_k (b_k − G_k)  ≤  A_i(K).
```

The weighted shortfall a hypothesis inflicts on its tests is bounded by the allowance it
was given.  If some competitor always bids at least `β > 0` (a sound hypothesis with a
guaranteed floor), `i` wins only with `b_k ≥ β`, so for a hypothesis whose tests return 0
the primitive time it consumes is `Σ_{M_i} m_k ≤ A_i(K)/β`.  Under (ii) that is `o(S_K)`:
**wealth is a claim on execution time**, and a long lease costs proportionally more of it.
This is an identity of the construction, not an analogy; the liability register of the
workspace is not invoked.

The same bound is what makes the one-step auction myopic on a renewable investment
(`FIXED_HORIZON.md` §4A): an investing action is a refuted one-step test, and the
refuted tests of every hypothesis together consume at most `𝒜_K/β` rounds.

**Fixture I — monopoly under the unweighted charge** (FIX `test_weighted.I_Monopoly`).
Apply the paper's construction verbatim to a variable-length block sequence (weight 1 per
block, bid `min(e, W)`).  Schedule `m_k = 2^{⌊√k⌋}` (non-dominant: `M_K/S_K ≍ 1/(4√K)`),
allowance `≍ i^{-2} k^{-1/4}`.  A hypothesis that promises 0 until round `K_0`, then 1 for
`n = ⌊A(K_0)⌋` rounds, is e.c., is tested exactly `n` times, has record `−n`, and the
macro-BRIA's overestimation over `K_0 + n` rounds is at most `n/(K_0+n) ≍ K_0^{-1/4}`.  It
is a covered, refuted hypothesis of a perfectly good macro-BRIA.  It holds a share of
primitive time that is `0.31, 0.375, 0.43` at `K_0 = 100, 256, 625` and tends to 1: the
`n ≍ K_0^{3/4}` blocks it buys after `K_0` each have length at least `2^{⌊√K_0⌋}`, while
`S_{K_0} ≍ 4√K_0 · 2^{√K_0}`, so the bought window dominates everything before it.  Under
the duration charge the same hypothesis cannot afford one block and never wins, the
weighted overestimation is `≤ 0`, and the primitive-time average is the good controller's
`3/4`.

So the unweighted macro-BRIA satisfies the paper's criterion on the macro sequence and
has primitive-time average reward tending to 0 along a subsequence in an environment
where a sound hypothesis guarantees `3/4`.  The weighted charge is necessary, and (i′) is
the price of it.

## 6. Answers to the dispatch's §8 questions

1. `m_k` is the weight for a per-time average (§1).
2. Discounted returns have bounded weight and reduce to the ordinary criterion (§1).
3. Yes, the primitive is a positive weight; the theorems are stated for `w_k`.
4. Lemma 6, Theorems 1–3 port with the algebra above; Theorem 1's two allowance
   conditions become (i′) and (ii).
5. Theorem 4 does not port as stated (OPEN); the paper's allowance fails (i′) as soon as
   `w_k` is unbounded, however slowly it grows.
6. Weighted coverage gives the weighted guaranteed-option theorem (§2), which is
   `GROWING_HORIZON.md`'s theorem.
7. Time expansion reduces the bounded case and fails the unbounded one (§1); the weighted
   criterion is the simpler formulation there, because the alternative does not exist.

## 7. What is not established

- Any rate: (i′) and (ii) are asymptotic; the geometric spacing of tests in fixture J is
  the auction's, not a bound.
- Sharpness of (i′) per hypothesis; the sharp condition is the schedule-level
  non-dominance, and (i′) is a sufficient uniform condition.
- A weighted Theorem 4.
- That the learner may *choose* `m_k` adaptively; the schedule here is declared in
  advance and known to hypotheses.  Hypothesis-requested lease lengths are a
  combinatorial-auction question the paper's footnote gestures at and this round does not
  touch.

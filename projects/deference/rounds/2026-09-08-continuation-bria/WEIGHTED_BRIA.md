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
Records rescale the same way.  So for uniformly bounded *finite test weights* the
weighted criterion is the ordinary criterion on rescaled data and nothing new is needed.
A **finite truncated discounted lease** is such a case: its weight `Σ_{j<m_k} γ^j ≤ 1/(1−γ)`
is bounded (FIX `test_pressure.K_DiscountedFiniteBlock`).  An **infinite-horizon
discounted return** is not: its value is not available at any finite test time — two
environments agreeing on the first `m` rewards differ in discounted value by `γ^m Δ`
(FIX `test_pressure.L_InfiniteDiscountedClaim`) — so a promise about it cannot be scored
by a lease without a further settlement mechanism.  That mechanism is not supplied here:
**OPEN**.  The first version's remark that discounted returns "reduce" is corrected to
the finite truncated case only.

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
- Theorem 3 → **weighted guaranteed option**, under the record condition (BR): a
  hypothesis whose weighted record on `α`'s test set for it is bounded below,
  `inf_K ℓ^h_K > −∞`, cannot have that record diverge to `−∞` along its rejection
  rounds, hence is rejected finitely often, hence `α^e_k ≥ L_k` for `k ≥ k_0`, hence
  `Σ_{k≤K} w_k (G_k − L_k) ≥ −o(S_K) − S_{k_0}`.  A sound promise (`ℓ ≥ 0` on every test
  set) is the special case; finite total tested overpromise is the intermediate one
  (`GROWING_HORIZON.md` §1; LEAN `record_ge_neg_overpromise`).  This needs only
  `S_K → ∞`.
- Theorem 2: the diagonal hypothesis is the same.
- Theorem 4 does **not** port as stated: it needs a notion of randomness for a
  block-weighted average along an e.c. selection, and the vMWC definition is
  unweighted.  OPEN, and not needed by this round.

Coverage's divergence clause is a design choice fixed by what the construction delivers;
the weighted guaranteed-option theorem uses only "record `≥ 0` ⇒ finitely many
rejections", which any coverage clause of this shape gives.

## 3. The construction — *[timing aligned in the fourth pass]*

Hypotheses `h_i`, `i ∈ ℕ`, activated lazily (§4.1).  Wealth in total-reward units.  One
weighted macro-round `k`, in order:

```
1. the block length m_k (weight w_k) is revealed;        nothing about m_{k+1}, … is known
2. hypotheses i ≤ s*(k) are active (the frontier, §4.1)
3. the OPENING subsidy A(k, i) is credited to i ≤ s(k):   B_k(i) := W_k(i) + A(k, i)
4. each active hypothesis emits (q_{i,k}, τ_{i,k}, e_{i,k})
5. per-unit bid            b_{i,k} = min( e_{i,k},  B_k(i) / w_k )
6. winner                  i*_k ∈ argmax_i b_{i,k}   (ties: lowest active index);  α^e_k = b*_k
7. the winner's (q, τ) is executed through the gate for the block
8. the block average G_k is observed
9. settlement              W_{k+1}(i*) = B_k(i*) + w_k (G_k − b*_k);   W_{k+1}(i) = B_k(i) otherwise
```

`W_k(i)` is the wealth carried into round `k` (`W_1 = 0`); `B_k(i)` is the **opening
capital** the bid is bounded by.  A hypothesis can promise per unit only what it can pay
in total: its liability on a full test is `w_k e_{i,k}`, capped at `B_k(i)`.

**Timing.**  The source paper credits `A(t, i)` *after* round `t` (`w_{t+1} = w_t + A(t,i)
+ payoff`; bids at `t` from `w_t`).  The weighted construction credits the round's subsidy
at its *opening*, before bids.  As a sequence of bids and settlements the two are the same
auction: opening timing with rule `A` is settlement timing with the shifted rule
`A'(k) = A(k+1)` and initial endowment `A(1, i)` (FIX `test_timing.Reindexing`, exact
equality of every bid, winner and estimate).  What differs is *what the rule may read*:
under settlement timing the subsidy that funds block `k` was fixed before `m_k` was
revealed; under opening timing it may depend on `m_k`.  For unit weights this is
immaterial; for the prefix rule of §4.1, whose `ΔM_k` term exists to capitalise
hypotheses against the block just revealed, it is the whole point (§4.1, layer III′).
So: **the fixed-horizon reduction is the paper's criterion verbatim; the weighted auction
is the paper's auction with the allowance credited at the opening of the round it funds —
a small modification, forced by online variable liabilities, and stated as such.**  The
first three passes wrote "the paper's construction" for the Python auction, which was
already opening-timed; that phrase is withdrawn for the weighted construction.

**Wealth identity** (LEAN `Auction.wealth_sum_eq`, timing-independent; FIX
`test_wealth_identity_and_nonnegativity`):

```
Σ_i W_{K+1}(i)  =  𝒜_K  +  Σ_{k≤K} w_k (G_k − α^e_k),       𝒜_K := Σ_{k≤K} Σ_i A(k, i).
```

**Nonnegativity** (LEAN `Auction.wealth_nonneg_opening`): under the opening-capital bound
every `W_k(i) ≥ 0`, hence every `B_k(i) ≥ 0`.

**No overestimation** (LEAN `Auction.overestimation_le_allowance_opening`):
`Σ_{k≤K} w_k (α^e_k − G_k) ≤ 𝒜_K`, with `𝒜_K` the subsidy *through round `K` inclusive* —
the current round's opening subsidy is counted.  So weighted no overestimation follows
from

```
(ii)   𝒜_K / S_K → 0.
```
Since `S_K ≥ K`, the paper's `𝒜_K / K → 0` implies (ii).

**Coverage.**  Let `h_i` outpromise `α` at the infinite set `B_i`; test set
`M_i` := rounds `i` wins.  Write `A_i(K) := Σ_{k≤K} A(k,i)`, allowance through `K`
inclusive.

- (A′) `M_i` is infinite.  If `i` never wins after `K_0`, then
  `B_k(i) = W_{K_0+1}(i) + Σ_{K_0 < n ≤ k} A(n, i) ≥ A_i(k) − A_i(K_0)` (LEAN
  `wealth_ge_of_no_win`, timing-independent).  If for some `k ∈ B_i`, `k > K_0`, this is at
  least `w_k e_{i,k}`, then `b_{i,k} = e_{i,k} > b*_k`, contradicting `b*_k` maximal.  So it
  suffices that `A_i(k) − w_k → ∞`.
- (C′) The record diverges.  At a rejection `K ∈ B_i` the opening-capital-bounded bid is
  below the promise, so `B_K(i) ≤ w_K b*_K < w_K e_{i,K}`, and
  `B_K(i) = A_i(K) + chargedRecord_i(K−1)` (LEAN `B_eq`).  Paid ≤ promised gives the
  record over the tests *before* `K`: `ℓ^i_{<K} < w_K e_{i,K} − A_i(K)` (LEAN
  `record_lt_of_rejected_opening`).  The criterion's record (Definition 5) is *inclusive*,
  `ℓ^i_K = Σ_{k ∈ M_i, k ≤ K}`, and at the rejection round `i` may itself be the
  wealth-constrained winner, contributing `w_K (G_K − e_{i,K}) ≤ w_K`; hence
  `ℓ^i_K < 2 w_K − A_i(K)` (LEAN `record_succ_lt_of_rejected_opening`), which tends to
  `−∞` along `B_i` under

  ```
  (i″)   A_i(K) − 2 w_K → ∞      for every i        (capital adequacy, opening timing)
  ```
  (i″) implies the (A′) condition.  The paper's proof uses the strict record
  `Σ_{t<T}` and needs only `A_i(K) − w_K → ∞`; the factor 2 is the price of the inclusive
  definition the criterion actually states, and it is exact — a hypothesis with no carried
  wealth needs `w_K` of opening capital to bid its promise and may lose a further `w_K` on
  that very test (FIX `test_timing.test_opening_timing_finances_the_current_spike`:
  with coefficient 1 the spike liar, carrying nothing after a loss, bids `0.69 < 3/4` at
  the next spike).  The first three passes' `A_i(K) − m_K → ∞` is replaced by (i″).

(i″) replaces the paper's `Σ_n A(n,i) = ∞`, which is (i″) at `w ≡ 1` up to the constant.

**Computability** (DERIVED, as in the paper's part 4): with `A(k, ·)` supported on
`i ≤ s(k)`, `s` computable with `s(k) → ∞`, the **bidders** at round `k` are the
ever-activated frontier `s*(k) := max_{j≤k} s(j)` — a hypothesis activated when
`i ≤ s(j)` keeps its wealth and keeps bidding after `s` drops below `i`.  `s*` is
nondecreasing, finite and computable from the prefix.  A hypothesis with `i > s*(k)` has
wealth 0 and bid 0 and is never the winner while some active bid is positive.  So `s*(k)`
hypotheses are simulated at round `k`, each once; the winner's controller runs for `m_k`
gated steps.  Cost per macro-round `O(s*(k) g(k) + m_k · (controller + gate))`; the
subsidy `𝒜_K` counts only `s(k)`.  FIX `test_final.D_NonmonotoneSupport`.

**Weighted BRIA construction theorem** (DERIVED from the above, the algebra LEAN):
*for any schedule `(w_k)` and any opening subsidy rule `A` with finite support satisfying
(i″) and (ii), the opening-timed auction is a weighted BRIA covering every c.e. class of
e.c. continuation hypotheses, computable with finitely many active hypotheses per
round.*

## 4. Capital adequacy and the existence theorem — *[repaired by the pressure pass; timing aligned in the fourth pass]*

**Fixture J** (FIX `test_weighted.J_Starvation`).  `m_k = k` with the paper's
`A(k,i) = k^{-1} i^{-2}`: `A_2(400) ≈ 1.6` against `m_400 = 400`; a hypothesis promising 1
on a controller paying 0 is rejected at every one of 400 rounds and tested at none.  The
auction is not a weighted BRIA for that schedule: capital adequacy fails.  With the *replenishing*
allowance `a_k = (M_k − M_{k−1}) + 1/k` on a two-element support, the same hypothesis is
tested at rounds `1, 2, 4, 12, 44, 171` — whenever its wealth passes `(3/4) m_k`, i.e. at
rounds spaced by a factor tending to 4 — its record is below `−200`, and the weighted
overestimation is below `1/100`.

### 4.1 The three layers

The first version of this document compressed three statements into one "iff".  They
have different quantifiers and are stated separately.

**I. Criterion impossibility under dominance** (DERIVED; the inequality LEAN
`dominant_block_lower_bound`; FIX `test_weighted.Dominance`).  Let `(m_k)` satisfy
`limsup_K m_K / S_K > 0`.  Then there is a positive *rational* `q` with
`D_q := {K : m_K ≥ q S_K}` infinite (any rational below the limsup).  Environment:
controller `good` pays `γ ∈ (0,1)` per step, controller `liar` pays 0, no reward exceeds
`γ`.  Hypotheses: `h_g = (good, γ)` at every round; `h_l = (liar, 1)` at `K ∈ D_q`,
`(liar, 0)` elsewhere.  Then **no estimating agent** — computable or not — is a weighted
BRIA covering `{h_g, h_l}`.

Proof.  `h_g`'s record is 0 on every test set, so it is rejected finitely often:
`α^e_k ≥ γ ≥ G_k` for `k ≥ k_0`.  If `α^e_K = 1` at infinitely many `K ∈ D_q`, the
cumulative weighted overestimation at each such `K ≥ k_0` is at least
`m_K (1 − γ) − S_{k_0} ≥ q(1−γ) S_K − S_{k_0}`, violating no overestimation.  So
`α^e_K < 1 = h^e_{l,K}` at all but finitely many `K ∈ D_q`: `B_l` is infinite, `h_l`'s
record must diverge, tests where it promises 0 contribute `≥ 0`, so it is tested at
infinitely many `K ∈ D_q`.  At such a test with `K ≥ k_0`, `G_K = 0` and `α^e_K ≥ γ`, and
`dominant_block_lower_bound` (with `ε = 0`, `c = q`) gives cumulative weighted
overestimation at least `qγ S_K − S_{k_0}`, whose ratio to `S_K` exceeds `qγ/2`
infinitely often.  Contradiction.  ∎

Effectivity.  `q` exists for every dominant schedule but is not computable from a code
for the schedule (the limsup is not).  *Given* `q`, `D_q` is decidable for a computable
schedule by an integer comparison of `m_K` against `q S_K`, and `h_l` is e.c. whenever
the schedule is: it needs one running sum and one comparison per round.  So the
statement is: for every schedule with `limsup m_K/S_K > 0` there exists a rational `q`,
and for every such `q` the two-element class `{h_g, h_l}` — e.c. when the schedule is —
and the computable environment above defeat every estimating agent.  Existential in
`q`, uniform given `q`, criterion-level, for the full e.c. class or any class containing
these two.  A class that excludes such hypotheses (sound promises only) is not defeated by
this argument.  The failure of the auction under dominance is a corollary: nothing
satisfies the criterion there.

**II. Auction sufficiency** (DERIVED from §3, the algebra LEAN).  For any schedule and any
opening subsidy rule with finite support satisfying capital adequacy (i″)
`A_i(k) − 2 m_k → ∞` for every `i` and negligible subsidy (ii) `𝒜_K / S_K → 0`, the
opening-timed auction of §3 is a weighted BRIA covering every c.e. class of e.c.
continuation hypotheses.  No condition on the schedule beyond what (i″) and (ii) say.

**III. Existence of allowances, with a uniform online witness** (DERIVED; the sum bound
LEAN `sum_support_jump_le`, `sum_jump_div_sqrt_le`; FIX `test_pressure.A_EffectivityGap`,
`B_ExplicitSchedule`, `test_timing`).  *[Timing aligned in the fourth pass: opening
subsidy, coefficient 2.]*

*(a) Opening subsidies satisfying (i″) and (ii) exist iff `m_K / S_K → 0`.*  Only if:
(i″) for `i = 1` gives `𝒜_K ≥ A_1(K) ≥ 2 m_K − C` eventually, so
`𝒜_K / S_K ≥ 2 m_K/S_K − o(1)`, and (ii) forces `m_K/S_K → 0`.  (The same one line works
for any fixed coefficient `c > 0` in place of 2.)

*(b) Uniform online construction.*  At the opening of block `k`, after `m_k` is
revealed, with `S_k = Σ_{j≤k} m_j` and `M_k = max_{j≤k} m_j`:

```
support     s(k) := ⌊ √(S_k / M_k) ⌋
subsidy     A(k, i) := 2 (M_k − M_{k−1}) + 1/k     for i ≤ s(k),   0 otherwise,
```
credited before bids.  Both read `(S_k, M_k)` alone — no modulus of convergence, no
information about `m_{k+1}, …`, no code for the schedule.  If `m_K/S_K → 0` then (i″)
and (ii) hold:

- (i″).  `M_K/S_K → 0` (a dominant running maximum is dominant at its own index:
  `m_j = M_K ≥ c S_K ≥ c S_j`), so `S_k/M_k → ∞` and `s(k) → ∞`; hence for every `i` there
  is a last round `k_i − 1` with `s(k) < i`, and `i` receives subsidy at every `k ≥ k_i`
  (gaps before `k_i` lower `A_i` by a constant; a gap never reduces wealth).  Then
  `A_i(K) ≥ 2(M_K − M_{k_i − 1}) + Σ_{k=k_i}^{K} 1/k`, so
  `A_i(K) − 2 m_K ≥ −2 M_{k_i−1} + ln(K/k_i) → ∞`.  A hypothesis outside the current
  support still bids (it is in the frontier), so (A′)/(C′) apply to it unchanged.
- (ii).  `𝒜_K = 2 Σ_{k≤K} s(k) (M_k − M_{k−1}) + Σ_{k≤K} s(k)/k`.  For the first sum,
  `s(k) ≤ √(S_k/M_k) ≤ √S_K / √M_k`, so `s(k)(M_k − M_{k−1}) ≤ √S_K · (M_k − M_{k−1})/√M_k`,
  and `Σ_k (M_k − M_{k−1})/√M_k ≤ 2√M_K` because `(a − b)/√a ≤ 2(√a − √b)` for
  `0 ≤ b ≤ a` (LEAN `jump_div_sqrt_le`) and the right side telescopes (LEAN
  `sum_jump_div_sqrt_le`; the support-weighted form is `sum_support_jump_le` with
  `B = √S_K`).  For the second, `s(k) ≤ √S_K` and `Σ_{k≤K} 1/k ≤ 1 + ln K`.  Hence

  ```
  𝒜_K  ≤  4 √(S_K M_K)  +  √S_K (1 + ln K)  =  S_K · [ 4√(M_K/S_K) + (1 + ln K)/√S_K ]  =  o(S_K),
  ```
  using `S_K ≥ K` for the last term.

So, in the dispatch's terms: **A** (mathematical non-dominance) suffices; **B** (effective
non-dominance, a computable majorant or modulus) is not needed; **C** (uniform
construction) holds in the strongest form — one online rule, reading only the prefix
through the block just revealed, serves every non-dominant schedule, computable or not;
**D** is subsumed.  The second pass's `ρ̄` argument is withdrawn.

*(III′) The same theorem is false under settlement timing.*  Let the subsidy that funds
block `k` be fixed before `m_k` is revealed (the source paper's timing with any
prefix-online rule), and suppose the rule keeps `𝒜_K/S_K → 0` on every non-dominant
schedule.  Then there is a non-dominant schedule and an e.c. hypothesis the auction
never tests while it outpromises infinitely often.  Construction: fix `good` at `3/4`
and a `liar` returning 0 that promises 1 exactly at spike rounds and 0 elsewhere.  Build
the schedule inductively.  After the prefix through stage `j − 1`, continue with
`m = 1`; on the schedule "prefix then ones forever", which is non-dominant, the rule's
ratio `𝒜_K/S_K` tends to 0, so there is `K_j` beyond which it is below `1/(4j²)`; place the
spike at `k_j = K_j + 1` with `m_{k_j} = ⌈S_{k_j − 1}/j⌉`.  The rule reads only the prefix,
so its behaviour through `k_j − 1` is the same on the final schedule.  The liar's carried
wealth at `k_j` is at most `A_liar(k_j − 1) ≤ 𝒜_{k_j−1} < S_{k_j−1}/(4j²)`, so its bid is
below `1/(4j) < 3/4` and `good` wins; the liar is rejected at every spike and tested at
none, record 0.  The final schedule is non-dominant (`m_{k_j}/S_{k_j} ≤ 1/j`, and `1/S`
elsewhere).  ∎  FIX `test_timing.SurpriseSpike`: on the schedule of fixture A
(`m_{4^j} = ⌊S_{4^j−1}/j⌋`) under settlement timing the spike liar bids at most `0.58`
at every spike and is never tested, under either coefficient; under opening timing with
coefficient 2 it bids 1 at spikes 64, 256, 1024 and is tested at each.  So under the
source paper's timing the prefix theorem needs one-block lookahead — the subsidy credited
after round `k` may read `m_{k+1}` — which is exactly opening timing with a shifted index.

Computability of the resulting learner: the subsidy adds one comparison and one
addition per active hypothesis per round; with the paper's simulation argument over the
frontier `s*(k)` the learner is computable in `O(s*(k) g(k) + m_k (controller + gate))`
whenever the class is c.e. and e.c. and the schedule is computable (`Enumerated` in
`src/bria.py` is the lazy activation).  For a non-computable schedule presented online
(block lengths revealed as blocks open) the same learner runs relative to that
presentation.

**Existence Theorem for weighted BRIA** (I + II + III).  *For a declared schedule `(m_k)`
with integer (or rational) lengths revealed block by block, the following are
equivalent: (1) `m_K/S_K → 0`; (2) opening subsidies satisfying (i″) and (ii) exist; (3)
the prefix rule above, credited at the opening of each block, makes the auction a
weighted BRIA covering every c.e. class of e.c. continuation hypotheses.  If (1) fails,
then for some rational `q > 0` no estimating agent covers the two e.c. hypotheses of
layer I.  Under settlement timing (the subsidy funding block `k` fixed before `m_k` is
revealed) no prefix-online rule achieves (3) on every non-dominant schedule.*
Quantifiers: (1)⇒(3) is uniform and online; (3)⇒(2) by definition; (2)⇒(1) is III(a);
¬(1)⇒impossibility is layer I, existential in `q`; the settlement-timing negative is
III′.

**Fixture A of the pressure pass** (FIX `test_pressure.A_EffectivityGap`, retuned).  A
schedule with `m_k = 1` except at `k = 4^j`, where `m_k = ⌊S_{k−1}/j⌋`: non-dominant with
the spike a `1/(j+1)` share of time, converging as slowly as one likes.  The prefix rule's
total subsidy is within the bound above at `K = 64, 256, 1024`, its share of primitive
time decreases (`0.90, 0.77, 0.66` — slowly, by design), `A_1(K) − 2m_K` grows, the
always-lying hypothesis is tested repeatedly (record below `−300`) and the weighted
overestimation stays within `𝒜_K/S_K`.  The same rule on `m_k = ⌊log₂k⌋+1` tests the
liar at rounds 15, 32 and 240 with overestimation below `1/500`.

**Fixture K** (FIX `test_weighted.K_FeasibleSchedule`, retained): the declared schedule
`m_k = ⌊log₂ k⌋ + 1` with the explicit allowance `A(k, i) = i^{-2} / ⌊√k⌋` for `i ≤ k`.
(i″): `A_i(k) ≥ i^{-2} (2√(k+1) − 2 − i)` since `Σ_{n≤k} n^{-1/2} ≥ 2(√(k+1) − 1)` and the
first `i` terms are at most `i`; minus `2 m_k ≤ 2 log₂ k + 2` this tends to `∞`.  This
explicit schedule is declared in advance, so its allowance may be credited at either
timing; the factor-2 condition holds because `√k` outruns any multiple of `log k`.
(ii): `Σ_{n≤K} 1/⌊√n⌋ ≤ 2√K + ln K + 3`, so `𝒜_K ≤ ζ(2)(2√K + ln K + 3)`, while
`S_K ≥ log₂ K! ≥ K log₂ K − 1.45 K`; the ratio tends to 0.  Checked at `K = 10², …, 10⁵`.
The dispatch's family `m_k ≍ log k`, `A(k,i) ≍ i^{-2} k^{-a}` works for every `a ∈ [0, 1)`
by the same integrals; the paper's `a = 1` fails (i″) for this schedule, since
`A_i(k) ≍ i^{-2} ln k < log₂ k`.  For the downstream application, where the schedule is
chosen, either this explicit allowance or the prefix constructor serves; the prefix
constructor is preferred because it is one rule for every schedule.

## 5. Long tests as liability: the attention bound

From `W_{K+1}(i) = A_i(K) + chargedRecord_i(K) ≥ 0` (LEAN `wealth_eq`,
`wealth_nonneg_opening`, `chargedRecord_ge_neg_allowance`):

```
Σ_{k ∈ M_i, k ≤ K} w_k (b_k − G_k)  ≤  A_i(K)      (subsidy through K inclusive).
```

The weighted shortfall a hypothesis inflicts on its tests is bounded by the subsidy it
was given, the current round's opening subsidy included: capital credited before a test
is counted in the budget of that test (FIX `test_timing.Bounds`).  If some competitor always bids at least `β > 0` (a sound hypothesis with a
guaranteed floor), `i` wins only with `b_k ≥ β`, so for a hypothesis whose tests return 0
the primitive time it consumes is `Σ_{M_i} m_k ≤ A_i(K)/β`.  Under (ii) that is `o(S_K)`:
**wealth is a claim on execution time**, and a long lease costs proportionally more of it.
This is an identity of the construction, not an analogy; the liability register of the
workspace is not invoked.

The same bound is what makes the one-step auction myopic on a renewable investment and
what makes the sparse-test agent's excursions density-zero (`FIXED_HORIZON.md` §4A): an investing action is a refuted one-step test, and the
refuted tests of every hypothesis together consume at most `𝒜_K/β` rounds.

**Fixture I — monopoly under the unweighted charge** (FIX `test_weighted.I_Monopoly`).
Apply the paper's auction (opening-timed, weight 1 per block, bid `min(e, B)`) to a
variable-length block sequence.  Schedule `m_k = 2^{⌊√k⌋}` (non-dominant: `M_K/S_K ≍ 1/(4√K)`),
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
where a sound hypothesis guarantees `3/4`.  The weighted charge is necessary, and (i″) is
the price of it.

## 6. Answers to the dispatch's §8 questions

1. `m_k` is the weight for a per-time average (§1).
2. Finite truncated discounted leases have bounded weight and reduce to the ordinary
   criterion; infinite-horizon discounted claims need a settlement mechanism, OPEN (§1).
3. Yes, the primitive is a positive weight; the theorems are stated for `w_k`.
4. Lemma 6, Theorems 1–3 port with the algebra above; Theorem 1's two allowance
   conditions become (i″) and (ii), and its allowance timing becomes opening timing (§3).
5. Theorem 4 does not port as stated (OPEN); the paper's allowance fails capital adequacy
   as soon as `w_k` is unbounded, however slowly it grows; the first version's
   modulus-based support is withdrawn for the prefix constructor of §4.1; and under the
   paper's own timing no prefix-online rule works (III′).
6. Weighted coverage gives the weighted guaranteed-option theorem (§2), which is
   `GROWING_HORIZON.md`'s theorem.
7. Time expansion reduces the bounded case and fails the unbounded one (§1); the weighted
   criterion is the simpler formulation there, because the alternative does not exist.

## 7. What is not established

- Any rate: (i″) and (ii) are asymptotic; the geometric spacing of tests in fixture J is
  the auction's, not a bound.
- Sharpness of (i″) per hypothesis; the sharp condition is the schedule-level
  non-dominance, and (i″) is a sufficient uniform condition.  The constant 2 is forced
  by the inclusive record; whether a smaller allowance coefficient serves under a
  different tie-breaking or bidding rule is not asked.
- Any bound on the *rate* at which the prefix constructor's `𝒜_K/S_K` vanishes beyond
  `4√(M_K/S_K) + (1 + ln K)/√S_K`; on the spiky schedule that is slow by design.
- A weighted Theorem 4.
- That the learner may *choose* `m_k` adaptively; the schedule here is declared in
  advance and known to hypotheses.  Hypothesis-requested lease lengths are a
  combinatorial-auction question the paper's footnote gestures at and this round does not
  touch.

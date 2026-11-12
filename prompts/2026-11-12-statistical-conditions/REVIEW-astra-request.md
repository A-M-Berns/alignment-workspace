# Two claims for adversarial review

Setting. A logical-induction-style market with a *floor*: on day `n` the price `p_n` of a
fresh sentence `phi_n` must satisfy `p_n >= c`, `0 < c < 1` fixed. `phi_n` settles the next
day at truth value `x_n` in {0,1}. The market is a `DualCertifiedMarket`
(`ExactConditions.lean` in this directory): prices `P`, multipliers `mu_n >= 0`, tolerances
`eps_n > 0` with `sum eps_n <= epsTotal`, and the **day inequality**

    for every valuation w in the cube [0,1]^Sentences:
        (firm's day-n value at w) + mu_n * (w(phi_n) - c)  <=  eps_n,

where the firm is the Logical Induction trading firm (a fixed weighted sum of all budgeted
efficiently computable traders) and its day value at `w` is
`sum_trades coef(P) * (w(sentence) - P_n(sentence))`. The **account** is
`Q_N(w) = sum_{n<=N} mu_n (w(phi_n) - c)`. Proved earlier (kernel-checked):
`Q_N <= U := 2 + epsTotal` at every live world, and *preservation*: if `Q_N >= -B` at every
world live at `N`, for all `N`, then no efficiently computable (e.c.) trader exploits `P`.
The converse of preservation was open, and so was any way to get the lower bound from a
statistical property of `x` (frequency of truth at least `c + gamma`).

All Lean referred to is in `StatisticalConditions.lean` here and compiles against the
pinned toolchain with axioms `[propext, Classical.choice, Quot.sound]`. You cannot build it
in this sandbox; review the mathematics and the statements. Attack both claims: look for a
false step, a hypothesis that is vacuous or silently strong, a statement that says less
than its gloss, and a gloss that says more than its statement.

## Claim R (the strongest claimed result): bounded account, or the threshold buyer exploits

**R1 (slackness).** Put `w = P_n` in the day inequality. The firm's day value at its own
prices is 0, so `mu_n (p_n - c) <= eps_n`. (`stake_prices_le`, `mu_mul_clearance_le`.)

**R2 (the account charges only days near the floor).** For any `delta > 0`, any `N`, any
valuation `w >= 0`:

    Q_N(w) >= -c * ( epsTotal/delta + sum_{n<=N, p_n < c+delta} mu_n ).

Proof: each term `mu_n (w - c) >= -c mu_n`; on a day with `p_n >= c + delta`, R1 gives
`mu_n <= eps_n/delta`. (`account_ge_slack`.) Corollary (`accountBounded_of_eventually_slack`):
if `p_n >= c + delta` for all `n >= N0`, the account is bounded below by
`c (epsTotal/delta + sum_{n<N0} mu_n)`, hence by preservation no e.c. trader exploits.

**R3 (the buyer).** Fix rationals `c >= 0`, `delta > 0`. Let
`W_n = min(1, max(0, (2/delta)(c + delta - p_n)))`: 1 when `p_n <= c + delta/2`, 0 when
`p_n >= c + delta`. It is an expressible feature of the day-`n` price of `phi_n` (rank `n`).
The *threshold buyer* buys `W_n` shares of `phi_n` on day `n`. Hypothesis
`Along c gamma x W`: if `W` is not summable then for all large `N`,
`(c + gamma) sum_{n<N} W_n <= sum_{n<N} W_n x_n`. With `delta < gamma`: if `W` is not
summable, the buyer's net worth over live worlds is bounded below and unbounded above,
i.e. it exploits. Proof: `W_n (x_n - p_n) >= W_n (x_n - (c+delta))` since `W_n > 0` forces
`p_n < c + delta`; summing, the settled value is at least
`sum W x - (c+delta) sum W >= (gamma - delta) sum W -> infinity` from `N0` on, at least
`-(c+delta) sum_{n<N0} W` before, and the open instance costs at most 1.
(`thresholdBuyer_exploits`; any history with prices at most 1, no certificate.)

**R (dichotomy, `bounded_or_buyer_exploits`).** In a dual-certified market with one floor
`c` per day, sentences settled by the next day, some world live each day, and
`Along c gamma x W` for the threshold weighting with `delta < gamma`:
*either the account is bounded below over live prefixes, or the threshold buyer exploits.*
Proof: if `W` is summable then `W_n < 1` eventually, so `p_n >= c + delta/2` eventually, so
R2 bounds the account; otherwise R3. Corollary (`accountBounded_iff_unexploited`): if the
threshold buyer is efficiently computable (a hypothesis, not discharged), then
*account bounded below  <=>  no e.c. trader exploits*.

Glosses claimed for R:
(g1) Under the frequency hypothesis along this ONE weighting, the converse of preservation
     holds: an unbounded account yields an exploiting e.c. trader — and the exploiter is a
     *buyer*, not the seller of the multipliers the earlier work was looking for.
(g2) Under that hypothesis the account is exactly the right criterion for a statistical
     floor: there is no logical inductor with a floor and an unbounded account.
(g3) The hypothesis that makes the earlier "bridge" fire is therefore not a frequency
     statement along the market's own normalized multipliers `mu_n/(U+1-Q_{n-1})`
     (uninhabited except when every x_n = 1) but (i) frequency along the threshold
     weighting — one explicit price feature — plus (ii) non-exploitation by one explicit
     trader; equivalently the floor is eventually slack: `p_n >= c + delta/2` for large n.
(g4) R does NOT show the account is bounded from the frequency hypothesis alone. It leaves
     open whether the floor market can have `W` non-summable (price near the floor
     infinitely often) on a sequence whose frequency along `W` is at least `c + gamma`.

Witness given: fresh atoms, truth sequence false on day 0 and true after; there
`Along` holds for every `[0,1]` weighting and the account is bounded (by a separate
finite-loss bound: with at most `R` false instances the account is at least
`-U((1-c)^-(R+1) - 1)`). No witness with infinitely many false instances exists.

## Claim X (the strongest claimed refutation): per-trader frequency bounds do not sum; whether the account is bounded depends on the firm's weights

Sequence level only. Stakes `mu_n >= 0`, settled account `prior_n = sum_{i<n} mu_i (x_i - c)`,
per-day ceiling `prior_n + mu_n (1-c) <= U`. `k_n` = number of false instances before `n`.

**X1 (one weighting).** If `w_n in [0,1]`, and `Along c gamma x w` with `gamma >= 0`, then
`sum_{i<N} w_i (c - x_i)` is bounded above in `N` (`Frequency.gain_bddAbove`). The bound is
`c * sum_{i<N0} w_i` where `N0` is where the frequency hypothesis starts to hold for *that*
weighting; nothing bounds `N0` across weightings.

**X2 (tables).** The table `T_R` (budget 1) stakes its whole wealth at the floor's odds,
`(1-c)^-(k+1)` shares, on the `k`-th false instance for `k < R`, and nothing else. Its
settled account is `-((1-c)^-min(k_n,R) - 1)`: bounded for each `R` (`table_prior`).
Each `T_R` has finite support, so it is a trivially non-divergent weighting: no
pseudorandomness hypothesis quantifying over *divergent* weightings constrains it.

**X3 (the mixture).** Weight `T_R` by `theta^R`, `R >= 1`, `0 <= theta < 1`. The weighted
sum of stakes on the `k`-th false instance is `(theta/(1-c))^(k+1) / (1-theta)`
(`stake_eq_tsum`). It meets the summed ceiling `U = theta/(1-theta)` = total weighted
budget (`ceiling`). Its settled account is
`-(c/(1-theta)) sum_{j<k_n} (theta/(1-c))^(j+1)` (`prior_eq`). Hence:
if `theta >= 1 - c` the account is at most `-(c/(1-theta)) k_n` — unbounded below on every
sequence with infinitely many false instances (`prior_le`); if `theta < 1 - c` it is bounded
below by a constant (`prior_ge`).

Glosses claimed for X:
(h1) So "frequency at least `c+gamma` along every (divergent, efficiently generable)
     weighting" cannot by itself bound the account of a mixture of traders: the per-trader
     bounds exist and do not sum, and whether they sum depends on the mixture's weights
     against `(1-c)` — in a firm, on the enumeration of traders. A theorem bounding the
     account must mention the weights (e.g. a discounted uniform bound
     `sum_k weight_k * sup_N gain_k(N) < infinity`), or go through prices as Claim R does.
(h2) This is NOT a counterexample market. Not shown: that the pinned firm contains such
     tables at such weights; that the market maker's fixed point leaves the tables net
     short at the floor (buyers in the firm net against them); that the truth sequence is
     pseudorandom relative to the resulting prices. Heuristic, with an exact toy
     (`floor_toy.py`, E3 and E5): when tables pin the price to the floor only on false
     days, the price reveals the false days, so the sequence is not pseudorandom relative
     to the market's own prices and a price-follower exploits; when tables that also stake
     a little off-table pin the price at the floor on every day (E5), prices carry no
     information, the frequency along the threshold weighting is the base rate, the
     account falls without bound and the buyer's wealth grows — consistent with Claim R's
     second horn.
(h3) An informal estimate: with firm weight `2^-j` for the trader of index `j`, a table for
     `R` false instances that is hard-coded needs index exponential in `R` when the
     sequence is incompressible, so its weighted gain `2^-j (1-c)^-R` vanishes; an
     enumeration that places the true `R`-table at index about `a R` makes it
     `(2^a (1-c))^-R`, unbounded when `c > 1 - 2^-a`. So the answer depends on the
     enumeration and on `c`.

## What to return

For each of R1, R2, R3, R, g1–g4, X1, X2, X3, h1–h3: CORRECT / WRONG / OVERSTATED, with the
specific step or counterexample. Then: the single most damaging objection to presenting R
as "the statistical theorem", and to presenting X as "a refutation". Be concrete; do not
summarize the claims back.

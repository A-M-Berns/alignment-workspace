# Statistical conditions on a floor market — statements of record and assumption ledgers

Every named object is a declaration in the namespace
`Workspace.Normativity.Contrib.StatisticalConditions`, in `StatisticalConditions.lean` or
`StatisticalConditionsVille.lean` under `lean/Workspace/Normativity/Contrib/`. Rerun:
`~/.claude/scripts/safe-lake.sh build Workspace` from `lean/`, then
`python3 tests/audit_axioms.py`. Each module ends with its `#print axioms` list; every result
audits to `[propext, Classical.choice, Quot.sound]`.

The setting, from `ExactConditions`: one floor `c ≤ price(φ n)` per day, realized values `x n`,
stakes `mu n ≥ 0`, `prior n = Σ_{i<n} mu i (x i − c)` (`Bridge.prior`), ceiling `U`, and the
**per-day ceiling** `prior n + mu n (1 − c) ≤ U`. In a `DualCertifiedMarket` `M` with
`M.C = floors φ (fun _ => c)` the stake is `M.mu n 0`, and the two **settlement hypotheses**
are `hsettle` (a world live at `N` gives `φ i` the value `b i` for `i < N`) and `hfresh` (on
day `n` a world affirming `φ n` is live). `realized b n` is `1` or `0`.

## 1. The cost of finitely many losses (`Losses`)

`lost c x n` is the number of `i < n` with `x i < c`.

**Theorem** (`Losses.headroom_le`). `0 ≤ c < 1`, `x n ≥ 0`, `mu n ≥ 0`, the per-day ceiling.
Then `U − prior n ≤ U (1 − c)^-(lost c x n)`.

**Theorem** (`Losses.account_ge`). Under the same hypotheses, for every `y ≥ 0`:
`prior n + mu n (y − c) ≥ −U ((1 − c)^-(lost c x n + 1) − 1)`. The exponent counts the lost
instances before `n` and one more for the open instance. `Losses.prior_ge` is the settled
account alone, with exponent `lost c x n`.

An instance with `x i ≥ c` is not counted: it does not raise the headroom. In particular an
instance refunded at its strength (`x i = c`) or not staked (`mu i = 0`) costs nothing.

**Theorem, tightness** (`Losses.compound_prior`, `Losses.compound_ceiling`).
`compound c U x n` is `U (1 − c)^-(lost c x n + 1)` on an instance with `x n < c` and `0`
otherwise. If `c < 1`, `U ≥ 0` and every lost instance settles at `0`, it meets the per-day
ceiling, with equality on each lost instance, and its settled account is exactly
`−U ((1 − c)^-(lost c x n) − 1)`. So the bound of `prior_ge` is attained on every truth
sequence, by a staker that stakes nothing on the instances that hold; the bound of
`account_ge` is attained at `y = 0` on a lost instance.

**Theorem, market form** (`DualCertifiedMarket.account_ge_of_losses`). `0 ≤ c < 1`,
`M.C = floors φ (fun _ => c)`, `hsettle`, `hfresh`. At every world live at `N`,
`account N ≥ −M.U ((1 − c)^-(lost c (realized b) N + 1) − 1)`.

**Theorem** (`DualCertifiedMarket.accountBounded_of_finite_losses`, registered
`statistical.finite-losses-affordable`). If moreover `lost c (realized b) N ≤ R` for all `N`,
then `M.AccountBounded (M.U ((1 − c)^-(R + 1) − 1))`.

*Ledger.* The bound is geometric in `R`; nothing here bounds the account of a schema with
infinitely many lost instances. *Inhabited:* `finiteLosses_witness` — fresh atoms at a constant
`c ∈ (0, 1)` over `truthProcess oneLoss`, which settles atom `0` false and every later atom
true; the floor market's account is bounded below by `3 ((1 − c)^-2 − 1)` and no efficiently
computable trader exploits it.

## 2. Unit stakes and market stakes (`Stakes`)

`WarrantSolvency.Schema.bounded_iff_frequency` reads a unit stake per undefeated instance: the
account is `T_n − c·U_n` and is bounded below iff `c·U_n − T_n` is bounded above. With the
stake `mu n` the identity survives (the account is `Σ mu i (x i − c)` by definition) and the
equivalence with the unweighted count does not:

**Theorem** (`Stakes.unit_bounded_staked_unbounded`). `c = 1/2`, `x` alternating (true on even
days). The unit-stake account takes the values `0` and `1/2`. The stakes `1` on true days and
`2` on false days are nonnegative, meet the per-day ceiling `3/2`, and their account after
`2m` days is `−m/2`.

**Theorem** (`Stakes.unit_unbounded_staked_bounded`). `c = 1/2`, `x` always false. The
unit-stake account after `n` days is `−n/2`. The stakes `2^-n` meet the per-day ceiling `1/2`
and their account stays above `−1`.

**Theorem** (`Stakes.abel_bound`). If `|Σ_{i<n} d i| ≤ B`, `|mu n| ≤ Mb` and
`Σ_{i<n} |mu (i+1) − mu i| ≤ V` for all `n`, then `|Σ_{i<n} mu i · d i| ≤ B (Mb + V)`.

So boundedness passes from unit stakes to market stakes when the stakes have bounded
variation, and back when their reciprocals do (the same theorem applied to `mu·d` and
`1/mu`; not stated separately). The first counterexample has stakes in `{1, 2}`: bounded and
bounded away from zero is not enough.

## 3. Random outcomes (`StatisticalConditionsVille`)

**Theorem** (`ville`). `μ` finite, `Y` a supermartingale for a filtration over `ℕ`,
`Y n ω ≥ 0`, `a > 0`. Then `μ {ω | ∃ n, a ≤ Y n ω} ≤ ofReal (E[Y 0] / a)`. Proof:
`ville_finite`, optional stopping (`Submartingale.expected_stoppedValue_mono` on `−Y`) at the
first day through `N` with `Y ≥ a`, Markov's inequality on the stopped value, then the union
over `N`.

`Betting.Fair μ ℱ c U x mu`: `0 ≤ c < 1`; `mu n` is `ℱ n`-measurable and nonnegative; `x n` is
`ℱ (n+1)`-measurable with values in `[0, 1]`; `c ≤ E[x n | ℱ n]` almost surely; and the per-day
ceiling holds at every `ω`, for `account c x mu n ω = prior` along the path.

**Theorem** (`Betting.Fair.headroom_supermartingale`). `U − account n` is a supermartingale;
it is nonnegative (`Fair.headroom_nonneg`).

**Theorem** (`Betting.Fair.account_bound`, registered `statistical.capital-bound-probability`).
`μ` a probability measure, `K > 0`: `μ {ω | ∃ n, account n ω ≤ −K} ≤ ofReal (U / (U + K))`.

**Theorem** (`Betting.Fair.ae_bounded_below`). Almost surely there is `K` with
`account n ω > −K` for all `n`.

*Ledger.* No margin `γ` is used. Integrability of the stakes is not assumed: `Fair.mu_le`
gets `mu n ≤ U (1 − c)^-(n+1)` from `Losses.headroom_le`. *Inhabited:* `Betting.witness` — a
fair coin on `Bool`, nothing known on day `0`, one unit staked on the coin at `c = U = 1/2`,
later outcomes one and unstaked; the settled account is `−1/2` on tails.

*What a market would need for this to give `AccountBounded` path by path* (stated, not built;
item 140). (i) A probability space carrying the observations, and an assessment whose live
worlds at `N` are the worlds agreeing with the observations through `N`, so that `hsettle`
holds along each path. (ii) The market's multiplier `mu n` measurable in the observations
before day `n`: in `FloorSchedule.market` it is a function of the realized past prices, which
are functions of the assessment's tables through day `n`, so this needs the assessment's
day-`n` tables to be measurable in the observations through day `n − 1`. (iii) The comparison
is with the *settled* account: `AccountBounded` quantifies over every world live at `N`,
including the one refuting the open instance, and `account_bound` bounds `prior N`; the open
instance adds at most `c · mu N ≤ c (U − prior N)/(1 − c)`, so a bound on `prior` gives one on
the account with the factor `(1 − c)⁻¹`. (iv) Every instance settles. An instance that is
true and never settled stays open in every later live world with both values, the account at
the refuting world carries `−c · mu` for it forever, and the supermartingale step — which
credits `mu (1 − c)` when it settles true — never happens for it; the ceiling `account_le`
still holds, but nothing bounds the number of such open instances. (v) The conclusion is
almost-sure, with a path-dependent bound: `AccountBounded B` for one `B` on a set of paths of
probability at least `1 − U/(U + B')`, not `AccountBounded` on every path.

## 4. The deterministic case

### 4(c), 4(d). Slack floors and the buyer near the floor

**Theorem** (`DualCertifiedMarket.stake_prices_le`). In any dual-certified market,
`M.C.stake M.mu n (M.P n) ≤ M.eps n`: the day's rows, staked by the multipliers and evaluated
at the posted prices, are worth at most the day's tolerance. Proof: the day inequality at the
valuation `w = M.P n`, where the firm's day value is `0`. For one floor per day
(`mu_mul_clearance_le`): `M.mu n 0 · (M.P n (φ n) − c) ≤ M.eps n`.

**Theorem** (`DualCertifiedMarket.account_ge_slack`). `0 ≤ c`, `M.C = floors φ (fun _ => c)`,
`δ > 0`, `w ≥ 0`. Then
`account N w ≥ −c (M.epsTotal/δ + Σ_{n ≤ N, M.P n (φ n) < c + δ} M.mu n 0)`.

**Theorem** (`DualCertifiedMarket.accountBounded_of_eventually_slack`, registered
`statistical.slack-floor-bounded`). If `c + δ ≤ M.P n (φ n)` for all `n ≥ N₀`, then
`M.AccountBounded (c (M.epsTotal/δ + Σ_{n<N₀} M.mu n 0))`.

`thresholdFeature φ c δ n` is the expressible feature
`min 1 (max 0 ((2/δ)(c + δ − φ_n^{*n})))`, of rank `n`; its value `thresholdWeight P φ c δ n`
is `1` when the price is at most `c + δ/2` and `0` when it is at least `c + δ`.
`thresholdBuyer φ c δ` buys that many shares of `φ n` on day `n`.

`Frequency.Along c γ x w`: if `w` is not summable, there is `N₀` with
`(c + γ) Σ_{i<N} w i ≤ Σ_{i<N} w i · x i` for all `N ≥ N₀`.

**Theorem** (`thresholdBuyer_exploits`). Any assessment `L` and history `P` with
`P n (φ n) ≤ 1`; `0 ≤ c`, `0 < δ < γ`; `hsettle`; a world live on every day;
`Frequency.Along c γ (realized b) (thresholdWeight P φ c δ)`; the threshold weights not
summable. Then `L.Exploits (thresholdBuyer φ c δ) P`. No certificate is involved.

**Theorem** (`DualCertifiedMarket.bounded_or_buyer_exploits`, registered
`statistical.bounded-or-buyer-exploits`). `M.C = floors φ (fun _ => c)`, `0 ≤ c`,
`0 < δ < γ`, `hsettle`, a world live on every day, and
`Frequency.Along c γ (realized b) (thresholdWeight M.P φ c δ)`. Then
`(∃ B, M.AccountBounded B) ∨ M.L.Exploits (thresholdBuyer φ c δ) M.P`.

**Theorem** (`DualCertifiedMarket.accountBounded_iff_unexploited`). If moreover
`EfficientlyComputable (thresholdBuyer φ c δ)`, then
`(∃ B, M.AccountBounded B) ↔ ∀ Tr, EfficientlyComputable Tr → ¬ M.L.Exploits Tr M.P`.

*Ledger.* The frequency hypothesis is on one weighting, a function of the market's own
prices. It is not derived from any property of the truth sequence alone. Efficiency of the
buyer is a hypothesis and is not discharged. The theorem does not say which disjunct holds:
it does not bound the account from the frequency hypothesis. The hypothesis is endogenous: a
truth sequence of frequency `3/4` priced at the floor on its false days and at one on its true
days fails it. `φ` is unrestricted in the declarations, and `ComputableMarket` is not a field
of a dual-certified market, so `IsLogicalInductor` needs it separately. *Inhabited:*
`thresholdFrequency_witness` — the market of `finiteLosses_witness` with `δ = (1 − c)/4`,
`γ = (1 − c)/2`; `oneLoss_along` gives the frequency hypothesis along every weighting in
`[0, 1]`, and the first disjunct holds. No witness with infinitely many false instances is
supplied, and none realizing the second disjunct in a dual-certified market.

### 4(a). One weighting

**Theorem** (`Frequency.gain_bddAbove`). `c ≥ 0`, `γ ≥ 0`, `w n ≥ 0`, `x n ≥ 0`,
`Frequency.Along c γ x w`. Then `Σ_{i<N} w i (c − x i)` is bounded above in `N`.

The bound is `c Σ' w` when `w` is summable and `c Σ_{i<N₀} w i`, for the `N₀` of that
weighting, when it is not; nothing bounds either across weightings. For a trader that restakes its
winnings the statement is `Bridge.bridge` (`ExactConditionsReserve`) applied to its own stake
and budget: under `Bridge.Frequency` for its own normalized stake `mu n / (U + 1 − prior n)`,
its account is bounded.

**Theorem** (`bridge_frequency_iff_summable`). Under the hypotheses of `Bridge.bridge`
(`0 < c < 1`, `γ > 0`, `x n ∈ [0, 1]`, `mu n ≥ 0`, the per-day ceiling),
`Bridge.Frequency c U γ x mu ↔ Summable (Bridge.ratio c U x mu)`. The hypothesis is an
implication from non-summability, so summable normalized stakes satisfy it whatever the
outcomes, and the bridge makes them summable. It holds, for instance, for `x 0 = 0`,
`mu 0 = 1` and nothing after. As a hypothesis it is the summability of the market's
normalized stakes and carries no frequency content of its own.

*Not proved, a reading:* whether one efficiently computable trader's normalized floor-selling
is a `PGenerableWeighting`. The pinned definition asks for a machine-metered stream of closed
features of rank at most the day. The trader's short position is such a feature by
`EfficientlyComputable`. Its normalization divides by `U + 1 − prior n`, which (i) depends on
the settled values `x i`, `i < n`, which are not price features — they can enter as constants
of the day-`n` feature only if the truth of `φ i` is computable in time polynomial in `n` by
day `n`; (ii) is a division, for which `EF` has only `safeRecip`, `max(1, ·)⁻¹` — and
`margin n ≥ 1` (`Bridge.bridge`'s proof), so `safeRecip` computes the reciprocal exactly;
(iii) is continuous. So expressibility turns on (i) alone. Item 141.

### 4(b). A mixture of tables (`TableMixture`)

`table c R x n` is `(1 − c)^-(lost c x n + 1)` on a lost instance among the first `R`, else
`0`: a staker of budget one that stakes its whole wealth at the floor's odds on the first `R`
lost instances. `stake c θ x n` is `(θ/(1 − c))^(lost c x n + 1) / (1 − θ)` on a lost instance,
else `0`.

**Theorem** (`TableMixture.stake_eq_tsum`). `0 ≤ θ < 1`:
`stake c θ x n = Σ'_R θ^(R+1) · table c (R+1) x n`.

**Theorem** (`TableMixture.table_prior`). `c < 1`, every lost instance settling at `0`:
`prior c x (table c R x) n = −((1 − c)^-min(lost c x n, R) − 1)`. Each table's account is
bounded.

**Theorem** (`TableMixture.ceiling`). `0 ≤ c < 1`, `0 ≤ θ < 1`: the mixture meets the per-day
ceiling `θ/(1 − θ)`, the tables' total weighted budget.

**Theorem** (`TableMixture.prior_le`, registered `statistical.table-mixture-unbounded`).
`0 ≤ c < 1`, `1 − c ≤ θ < 1`: `prior c x (stake c θ x) n ≤ −(c/(1 − θ)) · lost c x n`.

**Theorem** (`TableMixture.prior_ge`). `0 ≤ θ < 1 − c`:
`prior c x (stake c θ x) n ≥ −(c/(1 − θ)) (θ/(1 − c)) (1 − θ/(1 − c))⁻¹`.

*Ledger.* Sequences only. What this refutes is the inference from a bound on each
component's gain to a bound on the weighted mixture's. Each table stakes on finitely many
days, so no hypothesis on divergent weightings constrains it. The tables are defined from
`x`; that they form a uniformly computable family, or sit at prescribed indices of an
effective enumeration, is not shown. The mixture meets the scalar per-day ceiling and is not
shown to be the multiplier of any dual-certified market. Not shown: that the pinned firm contains such tables at
such weights (the firm's weight for the trader of index `j` sums to `2^-j` over budgets); that
the market maker's fixed point leaves them net short at the floor; that the truth sequence is
pseudorandom relative to the resulting prices. *Inhabited:* the statements hold for every
sequence `x` whose lost instances settle at `0`; the toy's E2 recomputes `prior_eq` on a
sequence with twelve losses.

## 5. The toy (exploration; no theorem depends on it)

`toy/floor_toy.py`, exact `fractions.Fraction`; `python3 toy/floor_toy.py --check`. One
sentence per day, floor `c = 3/5`; each trader's position is piecewise linear in the posted
price `p ∈ [c, 1]`; the price is the least `p` with weighted net position `≤ 0`, and the
multiplier is the net short at `p = c`. With the exact root the firm's gain is minus the
account. The scrambled sequence is false on days fixed by an integer hash (six false days in
32, twelve in 60).

| experiment | days | false | floor binds | of which false | final account |
|---|---|---|---|---|---|
| E1 seller, seller on `0 mod 4`, buyer; all true | 20 | 0 | 3 | 0 | ≈ 0.209 |
| E1 same firm; periodic (false on `0 mod 4`) | 20 | 5 | 10 | 5 | ≈ −0.374 |
| E1 same firm; scrambled | 20 | 2 | 3 | 0 | ≈ 0.209 |
| E2 tables, `θ = 1/2 > 1 − c`; scrambled | 60 | 12 | 12 | 12 | −682090227/8388608 ≈ −81.3 |
| E2 tables, `θ = 3/10 < 1 − c`; scrambled | 60 | 12 | 12 | 12 | −20887425/8388608 ≈ −2.49 |
| E3 tables `θ = 1/2`, buyer, price follower; scrambled | 32 | 6 | 10 | 6 | ≈ −16.3 |
| E4 buyer, price follower; scrambled | 32 | 6 | 0 | 0 | 0 |
| E5 tables `θ = 4/5` staking 1/20 off-table, buyer; scrambled | 32 | 6 | 32 | 6 | ≈ −100.6 |

Readings, each of a finite run. E2 equals `TableMixture.prior_eq` exactly (asserted by
`--check`). In E3 the floor binds on all six false days and on four of the 26 true ones, so
among floor-binding days the realized frequency is `4/10 < c`. In E5 the floor binds on each
of the 32 days, the posted price is the constant `c` (asserted), the realized frequency over
those days is `26/32 > c`, the account falls at each false day, and the buyer's wealth grows
from `1` to about `13.5`. That is the shape of the second disjunct of
`bounded_or_buyer_exploits` over 32 days, in a model whose firm weights were chosen for it;
it establishes neither perpetual binding nor an unbounded account. The scrambled sequence is
an efficiently computable hash, so it is not pseudorandom against efficient weightings; it
is unpredictable only to the traders listed.

## 6. What it means for a warrant

No new mathematics. A warrant's three forms (`SeedStatics.Form`) are rows on prices, each a
demanded bet at strength `c`: `premise X c` is the floor `c ≤ P(X)`, with bet value `x_X − c`;
`applicability X XA c` and `strength XA XAY c` are conditional floors, with bet value
`x_consequent − c · x_antecedent`. Applied repeatedly, a form is one such bet per instance,
staked by the market's multiplier, and the account charges an instance by the value of its
bet at the settling world. By settlement outcome (`WarrantEntitlement.settleOutcome`):

- **kept** (nothing pinned false): the conditional bet is worth `1 − c` where antecedent and
  consequent hold. Credited, never charged; it lowers the headroom.
- **vacuous** (antecedent pinned false): the bet is worth `0 − c·0 = 0`. Free. This is the
  called-off instance of §1: it is not a loss and the headroom does not move.
- **rebutted** (antecedent holds, consequent pinned false): worth `0 − c = −c`. Charged
  `c · mu`. This is the lost instance: the headroom grows by a factor of at most `(1 − c)⁻¹`.
- **retired** (a premise whose sentence is pinned false): worth `−c`. Charged like a rebuttal;
  a premise form is an unconditional floor and has no vacuous case.
- **undercut by the docket**: the survivor rule removes the row from later days, and a row
  not demanded on a day has no multiplier that day, so nothing is charged from then on. A
  row already demanded on an earlier day settles at its bet's value as above; the account as
  defined has no refund for an instance withdrawn between its day and its settlement. Whether
  it should is a design question this round does not answer.

Affordable strengths, by lost-instance record. A schema at strength `c < 1` with at most `R`
rebutted or retired instances is affordable, with account at least
`−U ((1 − c)^-(R+1) − 1)`, and that bound is attained (§1). It is finite for every `c < 1` and
every `R`, grows geometrically in `R`, and is infinite at `c = 1`, where one loss is
unaffordable. With infinitely many losses the reserve does not carry the schema, and what
does is its track record against the prices: the schema is affordable when its instances'
prices eventually clear the strength by a margin (§4, `accountBounded_of_eventually_slack`);
if they do not while the realized frequency on the instances priced near the strength is
above it, the market is exploited by buying those instances (`bounded_or_buyer_exploits`).
With outcomes that are favourable at `c` given the past, every strength `c < 1` is affordable
with probability at least `K/(U + K)` at capital `K` (§3).

## What is typed and what is not shown

Typed and kernel-checked: every statement above marked **Theorem**.

Not shown:

- **The account bounded from a property of the truth sequence** with infinitely many false
  instances, in any dual-certified market. Item 138.
- **Which disjunct of `bounded_or_buyer_exploits` holds** in `FloorSchedule.market` on a
  sequence of frequency above `c + γ`; whether it depends on the firm's enumeration. The toy's
  E5 and `TableMixture` are a finite model and a sequence-level fact, not a market.
- **Efficiency of `thresholdBuyer`**, and so `accountBounded_iff_unexploited` without its last
  hypothesis. Item 139.
- **The converse of preservation without the frequency hypothesis.** Item 139.
- **That a trader's normalized floor-selling is a `PGenerableWeighting`.** Item 141.
- **`Frequency.Along` from the pinned dependency's `PseudorandomAbove`.** The two are the same
  shape (a weighted average eventually above a level along a divergent weighting) and no
  declaration relates them; `PseudorandomAbove` also asks patience of the weighting.
- **An assessment driven by random observations.** Item 140.
- **Necessity** of `δ < γ` in `thresholdBuyer_exploits`, and of bounded variation in
  `abel_bound` beyond the one counterexample.

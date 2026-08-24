# Enforcement affordability: the two-defect taxonomy, prosecuted

Status: **research memo; unregistered**. Every claim is `ci-only`; all names
are provisional under `AGENTS.md` §6. Pinned input: *Strengthening Logical
Induction with Traderized Constraints*, mathematical skeleton v44 (August 22,
2026), sha256
`868e5007b5c1ef3b417aa163861188005ca5e2b53ec2582dd94e663ae538a1fd`; and
`lean/Workspace/Normativity/Contrib/{AssessmentProcess,AssessmentFirm}.lean`
at the merge base of this branch, cross-read against the pinned source
formalization at FAF `c0d885bf`. All evidence below is exact rational
computation in the round's single finite market model (`src/market_model.py`)
under the MarketMaker guarantee as a verified postulate; grades are
`proved-in-model` (exact inequality asserted by the suite),
`bound-with-argument` (paper argument, spot-checked), `refuted (witness)`,
or `open`.

## Verdict

**Proposition 6.1's divergence is an artifact of per-day worst-case
accounting for margined contested schedules, and real exactly where the
taxonomy's two defect classes say it is.** The central mechanism survives
every fixture: liability is realized enforcement inventory against
budget-throttled opposing flow — at the verified fixed point the realized
enforcement coefficient tracks the realized opposing flow to within the day's
`2^-n` allowance, so the available intensity `λ_n` never converts to realized
loss. Of the three headline claims: **tolerance-independence survives**
(liabilities across `δ_n ∈ {1/2, 1/n, 2^-n}` differ only within the
MarketMaker allowance); **the trichotomy survives, reorganized** by the
maintainer's taxonomy with the diachronic class generalized to the pair
`(K_n, K^D_n)`; **the exploitation identity survives only with its
quantifiers repaired** — per-day plausibility is refuted by witness, the
surviving identity is at-horizon, nesting-dependent, and coalition-closed.
One dispatched sub-claim is refuted: W3's *linear* total-variation rate
holds only for throttle-pinned constant flow; an adaptive pump compounds.

| Target | Grade |
|---|---|
| G1 (a)(b)(c) | confirmed, citations in §0 |
| G2 floors sum; no netting | proved-in-model |
| T1 uncontested O(2^-n) | proved-in-model; strengthens Thm 3.4 there |
| T2 war-chest bound, δ-free | proved-in-model (bound); fixtures (i)–(v) intact |
| T2(vi) adjudication | **margin account wins**; core account refuted as a necessity claim |
| T3 both margin clauses necessary | proved-in-model (two witnesses) |
| W1 anti-settlement | proved-in-model; divergence forced via Thm 4.4 (cited) |
| W2 dogmatism rate | proved-in-model; both terms scale as 1/margin |
| W3 revision pump | proved-in-model; dispatched linear rate **refuted (witness)** — compounding |
| W4 settlement surprise stream | proved-in-model, with the vindication-recharge engine |
| Diachronic functional | Hausdorff TV **refuted (witness)**; set-gap functional proposed and witnessed |
| Tier 4 identity | per-day form **refuted (witness)**; at-horizon+nesting form survives |
| Taxonomy exhaustiveness | exhaustive under generalization (b); recommendation in Part II |

## 0. Honesty gates

**G1 — budgeter semantics: (a), (b), (c) all confirmed.**

- (a) *Per-component trade scaling from realized price history, not
  firm-level netting.* The generalized Budgeter scales the raw day trade by
  the minimum over the day's live payout tables of a per-table loss cap,
  `lossCap(b + rawPriorWorth_w, −currentValue_w)`, with
  `lossCap(available, current) = (max 1 (−current/available))⁻¹` — source
  `Budgeter.lean:783` (`lossCap`), `:727` (`budgetWorldScale`), `:735`
  (`budgetScaleFeature`), `:918` (`BudgeterAt` = shutoff-or-`scaleBy`);
  lift `AssessmentProcess.lean:358,392,472,498`. The prior worth in the
  denominator is the component's own realized wealth at that table computed
  from the rational price history (`rawPriorWorthOf`,
  `AssessmentProcess.lean:292`). The firm only sums components
  (`AssessmentFirm.lean:78` `TradingFirmAt`, `:127`
  `tradingFirmTrader_netWorth_eq_component_sum`); no cross-component
  quantity enters any scale. The shutoff test scans earlier days' live
  tables for a realized breach (`priorBudgetBreach`, source `:600`, lift
  `:399`, with its meaning theorem at lift `:518`).
- (b) *Floors quantify over arbitrary histories.*
  `budgetedTrader_netWorth_floor` (lift `:704`) assumes only a real history
  matching an arbitrary rational table; `componentTrader_netWorth_floor`
  (`AssessmentFirm.lean:266`) adds only the `[0,1]` range hypothesis;
  `tradingFirmTrader_netWorth_floor` (`:293`) gives −2 as
  `Σ_j (1/2)^j < 2`. Nothing references the unmodified recursion.
- (c) *Deductive specialization.* `ofDeductiveProcess`
  (`AssessmentProcess.lean:205`) sets `Live n v ↔ v.ConsistentWith (D n)`,
  and `exploits_ofDeductiveProcess` (`:217`) makes the generalized
  criterion's assessment set definitionally equal to LI exploitation
  relative to `D̄` — net worth through day `N` at worlds plausible at `N`.
  The Budgeter itself specializes extensionally
  (`budgetScaleFeature_ofDeductiveProcess_denote :835`,
  `priorBudgetBreach_ofDeductiveProcess :868`,
  `BudgeterAt_ofDeductiveProcess_value :890`), so the source construction
  is an instance, not an analogue. Weights: `tradingFirmWeight j b =
  2^-(j+1+b)` (source `TradingFirm.lean:325`), budget cost per component
  `(1/2)^j`.

Consequence used throughout: **the throttle quantifies over worlds live at
the current day, and available capital is world-relative** — a component
whose adverse worlds die is vindicated, its worst-case worth improves, and
its effective war chest recharges. This single semantic fact drives W4 and
the diachronic engine.

**G2 — aggregation (`TestG2Aggregation`).** The component floors bind
individually and additively however flow is spread: one attacker with the
whole chest and two attackers splitting it land under the same aggregate
bound, each component floored at its own budget at every live table. The
confederate fixture separates mechanical scaling from accounting offset: a
component's scale is identical with and without a massively profitable
confederate, while the deliberately wrong netted rule (available = own
budget + own worth + confederate's worth) would relax it. What caps a
distributed attack is the sum of per-component war chests — the −2 firm
floor is `Σ_j (1/2)^j`, spread-independent.

---

## Part I — Geometric defects

**General characterization (as the evidence supports it).** A single day's
region is defective in proportion to `1/m`, where `m` is the *plausibility
margin*: the minimum distance from the region to the plausible payoff
patterns it excludes, measured in the relative geometry (settled coordinates
excluded), together with containment in the deductive region. Absence of a
homothetic core is not a defect. The margin controls two separate bills at
the same `1/m` rate: the war-chest conversion (a component risking `m` per
share against its worst live table sustains `B/m` shares of flow) and — a
finding of this round — the MarketMaker allowance itself (the day-`n`
guarantee tolerates a net imbalance of `2^-n/p` near a vertex at price `p`,
so even the slack is billed at `1/margin`).

### The adjudication: K = {1/2} (T2(vi), `TestT2viPointPegAdjudication`)

The registered disagreement resolves for the **margin account**, on the
dispatch's own decision rule. Point peg `{1/2}`, seller flow `F = 1`, war
chest `B = 1`, sixteen days:

| tolerance | realized lifetime liability |
|---|---|
| `δ_n = 1/2` | 15/64 ≈ 0.234 |
| `δ_n = 1/n` | 0 |
| `δ_n = 2^-n` | 35/64 ≈ 0.547 |

Flat: the differences sit inside the `Σ 2^-n < 1` allowance, while the core
account predicts growth with `λ_n = ρ_n/δ_n²` — by day 16 of the dyadic
schedule that is a factor of order `4^16`, and none of it is realized. The
mechanism assertion pins why: at every verified fixed point the realized
enforcement coefficient equals the realized opposing flow to within
`7·2^-n`, at every tolerance. Intensity is *available*, inventory is
*realized*, and only flow converts the one into the other. (The `1/n` run
realizes zero because its day-1 tolerance is 1: the price is pushed to the
boundary 0, where the enforcer's absorbed shares cost nothing at the billing
vertex — an honest, if degenerate, corner of the same accounting.)

The homothetic-core lens (skeleton Remark 6.2) is thereby **sufficient but
not necessary**, and what it detects at `{1/2}` is a *revenue* property,
not a solvency property: against matched round-trip churn the interval
`[2/5, 3/5]` earns its width as spread while the point peg earns nothing
(`test_zero_width_earns_no_spread_against_churn`), but neither goes
insolvent. The genuinely defective point regions are the near-vertex ones:

| `K = {ε}`, buyer flow 1, `B = 1/4`, `δ = 1/16` | realized liability | `B(1−ε)/ε` |
|---|---|---|
| ε = 1/4 | 1.119 | 0.750 |
| ε = 1/8 | 4.770 | 1.750 |
| ε = 1/16 | 10.939 | 3.750 |

— the displayed rate is `1/margin` (each halving of ε better than doubles
the realized liability), with the excess over `B(1−ε)/ε` accounted exactly
by the allowance term `Σ 2^-n/ε`. Both accounts agree here, isolating the
disagreement to the center, as the dispatch required.

### The uncontested baseline (T1, `TestT1Uncontested`)

With a firm bound present (`A_n = 1`) but no realized opposing interest,
the fixed point sits within `2^-n` of `K` — not merely within `δ_n` — the
realized position is at most `11·2^-n`, and cumulative liability against
*every* payoff pattern, plausible or not, is under the geometric sum
`11·Σ 2^-n`. This strengthens skeleton Theorem 3.4 in the uncontested case:
the `δ_n` bound is what the *worst-case* day guarantees; the *realized*
fixed point concedes only the MarketMaker allowance. Checked at `δ = 1/2`
and `δ_n = 2^-n`.

### The contested interior peg (T2, `TestT2ContestedInteriorPeg`)

The load-bearing model theorem, `proved-in-model` on `K = [2/5, 3/5]`
against maximal-flow shorts, a confederate pair, a six-component dispersed
swarm, and matched churn, at all three tolerance schedules:

> lifetime liability ≤ (aggregate war chest) · hi/(1−hi) + 7·Σ 2^-n,

with `hi` the far edge from the billing vertex — numerically identical in
its `B`-term across `δ_n ∈ {1/2, 1/n, 2^-n}`, realized liabilities within
`2·7·Σ 2^-n` of one another. The accounting: the throttling world `y = 1`
bills the shorts `(1−p_n)` per share, so total flow is at most
`B/(1−sup p_n)` with `sup p_n < hi` under one-sided flow; the billing world
`y = 0` bills the enforcer's inventory at `p_n ≤ hi` per share; and
inventory equals flow up to the allowance. Churn is not an escape: a
matched round trip locks in at least the region's width per share as a sure
loss to the churner — the enforcer's world-uniform spread revenue — and the
war chest depletes until the budgeter's shutoff fires
(`test_iv_churn_earns_the_width_as_spread`).

### The margin definition (T3, `TestT3MarginDefinition`)

Both clauses are separately necessary. Dropping **containment in `K^D`**:
with `φ ↔ ψ` deduced and `K` a box off the diagonal, the riskless coherence
arbitrage (buy `φ` low, sell `ψ` high) gains at *every* live table, is never
throttled, never shuts off, and bills the enforcer at least 3/10 per day
forever. Putting the same flow against a region inside the diagonal
re-prices the two coordinates jointly and the free lunch vanishes — the
enforcer never goes negative. Dropping **the distance clause** reproduces
the `K = {ε}` blow-up: `{ε} ⊆ [0,1] = K^D` satisfies containment while
diverging at `1/margin`.

---

## Part II — Diachronic defects, generalized to the pair (K_n, K^D_n)

**General characterization (as the evidence supports it).** The diachronic
bill is governed not by Hausdorff total variation but by the **set-gap path
functional**: the sum over transitions of `dist(K_n, K_{n+1})` — the
*minimum* distance between consecutive regions — extended to the pair by
counting a settlement event as the gap `dist(K_n, settled face)` when the
deductive region collapses across the peg. A zero-gap move (overlapping
regions) is free: the price can stand still at a shared point, so there is
no forced repricing and nothing to pump. A positive gap is extracted by
flow at up to the gap per share, against the war chest — and the war chest
is not constant: **world-uniform extraction (cash) and settlement
vindication both recharge it**, which makes the growth against unbounded
gap-paths compounding, not linear.

### The revision pump (W3, `TestW3RevisionPump`)

`K` alternating `[1/10, 1/5]` and `[4/5, 9/10]`: an adaptive pump buys near
1/5 and sells near 4/5, extracting world-uniform cash at 0.4–0.8 per unit —
the **set gap** 3/5 up to price-impact dips, not the Hausdorff distance
7/10. Its worst-pattern worth compounds: 1.02 → 3.10 → 7.17 → 15.06 across
four cycles (the last cycle's extraction exceeds twice the first — the
dispatched *linear in total variation* rate is thereby **refuted as
stated**: it is correct exactly for throttle-pinned constant flow, verified
in the companion fixture, and beaten by any pump that redeploys its realized
cash). The exploitation shape is explicit — floored below at `−B`,
world-uniformly unbounded above — so skeleton Theorem 4.4's contrapositive
applies: this schedule cannot be enforced by *any* criterion-preserving
construction. The full motion-tagged decomposition (settlement-forced /
certificate-backed / residual motion) remains the named follow-up.

### The two probes (`TestDiachronicProbes`)

- **Bounded gap-sum**: thin regions jumping by `4^-k`, margins maintained —
  the pump extracts essentially nothing and the enforcer stays within a
  small constant. With gaps `g_k` and entry margin `m`, the compounding
  closes: the war chest grows by at most the factor `Π(1 + g_k/m)`, finite
  when `Σ g_k` is.
- **Frequency without gap is FREE**, not merely cheap: daily alternation
  between the overlapping bands `[2/5, 1/2]` and `[1/2, 3/5]` gives the
  pump nothing at all (its gains stay under the slack), because the shared
  point 1/2 lets the peg never move. Frequency alone cannot drive
  divergence; only gap-crossings are billable. This corrects the
  path-length picture in the direction the addendum anticipated.

### Settlement surprise (W4, `TestW4SettlementSurprise`) and the exhaustiveness verdict

Three sequential episodes, each an interior-margined peg `[2/5, 3/5]` on a
sentence that settles false at episode end; one adversary, one war chest
(`B = 1/2`), shorting the live episode's coordinate at half-throttle.
Per-episode enforcer losses at the surviving world: **0.159 → 0.369 →
0.475** — increasing, because each settlement vindicates the shorts, the
worst-case worth improves, and the recharged chest funds more flow; the
adversary is never shut off, and the stream diverges linearly at minimum.
The surprise term is exactly *inventory × entry mispricing*: each episode's
loss equals the enforcement coefficients weighted by their entry prices,
within the allowance (asserted). Prompt settlement-tracking (region moves
to the settled face) is free beyond that term; delaying the move three days
adds a strictly positive W1-type bleed per delayed day (asserted). On
schedules confined to never-settling coordinates the whole term vanishes:
the same stream without settlement obeys the single T2 bound globally.

**Exhaustiveness: recommendation (b).** W4 is the diachronic class
*correctly generalized*: the defect is a motion of the pair
`(K_n, K^D_n)` — the deductive region collapses across a stationary peg,
which is the same billable gap-crossing as a region jump, measured as
`dist(K_n, K^D_{n+1})`, with the extra twist that the crossing also
*vindicates* the opposing flow (recharge). Option (a), a third class, is
unnecessary: every W4 assertion follows from the pair-path functional plus
the recharge mechanism already needed for W3's compounding. Option (c),
reduction to per-day relative geometry, fails: the fixture is
geometrically perfect on every single day, and no single-day functional
sees the bill — the loss is realized exactly at a transition. The
anti-settlement pole W1 (`TestW1AntiSettlement`) is the degenerate extreme
of the same class: a *permanent* pair-gap (`dist(K_n, settled face) ≥ 7/10`
forever), billed linearly by riskless flow that no plausible world
penalizes — with the exploitation shape explicit, so divergence is again
Theorem-4.4-forced rather than a defect of this construction.

---

## Part III — Synthesis: the single-coordinate trichotomy

*Paper-facing prose for skeleton §6; the maintainer may adapt. Conditional
on the model results above; nothing here is registered.*

> **Candidate Theorem (single-coordinate affordability trichotomy).** Let
> `(Φ, K̄, δ̄)` be a constraint schedule on a single sentence `φ` relative
> to a deductive process `D̄`, enforced by `ConstraintCompiler` inside the
> `LIA` recursion, with opposing flow generated by the TradingFirm's
> budgeted components (aggregate war chest `W`). Write `V_n ⊆ {0, 1}` for
> the day-`n` plausible values of `φ`, `m_n = dist(K_n, V_n \ K_n)` for the
> day's plausibility margin, and
> `g_n = max(dist(K_n, K_{n+1}), dist(K_n, conv V_{n+1}))` for the day's
> pair-gap. Then:
>
> 1. **(Absorbed.)** If `V_n ⊆ K_n` for all `n`, the enforcement trader has
>    zero lifetime liability. *(Skeleton Theorem 4.6; cited.)*
> 2. **(War-chest-affordable.)** If `inf_n m_n = m > 0` on the contested
>    days, `Σ_n g_n = G < ∞`, and the far-side entry stays bounded away
>    from the billing vertex, then lifetime liability is finite and
>    tolerance-free: at most
>    `W · C(geometry) · Π_n (1 + g_n/m) + Σ_n 2^-n/m`, where `C(geometry)`
>    is the far/near ratio of the peg (for a fixed interior region
>    `[lo, hi]`, `C = hi/(1−hi)` against short flow). The bound does not
>    mention the tolerance schedule.
> 3. **(Criterion-forced.)** If the schedule admits a plausibly-uniform
>    income channel — a permanently excluded settled value (`m_n ≥ m` on
>    the dead side for infinitely many `n` after settlement), an unbounded
>    pair-gap path (`Σ g_n = ∞` with entries bounded away from the
>    vertices), or an infinite stream of vindicating settlement crossings —
>    then some budgeted component's assessments are bounded below and
>    unbounded above on plausible-at-horizon worlds, so by Theorem 4.4's
>    contrapositive **no** market enforcing the schedule preserves the
>    Logical Induction Criterion; divergence is forced for every
>    construction, not a failure of this one.
>
> The boundary between 2 and 3 is quantitative in two places: as
> `inf m_n → 0` liability grows as `1/m` (both through the war-chest term
> and through the MarketMaker allowance term), and as the gap-path partial
> sums grow, liability compounds at the factor `Π(1 + g_n/m)` because both
> world-uniform extraction and settlement vindication replenish the
> opposing war chest.

*Proof-sketch elements, each carried by a model fixture:* fixed-point
flow-inventory identity (T2 mechanism assertion); throttle conversion
`flow ≤ chest/margin` (G1 semantics, floor lemmas); spread revenue against
matched churn (T2 iv); gap extraction at set-gap rate with compounding (W3,
probes); vindication recharge (W4); exploitation shapes for the forced pole
(W1, W3); allowance term `2^-n/margin` (W2 accounting).

## Tier 4 — the surviving identity

The dispatched biconditional survives with three repairs, each pinned by a
fixture (`TestTier4Identity`):

> **Surviving identity (model form).** Over a support-locally nested
> assessment (the deductive case), the enforcement trader has bounded
> lifetime liability **iff** no component *and no coalition of components*
> achieves cumulative value against the enforcement trades that is bounded
> below and unbounded above uniformly over **plausible-at-horizon** worlds.

- *Forward:* the ledger conservation inequality — the summed cumulative
  value of all traders is at most `Σ 2^-n` at every table — caps every
  coalition's upside by the enforcer's downside plus slack; coalitions are
  handled at no extra cost, which answers the individual-vs-ecology
  quantifier.
- *Reverse:* each divergence witness carries its exploiter explicitly (W1,
  W3), floored by the budgeter and unbounded above at horizon-live worlds.
- *The required attack succeeds against the per-day quantifier and fails
  against the at-horizon one:* with non-nested live sets (alternating
  singletons), a trader harvests positive income every single day, each
  day's income trivially uniform on that day's live set, while every
  horizon assessment stays near zero and enforcement liability stays
  bounded — per-day-uniform income never becomes horizon upside. Under
  support-local nesting the attack is impossible: the live sets shrink, so
  day-uniform income is horizon-uniform (checked exhaustively on the W4
  schedule; the general argument is one line from the `nested` field of
  the `Assessment` interface). The identity therefore needs at-horizon
  plausibility *and* nesting; for deductive processes nesting is free.

## Model honesty notes

Findings about the pinned semantics and the model that the reader needs:

1. **Exact-touch shutoff.** The budgeter's loss cap permits a trade that
   consumes the available capital exactly; the realized worth then sits at
   `−b` and the shutoff test (`≤ −b`) fires permanently on the next day. A
   maximally aggressive component gets one full-throttle day and dies.
   Every surviving attacker in this round self-throttles at half capital;
   the war-chest-to-flow conversion in the bounds carries a corresponding
   constant factor.
2. **Honest `A_n` for adaptive flow.** Proposition 3.1's `A_n` bounds the
   firm's day strategy; for a component whose flow scales with realized
   wealth, the bound grows with the wealth. Freezing `A_n` while the flow
   grows understates `λ_n` and lets the attacker's own price impact eat the
   spread being measured — a modeling error we made and corrected, worth a
   sentence in the paper's §6.
3. **The guarantee is one-sided.** `MarketMaker` bounds the combined value
   *above* only; money-burning fixed points (net imbalance costing all
   traders) are conforming, and near a vertex the tolerated imbalance is
   `2^-n/p`. This is the source of the allowance term at `1/margin` in W2
   and of nonzero slack everywhere; all bounds in this memo carry it
   explicitly.
4. **Same-day state discipline.** All day strategies are functions of the
   pre-day state and the returned price state; the model computes every
   realized trade before executing any (an execution-order leak here
   initially produced phantom enforcement inventory — caught by the W3
   accounting, fixed, and the suite re-run green).
5. The model's MarketMaker searches for *a* conforming price state and
   verifies the guarantee exactly at every cube vertex; it does not claim
   to reproduce the LIA fixed point, only the postulate the skeleton
   actually uses. Early days have large allowances (`2^-1`, `2^-2`, …), and
   several fixtures' realized numbers show it.

## What is not established

No claim is registered; nothing here is kernel-checked, and no Lean
statement was attempted (nothing fell out in under an hour against the
Contrib modules). The model theorems are exact finite computations on
one-coordinate (and one two-coordinate) fixtures with specific attackers;
the trichotomy is a candidate statement whose general proof (arbitrary
budgeted ecologies, arbitrary rational polytopes, multi-coordinate
cross-subsidy) is not given. The identity's forward direction uses the
model's ledger conservation, which in the full construction corresponds to
summing MarketMaker bounds — stated, not proved, beyond the finite runs.
Out-of-scope items were not attempted: multi-coordinate cross-subsidy
closure beyond G2, the motion-tag TV/surprise interaction, reason-state or
frontier connections. The two-defect taxonomy's exhaustiveness is argued
relative to the fixture classes prosecuted here, not proved as a theorem
over all schedules.

## Naming

Provisional, queued in `DECISIONS.md`, coined only where the dispatch asked:
**plausibility margin** (the T3 margin notion), **opposition war chest**
(the aggregate budget quantity), the trichotomy regimes **absorbed /
war-chest-affordable / criterion-forced**, and the working terms
**set-gap path functional**, **vindication recharge**, **exact-touch
shutoff**.

Run the checks with:

```sh
python3 tests/run.py
```

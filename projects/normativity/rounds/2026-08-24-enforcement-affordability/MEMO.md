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

---
---

# Continuation: paper-1 material (C0–C3)

## Verdict

**The one-coordinate affordability theorem is true and needs a fourth
hypothesis the parent round did not state: a component recycling the
enforcer's own losses from an unconstrained coordinate makes a static,
perfectly-margined peg's liability compound geometrically.** C1's fork lands
on the negative side — the self-financing inequality does not close, and the
parameterized-chest fallback does not rescue it, because recycling refills the
war chest faster than the chest draws down. C0 is therefore stated with an
explicit no-cross-coordinate-subsidy hypothesis, and each of its four
hypotheses carries a necessity witness.

Status: **research memo; unregistered**. Executed 2026-08-25 against the round
above, whose grades and text are unchanged. Same model, same pinned inputs;
the skeleton v44 checksum and the `Contrib` file/line citations of §0 were
re-verified against this branch and all resolve. Fixtures added in
`tests/test_continuation.py`; the round's suite is 46 fixtures.

The adopted split for the traderization paper puts the general affordability
characterization — trichotomy, diachronic functionals, recharge — in a
follow-up. Paper 1 keeps the liability interface, one real nonzero-liability
theorem, and one criterion-forced impossibility. This continuation produces
those two, the lemma the first of them needs, and the two secondary remarks.

| Target | Grade |
|---|---|
| C1 aggregate-chest closure (channels a, b) | proved-in-model |
| C1 self-referential channel (c) | **fork: does not close** — `refuted (witness)` for the closed form |
| C0 one-coordinate bound under (H1)–(H4) | proved-in-model (bound); four necessity witnesses |
| C0 hypothesis necessity, each of (H1)–(H4) | proved-in-model (witness each) |
| C0′ criterion-forced impossibility | bound-with-argument (Thm 4.4 contrapositive, cited) |
| C2 Appendix D severance | proved-in-model |
| C3 converse of Theorem 4.6, qualitative | proved-in-model |
| C3 quantitative floor `m²/4(1−m)` | bound-with-argument (12 configurations) |
| Non-deductive nested spot-check | **open** — not exhibitable at finite support; see `FOLLOWUP_STOCK.md` |

## C-0. Spot-checks of the parent round

`TestParentSpotChecks`. The parent's `lifetime_liability` reads the enforcer's
deficit at the **final horizon**; Definition 4.1 takes the supremum over
**every** horizon `N` and every world live at `N`, so the parent's upper bounds
do not transfer by definition. They transfer in fact: on every parent fixture
re-run here — the T2 family at all three tolerances, T1 at two, the `{1/2}`
point peg at three — the two quantities are **exactly equal**, and a scan over
region, flow size, side and budget produced no separating instance. The
enforcer's cumulative worth is monotone along every run this model produces.
Every continuation fixture below uses the Definition 4.1 measure. No parent
grade changes; the definitional gap is real and undeveloped, and is recorded in
`FOLLOWUP_STOCK.md`.

## C1. The self-financing lemma

A component's wealth is global. Its throttle on the constrained coordinate
reads `b + prior worth at the binding live table`, and *prior worth* counts
everything the component has done, on every sentence. C0's bound is honest
only if the income channels into that quantity are closed or parameterized.

The channels, and what each is worth:

- **(a) MarketMaker slack.** Bounded by `Σ 2^-n < 1` in total, by Lemma 3.2
  summed over days. Enters every bound as the additive allowance term.
- **(b) Other budgeted components.** Bounded by the paying component's own
  floor, `−b_k` (`AssessmentFirm.lean:266`). Recycling through this channel
  **redistributes** the aggregate war chest; it cannot mint.
- **(c) The enforcement trader's own losses** — the quantity being bounded.
  This is the self-referential channel, and it is the one that decides the
  shape of C0.

**Channel (b) is real and defeats the per-component reading**
(`test_patsy_income_breaks_the_per_component_chest`). Two sentences, `ψ`
settled false and unconstrained, `φ` pegged at `[2/5, 3/5]`. A patsy component
with budget `b_B` holds a downward-sloping demand for `ψ`; the attacker, with
budget `b_A = 1` **throughout**, sells `ψ` into it at the clearing price `2/5`
a day and spends the proceeds shorting `φ` at half capital. With `b_B = 64`
over 56 days the realized liability is **11.74**, against **8.50** for the T2
bound instantiated at the attacker's own war chest — the per-component form
fails — and against **0.44** for the same attacker with the harvest switched
off, a factor of 27. The patsy pays for all of it inside its own floor.

**Channel (b) closes in the aggregate**
(`test_aggregate_nominal_chest_still_caps_patsy_recycling`). At
`b_B ∈ {8, 32, 64}` the liability stays inside `(b_A + b_B)·C + slack` at every
horizon. What caps a subsidised attack is the sum of the war chests of every
component that pays into it — the parent's G2 finding, extended from
simultaneous spreading to sequential transfer.

**Channel (c) does not close, and no schedule-local bound survives it**
(`test_self_referential_recycling_compounds_and_closes_nothing`). One
component, budget `b_A = 1`, no patsy. The enforcer holds a **static,
perfectly-margined** peg `[2/5, 3/5]` on `φ` and a **moving** peg on `ψ`
alternating between `[1/10, 1/5]` and `[4/5, 9/10]`. The component pumps the
`ψ` gap for world-uniform cash — the parent's W3 engine — and spends an eighth
of its capital a day shorting `φ`. Over eight cycles:

| cycle | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| war chest | 0.301 | 0.645 | 1.078 | 1.621 | 2.302 | 3.155 | 4.226 | 5.567 |
| `φ` flow | 0.755 | 0.959 | 1.212 | 1.530 | 1.928 | 2.427 | 3.054 | 3.839 |
| `φ`-coordinate liability | 0.137 | 0.515 | 0.998 | 1.607 | 2.374 | 3.341 | 4.557 | 6.085 |

The cycle-on-cycle flow ratio stays between 1.257 and 1.270 across all seven
steps: the growth is **geometric**, not linear, and it does not decay over the
run. The component is never shut off and never breaches
its `−1` floor. The `φ` peg satisfies every geometric hypothesis one could ask
of it — constant, interior, margin `2/5`, contained in the deductive region —
and its liability is unbounded, funded entirely by the enforcer's losses on a
sentence the `φ` schedule never mentions.

**The parameterized-chest form does not rescue it as stated.** Reading `W` off
the opposition's realized cumulative drawdown at the throttling world gives
`W = 0.42`, while the liability is 21.91: recycling refills the chest faster
than it draws down, so the drawdown never sees the flow it funds. The
unconditionally true parameterization is by the **gross** capacity — budget
plus all income received at the throttling world — and under channel (c) that
quantity is itself unbounded, so the statement is true and empty.

**The discriminator**
(`test_the_discriminator_is_the_enforcers_sign_at_the_throttling_world`). The
recycling coefficient `κ` is zero exactly when the enforcement trader's
cumulative value is **nonnegative at the world that throttles the opposition**.
On a static interior peg under one-sided flow this holds structurally and is
asserted daily: the throttle binds at `W(φ) = 1` on every day of the 22-day
run, and the enforcer's cumulative value there is `≥ 0` at every horizon
(`test_throttle_binds_where_the_enforcer_profits`). The projection trade takes
the side opposite the flow, so it profits exactly where the flow loses — the
enforcer funds nothing at the world where funding would relax the throttle. On
the pumped schedule the enforcer is a net payer at a throttling world through
the `ψ` coordinate, and that is precisely where closure fails.

**The lemma, as the evidence supports it.** Let `q` be the opposition's
cumulative net position on `φ` and `m` the margin. Then
`q ≤ (Σ_j b_j + I)/m`, where `I` is the cumulative income the opposition
receives at the throttling world from outside its own budgets. `I ≤ Σ 2^-n`
when the opposing components trade only `φ` **and** the enforcer's value at
that world is nonnegative; `I` is unbounded otherwise. The schematic
`L ≤ (chest + slack + κ·L)/m` closes when `κ < m` and channel (c) is what
makes `κ` large — not by a little, but without bound.

**No repair was attempted.** Closing channel (c) requires either fencing a
component's per-coordinate capital — which contradicts the pinned Budgeter,
whose scale is one scalar over the whole day trade
(`AssessmentProcess.lean:392`, `budgetScaleFeature`) — or restricting the
schedule to firms that trade nothing else. The second is hypothesis (H4)
below; the first is a modification of the construction and out of scope.

## C0. One-coordinate affordability

*Paper-facing prose for skeleton §6; the maintainer may adapt. Conditional on
the model results above; nothing here is registered.*

> **Theorem (one-coordinate affordability).** Let `D̄` be a deductive process
> and `(Φ̄, K̄, δ̄)` a constraint schedule with `Φ_n = {φ}` for every `n`. Write
> `V_n := {W(φ) : W ∈ PC(D_n)} ⊆ {0,1}` for the day-`n` plausible values and
> `K^D_n = conv V_n` for the deductive region of Definition 5.1. Call day `n`
> *contested* when `V_n ⊄ K_n`. Set
> `Ē := ConstraintCompiler^D̄(Φ̄, K̄, δ̄)` and let `P` be the pricing sequence
> of the recursion `P_n = MarketMaker_n(TradingFirm^D̄_n(P_{≤n−1}) + E_n, P_{≤n−1})`.
> Assume:
>
> - **(H1) Containment.** `K_n ⊆ K^D_n` for every `n`.
> - **(H2) Margin.** There is `m > 0` with `dist(K_n, V_n \ K_n) ≥ m` on every
>   contested day.
> - **(H3) Stationary interior peg.** There are rationals `0 < lo ≤ hi < 1`
>   with `K_n = [lo, hi]` on every contested day.
> - **(H4) No cross-coordinate subsidy.** Every budgeted component of
>   `TradingFirm^D̄` whose day strategies are not identically zero against `Ē`
>   has support contained in `{φ}`.
>
> Then `Ē` has bounded lifetime liability relative to `D̄`:
>
> `B ≤ W · C(lo, hi) + c·Σ_n 2^-n`,  `C(lo, hi) = max( hi/(1−hi), (1−lo)/lo )`,
>
> where `W` is the aggregate budget of the opposing components — at worst the
> TradingFirm's uniform `2` of Remark 4.2 — and `c` is an absolute constant.
> **No term mentions `δ̄`.** In margin form, `C(lo, hi) ≤ (1−m)/m`, so the
> bound degrades as `1/m` and in no other way.

Under (H1) a single sentence that has settled forces `K_n = K^D_n = {the
settled value}`, so that day is uncontested; (H1) and (H3) together therefore
say **`φ` is undecided on every contested day, and the peg is interior**. That
is the whole content of "regions contained in the day's deductive region" in
one coordinate, and it is what separates this theorem from the impossibility
below.

### Proof sketch, step by step

Each step carries the fixture that verifies it in the model and the `Contrib`
lemma a Lean promotion would compose from.

1. **Day accounting.** By Lemma 3.2 the combined day-`n` strategy
   `TradingFirm_n + E_n` has value at most `2^-n` at every `[0,1]`-valuation on
   the finite support, not merely at every world.
   *Fixture:* the model's `solve_day` verifies this exactly at every vertex of
   the support cube on every day of every run; a violation raises.
   *Lean:* **none in `Contrib`** — cited from the source MarketMaker.

2. **Flow–inventory identity.** Let `c_n` be the opposition's realized `φ`-share
   coefficient on day `n` and `e_n` the enforcement coefficient. At the verified
   fixed point `|e_n + c_n| ≤ c·2^-n`. The enforcer's cumulative inventory is
   therefore the negative of the opposition's cumulative position, up to
   `Σ 2^-n`. This is the step that makes the theorem true: the *available*
   intensity `λ_n = ρ_n/δ_n²` never appears, only *realized* flow.
   *Fixture:* `TestT2ContestedInteriorPeg.test_i_maximal_flow_short`;
   `TestT2viPointPegAdjudication.test_center_point_peg_is_affordable_uniformly_in_delta`.
   *Lean:* **none.**

3. **Throttle conversion.** Each opposing component `j` is a budgeted trader
   with budget `b_j`, whose cumulative net worth at every world live on every
   day is at least `−b_j`. Under (H1)+(H3) the world `W(φ) = 1` is live on every
   contested day. A component holding `q_j` shares short, acquired at prices at
   most `hi`, has value at most `−q_j(1−hi)` there. Hence
   `q_j ≤ b_j/(1−hi)`. Symmetrically for long flow with `lo` and `W(φ) = 0`.
   *Fixture:* `TestC1SelfFinancing.test_throttle_binds_where_the_enforcer_profits`;
   `TestG2Aggregation`.
   *Lean:* `AssessmentProcess.lean:704` (`budgetedTrader_netWorth_floor`) for
   the global floor; `:653` (`BudgeterAt_value_ge_neg_available`) for the
   per-day form; `:628` (`budgetScaleFeature_denote_le_lossCap`) for the scale.

4. **Aggregation without netting.** Summing step 3 over components gives
   `q ≤ W/(1−hi)` with `W = Σ_j b_j`, independent of how the flow is spread,
   because each component's scale reads only its own realized ledger.
   *Fixture:* `TestG2Aggregation.test_floors_sum_independent_of_spread`,
   `test_confederate_gains_cannot_relax_the_throttle`.
   *Lean:* `AssessmentFirm.lean:127`
   (`tradingFirmTrader_netWorth_eq_component_sum`), `:266`
   (`componentTrader_netWorth_floor`), `:293`
   (`tradingFirmTrader_netWorth_floor`).

5. **Billing.** By step 2 the enforcer's inventory is long `q`, acquired at
   prices at most `hi`. At the billing world `W(φ) = 0` its cumulative value is
   at least `−q·hi`, hence at least `−W·hi/(1−hi)` by step 4.
   *Fixture:* `TestT2ContestedInteriorPeg` (i)–(v);
   `TestC0ParameterizedBound.test_bound_holds_and_is_tolerance_free_under_self_containment`.
   *Lean:* **none.**

6. **Allowance.** Accumulating step 1's per-day slack gives the additive
   `Σ 2^-n` term. Near a vertex at price `p` the day-`n` guarantee tolerates a
   net imbalance of `2^-n/p`, so the allowance itself is billed at `1/margin`.
   *Fixture:*
   `TestT2viPointPegAdjudication.test_near_vertex_point_pegs_blow_up_at_rate_one_over_margin`;
   `TestC0ParameterizedBound.test_margin_controls_the_bound`.
   *Lean:* **none.**

7. **Closure of the income channels (C1).** By (H4) the opposition trades only
   `φ`, so its only income at the throttling world is from `Ē`'s own `φ`
   position and the day allowance. By step 2 that position is opposite the
   flow, hence nonnegative at the throttling world. The `b_j` of step 3 are
   therefore the nominal budgets, not budgets-plus-income.
   *Fixture:* `TestC1SelfFinancing.test_throttle_binds_where_the_enforcer_profits`,
   `test_the_discriminator_is_the_enforcers_sign_at_the_throttling_world`,
   `test_aggregate_nominal_chest_still_caps_patsy_recycling`.
   *Lean:* **none** — the sign fact is a property of the projection trade, not
   of the Budgeter.

8. **Tolerance-freedom.** `δ̄` enters only through `λ_n`, which step 2 shows is
   an available and not a realized quantity. No term of the bound mentions it.
   *Fixture:* `TestT2ContestedInteriorPeg.test_v_tolerance_independence`;
   `TestC0ParameterizedBound.test_bound_holds_and_is_tolerance_free_under_self_containment`.
   *Lean:* **none.**

**Steps with no existing Lean support: 1, 2, 5, 6, 7, 8.** Everything the
`Contrib` modules currently carry is the budgeting side — steps 3 and 4. The
market side (the MarketMaker guarantee, the projection trade and Lemma 2.3,
the fixed-point flow–inventory identity, the billing geometry) has no
counterpart there, and a Lean promotion of this theorem would have to build it.
Step 2 is the load-bearing gap: it is the only step that is not either pure
convex geometry or an instance of a floor lemma, and it is the one the paper's
own §6 accounting most needs stated as a lemma.

### Necessity of each hypothesis

Each is witnessed, so none is decoration.

| dropped | witness | what happens |
|---|---|---|
| (H1) | `TestW1AntiSettlement` (parent) | peg excludes the settled value; riskless flow no plausible world bills; linear divergence |
| (H2) | `TestT2viPointPegAdjudication.test_near_vertex_point_pegs_blow_up_at_rate_one_over_margin` (parent) | `K = {ε}` inside `K^D`; liability at rate `1/margin` |
| (H3) | `TestW3RevisionPump` (parent) | region motion pumped at the set-gap rate; compounding |
| (H4) | `TestC1SelfFinancing.test_self_referential_recycling_compounds_and_closes_nothing` (this continuation) | static perfectly-margined peg; liability geometric in the cycle count |

### The impossibility half

*Paper-facing; promotes the parent's W1 witness to a skeleton-facing statement.*

> **Proposition (criterion-forced divergence).** Let `D̄` decide `φ` true at
> stage `n₀`, and suppose the schedule satisfies `K_n ⊆ [0, 1−μ]` for all
> `n ≥ n₀`, with `μ > 0`, and `δ_n ≤ μ/2` for all large `n` — that is, `K_n`
> persistently excludes the settled value by a margin, violating (H1). Let `T`
> be the trader buying one `φ`-share on each day `n ≥ n₀`. Then for every `N`
> and every `W ∈ PC(D_N)`,
>
> `W(Σ_{n≤N} T_n(P)) ≥ (μ/2)(N − n₀) − c₀`,
>
> bounded below and unbounded above, so `T` — which is efficiently computable —
> exploits `P` relative to `D̄`. By the contrapositive of Theorem 4.4, `Ē`
> does **not** have bounded lifetime liability, for **any** enforcement trader
> realizing the schedule. Divergence here is a property of the schedule, not a
> defect of `ConstraintCompiler`.

*Proof sketch.* After `n₀` the only plausible world has `W(φ) = 1`. Theorem 3.4
gives `dist(P_n|_{Φ_n}, K_n) ≤ δ_n`, so `P_n(φ) ≤ 1 − μ + δ_n ≤ 1 − μ/2`. Each
day's trade has value `1 − P_n(φ) ≥ μ/2` at that world, and the same at every
world plausible at any later stage, since `D̄` is nested. Summing gives the
displayed bound; boundedness below is the finite prefix before `n₀`. ∎

*Fixture:* `TestW1AntiSettlement.test_linear_divergence_and_exploitation_shape`
(parent) — the exploiter is exhibited, never throttled, never shut off, with
enforcer liability at least `days/2 − 2` and the exploitation shape asserted
directly. *Lean:* `AssessmentProcess.lean:217` (`exploits_ofDeductiveProcess`)
identifies the generalized criterion's assessment set with LI exploitation
relative to `D̄`, so the exploitation shape is stated in the right terms;
Theorem 4.4 itself has **no** `Contrib` counterpart and is cited.

### The worked example pair

For the section's illustration, two point pegs on an undecided `φ`, both with
`K_n ⊆ K^D_n = [0,1]`, differing only in where the point sits.

**`K = {1/2}` is affordable, uniformly in the tolerance.** Against maximal
short flow with war chest `1` over sixteen days, the realized lifetime
liability is `15/64`, `0` and `35/64` at `δ_n = 1/2`, `1/n` and `2^-n` — all
inside the `Σ2^-n` allowance of one another, against a homothetic-core
prediction growing like `4^16`. The margin is `1/2`, `C = 1`, and the bound is
`W + slack`. *Fixture:*
`TestT2viPointPegAdjudication.test_center_point_peg_is_affordable_uniformly_in_delta`.
What the homothetic core detects at the centre is a **revenue** property, not a
solvency one: against matched churn the interval `[2/5, 3/5]` earns its width
as spread and the point peg earns nothing, and neither goes insolvent
(`test_zero_width_earns_no_spread_against_churn`).

**`K = {ε}` blows up as `1/margin`.** Same construction, buyer flow `1`, war
chest `1/4`, tolerance `1/16`:

| `ε` | realized liability | `B(1−ε)/ε` |
|---|---|---|
| 1/4 | 1.119 | 0.750 |
| 1/8 | 4.770 | 1.750 |
| 1/16 | 10.939 | 3.750 |

Each halving of `ε` better than doubles the liability; the excess over the
war-chest term is accounted exactly by the allowance term `Σ2^-n/ε`, which is
the second place the margin is billed. *Fixture:*
`TestT2viPointPegAdjudication.test_near_vertex_point_pegs_blow_up_at_rate_one_over_margin`
and `TestC0ParameterizedBound.test_margin_controls_the_bound`.

The pair isolates the disagreement between the two accounts to the centre of
the interval, which is where the parent round adjudicated it, and shows the
`1/m` rate of the theorem's `C(lo, hi) ≤ (1−m)/m` at the vertex.

## C2. Appendix D: what Theorem D.1's hypothesis buys

*A self-contained subsection the maintainer may adapt into Appendix D.*

Theorem D.1 replaces `PC(D_n)` by a sequence `L̄ = (L_1, L_2, …)` of world
sets under two hypotheses: each `L_n` lists exactly the restrictions it
realizes on each finite support, and **every world in `L_{n+1}` agrees, on
every finite support, with some world in `L_n`**. The second is not
bookkeeping. It is what keeps liability and exploitation the same question.

Without it the correspondence severs, and the witness is explicit
(`TestC2AppendixD.test_day_uniform_income_never_becomes_horizon_upside`; the
parent's `TestTier4Identity.test_non_nested_live_sets_break_the_per_day_quantifier`
is the same construction). Take a single undecided sentence, `K = {1/2}`, and
let the live sets alternate between the two singletons: `L_n = {W(φ) = 0}` on
odd days and `{W(φ) = 1}` on even. A trader that sells on odd days and buys on
even banks a positive income on **every** day, uniform on that day's live set
by triviality — at least `1/8` a day, so at least `2` over sixteen days — while
its cumulative worth at every horizon's live world stays within `1` of zero and
the enforcer's liability stays inside `1 + Σ2^-n`. Day-uniform income never
becomes horizon upside. A liability bound therefore certifies nothing about
exploitation, and the criterion-preservation argument of Theorem 4.4 has
nothing to bite on.

The agreement condition is exactly what this violates, and the model checks it
directly: on the alternating sequence it fails at every day
(`test_alternating_singletons_violate_the_agreement_condition`), and on a
nested settlement schedule over three sentences it holds at every day
(`test_the_settlement_stream_satisfies_it`), both by exhaustive enumeration
over sub-supports. Under the condition the live sets can only shrink on each
finite support, so a day trade whose value is constant on the day's live
restrictions has that same value on every later horizon's — and the ledger
conservation inequality then caps every coalition's upside by the enforcer's
downside plus slack. For a deductive process the condition is free: `D_n ⊆ D_{n+1}`
gives `PC(D_{n+1}) ⊆ PC(D_n)` outright.

So the one paragraph the appendix needs: **nesting is what makes bounded
liability a statement about exploitation rather than about arithmetic.** It
buys the promotion of per-day uniformity to horizon uniformity, and that
promotion is the only route from a downside bound on one trader to the absence
of upside for every trader.

## C3. Converse of Theorem 4.6

Theorem 4.6 gives zero lifetime liability when every plausible world's payoff
vector lies in `K_n`. The flow-quantified converse holds in the model.

> **Remark.** For a single-sentence schedule on an undecided `φ` with
> `K_n = [lo, hi]` constant, the enforcement trader has zero lifetime liability
> against **every** budgeted opposing component if and only if every plausible
> payoff pattern lies in `K_n`. The forward direction is Theorem 4.6; for the
> converse, an excluded plausible value at distance `m` from `K_n` is extracted
> by any sustained budgeted flow toward it, forcing liability at least
> `(absorbed inventory)·m > 0`.

Both directions are checked. Absorption gives **exactly** zero — not merely
small — at every flow size tested, both for `K = [0,1]` with `φ` undecided and
for `K = [0,1/2]` with `φ` settled false
(`TestC3ConverseOfTheorem46.test_absorbed_patterns_give_exactly_zero_liability`,
`test_absorbed_after_settlement_gives_exactly_zero`). Exclusion forces strictly
positive liability in all twelve configurations tested — margins
`m ∈ {1/5, 3/10, 2/5, 1/2}` against flows `F ∈ {1/8, 1/4, 1/2}` — and the loss
is `(inventory)·m` to within the slack
(`test_an_excluded_plausible_pattern_forces_positive_liability`,
`test_the_forced_loss_is_inventory_times_margin`).

The quantitative floor is **uniform in the flow size**: every configuration
satisfies `L ≥ m²/4(1−m)`. That the floor does not improve with flow is not an
artifact — liability *decreases* in `F` across the scan, because a larger flow
trips the budgeter's throttle sooner and buys less total inventory. The
qualitative biconditional is `proved-in-model`; the particular closed form
`m²/4(1−m)` is fitted to twelve points and is graded `bound-with-argument`.

## What this continuation does not establish

Nothing here is registered or kernel-checked, and no Lean statement was
attempted; six of C0's eight steps have no `Contrib` support at all, and the
promotion table says which. C0 is proved in the model for the specific attacker
classes of the parent round plus this continuation's two recycling families, on
one- and two-coordinate fixtures with a stationary rational interval peg; the
general statement over arbitrary budgeted ecologies and arbitrary rational
polytopes is not given. (H4) is stated as a hypothesis because C1 shows it
cannot be removed, not because the general cross-subsidy behaviour is
understood — the multi-coordinate joint-margin question is the follow-up
paper's, and this round did not develop it. C0′ rests on Theorem 4.4, cited and
not re-proved, and on Theorem 3.4 for the price bound; the model realizes a
much tighter price than `δ_n` there and the proposition does not use that. C3's
converse is checked over twelve configurations at one peg family, and its
closed-form floor is a fit. The Appendix D subsection establishes the severance
and the agreement condition's role by witness and by exhaustive check on two
schedules; it does not prove Theorem D.1. The non-deductive spot-check C2
allowed for was **not performed and is not performable in this model** — at
finite propositional support every finite table list is the plausible-world set
of some finite sentence set, so the deductive and Appendix D cases cannot be
separated by the live sets themselves; the separation lives in the *sequence*
condition, which is what the alternating witness exercises. That is recorded,
undeveloped, in `FOLLOWUP_STOCK.md`.

## Naming

Provisional, queued in `DECISIONS.md`, additional to the parent round's list:
**self-financing lemma** (the C1 statement), **recycling coefficient** (the
`κ` of the schematic bound), **cross-coordinate subsidy** (hypothesis (H4)'s
negation), **throttling world** and **billing world** (the two worlds of the
step-3/step-5 accounting), and **gross capacity** (budget plus income received
at the throttling world).

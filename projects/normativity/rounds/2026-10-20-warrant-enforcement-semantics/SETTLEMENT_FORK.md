# Part B — the fork: what the security settles against

All Lean names are in `Workspace.Normativity.Contrib.WarrantEntitlement`. The exact numbers
are recomputed by `tests/run.py` from `src/fixture.py`.

## The fixture

| | |
|---|---|
| fragment | `X, X∧A, X∧A∧Y, Y` on atoms `X, A, Y`; six distinct payout vectors (`A` is invisible when `X` is false) |
| warrant | one occurrence, three rows: `P(X) ≥ c_P`, `P(X∧A) ≥ c_A P(X)`, `P(X∧A∧Y) ≥ c_S P(X∧A)` |
| strengths | `c_P = 4/5`, `c_A = 3/4`, `c_S = 2/3` |
| odds | `4, 3, 2`; `ρ = 4` |
| bankroll | `B = 3ρ = 12` |
| intensity | `β = 10` on every row (the bound does not read it) |
| `n₁ = 3` | `X` settled true |
| `n₀ = 5` | the applicability port defeated |
| `n_E = 8` | the evaluation of `Y` lands (`Y` or `¬Y`, a typed input) |

Gaps (surplus if positive, deficit if negative) of the three rows at the eight worlds:

| world `(X, A, Y)` | premise | applicability | strength |
|---|---|---|---|
| `(1,1,1)` all true | `1 − c_P = 1/5` | `1 − c_A = 1/4` | `1 − c_S = 1/3` |
| `(1,1,0)` | `1/5` | `1/4` | `−c_S = −2/3` |
| `(1,0,·)` | `1/5` | `−c_A = −3/4` | `0` |
| `(0,·,·)` | `−c_P = −4/5` | `0` | `0` |

Each row has exactly one deficit pattern and its deficit is its strength; the all-true world
clears every row with surplus `1 − c_j`. `Fixture.gap_dominated`: for every propositionally
consistent world `w` and every row, `−gap(w) ≤ ρ · gap(all-true)` with `ρ = max_j c_j/(1 − c_j)`,
and `ρ` is the least such factor (`minimal_rho`).

## The bankroll theorem

The enforcer is the force layer's compiled position on the day's presentation
(`warrantEnforcer sched`, `action n _ := enforcementStrategy (sched n) n`). Writing
`u_{t,j} = β_{t,j} · g_{t,j}(p_t)` for the units it holds on row `j` at date `t` (intensity times
violation at the displayed price), its value at a world `w` on date `t` is

    V_t(w) = Σ_j u_{t,j} · gap_{t,j}(w) + Σ_j β_{t,j} g_{t,j}(p_t)²          (`day_value_eq`)

— the units-weighted signed gaps plus a nonnegative square term. Hence `V_t(w) ≥ Σ_j u_{t,j} gap_{t,j}(w)`
(`day_value_ge`). Now fix a date `n`, a live world `v'` and the live world `w` to be bounded,
and suppose for every `t ≤ n` and every enforced row `−gap_{t,j}(w) ≤ ρ · gap_{t,j}(v')`. Then

    netWorth_n(v') ≥ Σ_{t ≤ n} Σ_j u_{t,j} gap_{t,j}(v') =: S_n                 (`slackMass_le_netWorth`)
    netWorth_n(v') < 1 + 2 = 3                                                 (`enforcer_netWorth_lt_three`)
    netWorth_n(w)  ≥ −ρ · S_n ≥ −3ρ                                            (`netWorth_ge_neg_odds`)

The middle line is the market maker's constant at every propositionally consistent world
(the dependency's `marketMaker_netWorth_lt_one`) plus the trading firm's floor at every live
world (`AssessmentFirm.tradingFirmTrader_netWorth_floor`, `−2`), through
`realizedAggregate_netWorth`. Nothing else enters: not `β`, not `δ`, not `n`, not the number
of rows. `liability_of_odds` is the `∀ n v, Live n v → −3ρ ≤ netWorth` form, and
`warrant_normative_inductor` is `Evaluation.conditional_normative_inductor` at the warrant
enforcer with `B = 3ρ` and that hypothesis discharged.

**Why a constant where the force interface has a sum.** The interface's certificate
`Σ_t (ε_t + C_t) D_t / δ_t` bounds each date's worst live loss and adds; the odds argument
follows one world `w` across dates and pays for its total deficit with the surplus the same
trades earn at `v'`, which the market's capital caps once. Item 40's text names exactly this
distinction ("the criterion follows a single world across dates").

**What a counterparty can afford.** `src/fixture.py::budgeted_seller_run` runs a seller of
`X` against the premise row at `β = 10`, selling `1/2` a day while a budget of `3` at the
slack world (`X` true) allows; the maker zeroes the aggregate at `p = c_P − k/β = 3/4`. It
sells `12` units over `24` dates and stops; the enforcer's book at the deficit world is
`−9 = −3 · odds(3/4)`, under `budget · odds(c_P) = 12`. At `β ∈ {1, 10, 1000}` and budgets
`1, 3` the realized liability never passes `budget · odds(c_P)` (`tests/test_fixture.py`).

## (i) Deductive settlement

The dispatch's (i) is the world-inclusive case: every plausible world satisfies every row.
Then every gap at every live world is `≥ 0`, every day's value is `≥ 0`
(`netWorth_nonneg_of_inclusive`), `B = 0`, and the warrant said nothing the deductive process
had not already proved: a logical fact wearing a strength. In the Lean of record this is the
hypothesis `hadm` of `compiled_end_to_end` and `deductive_normative_inductor`
(`DeductiveEffective.deductive_end_to_end` has no region input at all; its region is the
plausible worlds' own). **A genuine warrant fails `hadm`** — the premise row alone excludes
every `X`-false plausible world as a point — and that is the boundary of the deductive case.

For the genuine warrant under deductive settlement of `X` at `n₁`: the all-true world is
plausible at every date (`Fixture.allTrue_live` with the evaluation affirming, or
`allTrue_live_before` before any evaluation), so `Fixture.liability` gives `−3ρ = −12` at
every live world at every date, for every `n₀, n₁`. Settling `X` kills the premise row's
deficit worlds and changes nothing in the bound. If deduction later proves `X∧A∧Y`, the
rows become world-inclusive and the enforcer's account from then on only gains.

> **Superseded 2026-10-21.** The readings of (ii) and (iv) below that rest on the region
> *emptying* at a disagreeing evaluation (`disagree_region_empty`, "force is withheld") and on
> the premise row guarding the chain are superseded by rebuttal by settlement
> (`DECISIONS.md`, 2026-10-21, M1–M3): the strength row is rebutted and leaves, the region
> stays nonempty, and the bankroll across the rebuttal is `3ρ(2 + ρ)`. See
> `../2026-10-21-rebuttal-and-end-to-end/REBUTTAL.md`. The orphan pin of (iv) stands as the
> countermodel to the port-only rule.

## (ii) Evaluation settlement

`Y` is settled at `n_E` by a declared evaluation `e`; in `Fixture.stage` the evaluation's
verdict enters the stage as `Y` or `¬Y`, the same way a deduced sentence does. The
assessment process does not know where a settled sentence came from.

- `e = true`: `Fixture.liability`, `−3ρ` forever.
- `e = false`: before `n_E` the all-true world is live and the bound is `−3ρ`; at `n_E`
  the settlement pins `X = 1`, `Y = 0`, `X∧A∧Y = 0`, and with the applicability row live the
  chain `P(X∧A∧Y) ≥ c_S P(X∧A)`, `P(X∧A) ≥ c_A P(X)`, `P(X) = 1` forces `c_A ≤ 0` —
  **the region is empty** (`Fixture.disagree_region_empty`), force is withheld (the
  interface's default), and the account is frozen at its `n_E − 1` value, which was bounded
  at every world live then, a superset of the worlds live later
  (`Fixture.liability_disagree`, through `netWorth_eq_of_tail_zero` and
  `ofDeductiveProcess_nested`). Same `B = 3ρ`.

**Does enforcement assume the normative conclusion?** No. The only working `B` presupposes
nothing about what the evaluation says; it presupposes that the world agreeing with the
warrant is live until the evaluation lands — that the counterparties who bet against the
warrant are budgeted against that world. The disagreement is then a realized loss of at most
`B`, paid, not a failure of the criterion. The dispatch's "unbounded if the evaluation is
unconstrained by the warrant" is refuted on the fixture: `liability_disagree` holds for the
evaluation most hostile to the row. What *would* be unbounded is an evaluation foreknown by
traders while the agreeing world is still assessed as live — a transparency failure of the
settlement channel, not a property of this round's objects.

## (iii) Pegged, no settlement

In the pinned substrate every `PCWorld` assigns `Y` a value; "no payoff event" is "both
values stay live forever", which is (ii) with `n_E` beyond every date. The all-true world is
live forever, `Fixture.liability` applies at every `n`, and **every clause of the criterion
survives**: `warrant_normative_inductor` gives `L.IsLogicalInductor (history L (warrantEnforcer sched))`
under the same two remaining hypotheses (`computableMarket`, the uptake certificate) as the
conditional theorem. No clause fails on any trader. The enforcer's securities "never
settle" only in the sense that no date ever removes a `Y`-world from assessment; its account
is assessed at both and bounded at both.

So the fork collapses in the account: (i), (ii) and (iii) are one assessment process with
three live-set schedules, and the bankroll is the same function of the strengths on all
three. The maintainer's ruling (M2) is on whether a pegged reading *outside* this substrate
is wanted; see `DECISIONS.md`.

## (iv) The defeater

At `n₀` the applicability port is defeated; its row leaves the bundle
(`defeat_widens` in the port; `rowsAt c β hβ n₀ n` drops `applRow` for `n ≥ n₀`). The
enforcer takes no new position on it. The units bought before `n₀` stay on its book — a
trader's net worth is the sum of its past trades' payoffs at the assessed world, and nothing
unwinds — so the liability incurred between entry and `n₀` is **not recovered**; it is
**absorbed by `B`**, because every date before `n₀` had the all-true world live and the
row's own share of the bound is `3 · c_A/(1 − c_A) = 9 ≤ 12`. After `n₀` the row
contributes nothing further.

The hazard the defeat creates is the round's one refutation. With the applicability row
gone, a refutation of `Y` at `n_E` (with `X` settled) **no longer empties the region**:
`(1, 0, 0, 0)` lies in it (`Fixture.orphan_region_nonempty`). The strength row with `X∧A∧Y`
pinned to `0` now reads `c_S P(X∧A) ≤ 0` — the linear row has **contraposed**: a defeasible
"if `X∧A` then probably `Y`" has become "`Y` is false, so `X∧A` is false". No live world has
positive gap on it and the live world `X, A` true, `Y` false has gap `−c_S`
(`Fixture.orphan_no_slack`). The bankroll theorem's hypothesis fails, and
`src/fixture.py::harmonic_buyer_run` exhibits the trader: buying `k_t = 1/(t+1)` units of
`X∧A` a day against the enforcer's short at the maker's price `k_t/(c_S² β)`, the buyer's loss
at the `X∧A`-false world is `Σ k_t p_t = Σ k_t²/(c_S² β) < 9/20 · (π²/6) < 0.37` while the
enforcer's loss at the `X∧A`-true world is `Σ k_t (1 − p_t) ≥ H_n − 0.37`: `−2.58` at `10`
dates, `−4.13` at `50`, `−5.51` at `200`, past every bound. The buyer is a fixed rational
schedule, efficiently computable, within any budget `≥ 1`.

Two readings, both supported by the mathematics and both filed: per-row ports are unsafe
and the defeat condition belongs to the occurrence (item 112); and a strength row whose
consequent has settled should leave the region, since an inference rule has nothing to say
once its conclusion is known and a linear row cannot help contraposing (item 113).

## (v) Item 39 in its own terms

**Weak, under all three semantics.** The warrant's region `K_t` excludes live worlds as
points — every `X`-false world while the premise row is live — and adds nothing to liveness,
which is settlement's. The strong reading (`C_t ⊆ Δ(Ω_t)` with the live worlds its support)
holds exactly when every live world is in `K_t`, which is world-inclusion, `B = 0`, and the
logical case. The pair the item asks for: the point masses on `(X, A, Y) = (0, 0, 0)` and
`(0, 1, 0)` have the same payout vector `(0, 0, 0, 0)` on the fragment, hence the same
projection, and different live worlds (`same_projection_different_support`). On the four
priced sentences themselves no two distinct point masses coincide, so the exhibited weakness
is the fibre one of `SEMANTIC_PROJECTION.md` §3; the operative weakness for enforcement is
the point exclusion, which is what the bankroll pays for.

## Statement in P2's form

Conformance is the force layer's: at every date the enforced rows' violations at the
displayed price satisfy `Σ_j β_j g_j² ≤ ε + C` and so each `g_j ≤ δ` — a bounded public
defect, never `P_t ∈ K_t`. This round adds the account side: at that defect the enforcer's
assessed liability is at most `3ρ`. Neither statement is membership.

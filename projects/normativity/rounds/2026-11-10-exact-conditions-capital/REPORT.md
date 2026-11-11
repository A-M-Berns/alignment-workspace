# Report — exact conditions on a price history

| | |
|---|---|
| Prompt author | Claude Fable 5.2 (Anthropic), on the maintainer's instruction in conversation on 2026-11-10 (`prompts/2026-11-10-exact-conditions-capital/PROMPT.md`, verbatim) |
| Executor | Claude Fable 5.2 (Anthropic), in Claude Code |
| Base | `origin/main` at `ad05a981` |
| Date | 2026-11-10 |

## Result by component

| | verdict | declaration |
|---|---|---|
| A0 interface | closed | `ExactConditions.DualCertifiedMarket` |
| A1 ceiling | closed | `DualCertifiedMarket.account_le` |
| A2 preservation | closed | `DualCertifiedMarket.no_efficient_trader_exploits`; converse `account_unbounded_of_exploit`; quantitative `budgeted_netWorth_le` |
| A3 entailed conditions | closed | `DualCertifiedMarket.account_nonneg_of_entailed`, `deductive_exact` |
| A4 prefix reserve | closed | `reserve_sum_bound`, `DualCertifiedMarket.reserve_bound`, `accountBounded_of_reserve`, `account_ge_neg_odds` |
| A5 obstruction | closed, efficiency a hypothesis | `Condition.seller_netWorth_ge`, `seller_exploits` |
| A6 counterexamples | closed, efficiency a hypothesis | `tighteningFloor_seller_exploits`, `freshFloor_seller_exploits` |
| A7 conditional bridge | closed | `Bridge.bridge`, `DualCertifiedMarket.accountBounded_of_frequency` |
| A8 nonvacuity | closed | `plainMarket`, `FloorSchedule.market`, and the witnesses listed in `THEOREM.md` |
| B1 projected fixed point on a polytope | open | — (item 136) |
| B2 multipliers by duality | open | — (item 136) |
| B3 assembly | closed for one floor per day only, by another route | `FloorSchedule.exists_market` |
| Tier C | not attempted | items 137, 139 |

"Closed" is reported against the Lean declaration named. No statement of the arc was found
false. The reopening condition of each is a failure of `tests/audit_axioms.py` on its module.

## Corrections and deviations

Each change to a statement of the dispatch, and each instruction not followed as written.

1. **A0, tolerances.** The dispatch has `Σ eps_n = eps`. The interface carries `epsTotal` with
   every partial sum at most it, and `U = 2 + epsTotal`. Equality is used nowhere.
2. **A0, multipliers** are real; the dispatch does not say. Stakings of a seller (A5) are
   rational, since a strategy's coefficient is a rational constant.
3. **A0, the day inequality** is over cube valuations, as the dispatch prefers. The pinned
   lemmas support it: `fixed_point_lemma_bounded` is stated over the cube, and the market
   maker's acceptance over Boolean tables extends to the cube because a strategy's value is
   affine in the valuation (`value_le_of_bitTables`). A1–A7 read it at world payouts only.
4. **A2** uses neither exact membership nor nonnegativity of the multipliers. They are fields
   of the interface and are used from A3 on.
5. **A3.** "Regions are the deductive regions" is the hypothesis that on cube points the rows
   hold iff `DeductiveRegion.deductiveRegion` does. The deductive region is a hull of listed
   vertices; no row presentation of it is computed. Live worlds satisfy the rows of *earlier*
   days by support-local nesting, which the dispatch's sketch does not mention and the
   assessment interface requires (`Condition.holds_of_live_later`).
6. **A4, hypotheses weakened.** The sequence lemma needs the ceiling only at profiles from
   which mass is released on day `n` and, on day `N`, at the profiles other than the one
   bounded. The registered theorem keeps the dispatch's form (day-`n` mass on worlds live at
   day `n`). Days are indexed from `0`, so the witness example is the case `N = 1`.
7. **A4, the hindsight remark.** That a reserve supported on worlds live at the last day
   fails in the example is a comment in the source and is not a theorem.
8. **A4 and `OddsBankroll`.** `account_ge_neg_odds` is the constant two-point reserve and has
   the shape of `OddsBankroll.Account.netWorth_ge_neg_odds`. It is not a reduction: the force
   layer's units are intensity times violation on a `Presentation`, and no lemma here makes
   them multipliers of a dual-certified market.
9. **A5.** The history is arbitrary — no range or rationality is needed.
10. **A6, indexing.** Day `n` (from `0`) carries the level `1 − 2^-(n+1)`. (a): at least `−1`
    everywhere and at least `N` through day `N`, which is the dispatch's `N − 1` over `N`
    days. (b): the dispatch's levels `1 − 2δ_n`, `δ_n = 2^{-n-2}`, with `n` shares on day `n`;
    at least `−1` at *every* world, not only live ones.
11. **A6, efficiency** of the two sellers is left as a named hypothesis, as the dispatch
    allows. The pinned definition is a polynomial-time machine emitting the strategy's
    serialization; no attempt was made.
12. **A7.** `x n ∈ [0,1]` rather than `{0,1}`. `Y_{n−1}` is `margin n`. The frequency
    inequality is over partial sums `i < N`. The dispatch's last conclusion ("`Q_n` minus any
    sub-sum is bounded below by `−Σ mu`") is proved as: every finite sub-sum, with any
    nonnegative values in place of `x`, is at least `−c Σ' mu`.
13. **Tier B.** B1 and B2 are not proved. The dispatch's route (projection onto `K`, the
    Farkas lemma of `EconCSLib`) was not taken. For floors there is a shorter one: substitute
    `lo + (1 − lo)·price` for the day's price features in the firm's strategy and price the
    result with the unmodified `MarketMaker`. Its acceptance says each positive aggregate
    position sits at price one and each negative one at the reparametrized zero, the floor;
    the multiplier is the negative position. `floor_day_le` proves this for any lower-bound
    function; the market is assembled for one floor per day. Computability was not attempted.
14. **Tier C.** The exactness of the reserve bound and the finite-model equivalence are
    clauses of item 137; extraction is item 139. The volume bound and the almost-sure theorem
    under random observation are not filed: the dispatch does not define `H_n`, `V_n`, `η_n`,
    and nothing in Tier A carries a probability on observations.
15. **New types against old.** `Bet` duplicates `EnforcementStrategy.Row` (which carries an
    intensity and sums over a presentation's coordinates) and
    `NormativeInductorComposition.Row d` (over `Fin d`, in `≤` form); it is a trade list, so
    that selling it is a strategy. `Condition` duplicates a schedule of `Presentation`s or
    `Bundle`s for the same reason. `FloorSchedule` is not a `RationalConstraintSchedule`,
    which gives its regions by vertices. `FarkasCert`, `SeedStatics`, `WarrantEntitlement` and
    `EnforcementPreservation` are not used.
16. **Site.** `state/prs.json` records merged pull requests; no entry is added.
    `state/concepts.json` would need a judgment on which concept this bears on; skipped.
17. **Tooling.** `checkers/graph.py` was run with `python3.12`; the machine's `python3` cannot
    parse it. The handle `@claude-fable-5-2` is added to `graph/policy.yaml`, as the map's
    protocol derives it from the model, and to the handle set a unit test pins
    (`checkers/tests/test_graph.py`, one literal). That file is under `checkers/`; the edit is
    recorded in the round's `DECISIONS.md` entry and is the one change outside the dispatch's
    stated surfaces.
18. **Wiki.** `wiki/Normativity.md`'s bound count of registered normativity claims is moved
    from 88 to 96, which `checkers/wiki_state_bindings.py` requires. No other wiki edit.

## What was found

The statements of Tier A hold as dispatched, with the adjustments above. Three facts were not
in the dispatch.

**Preservation needs only the day inequality.** `no_efficient_trader_exploits` follows from
the summed day inequalities and dominance; that the prices lie in the region plays no part.
Membership is what makes the multipliers a seller's staking (A5) and what the reserve bound
averages against (A4).

**Floors need no duality.** A lower bound on a price is a change of variable on that price,
and the market maker already solves the changed problem. The multiplier is read off the
fixed point rather than obtained from a separation theorem.

**The same schedule shape lands on both sides.** Fresh atoms, each settled true the next day:
at levels `1 − 2^-(n+1)` every compliant history is exploited (`freshFloor_seller_exploits`);
at a constant level `c < 1` the floor market is unexploited and its multipliers are summable
(`constantFresh_unexploited`). In the first the staking `n` has account bounded above by `1`;
in the second the bridge applies because every realized value is one.

## What this round does not establish

- No exactly compliant market for a region other than one floor per day.
- No computable market: every `IsLogicalInductor` conclusion is conditional on
  `ComputableMarket`, which is inhabited for no market of this round.
- No efficient seller: the criterion forms of A5 and A6 are conditional.
- The frequency hypothesis is assumed. Its only inhabitant has every realized value equal to
  one, where it is trivial; the bridge has not been exercised on a sequence with failures.
- The converse of A2. Boundedness of the account is sufficient for the criterion; whether an
  unbounded account yields an efficient exploiter is item 139.
- Tightness of the reserve bound, and of the constant `3` in the floor market.
- That the two counterexamples are the only obstructions, or that reserves are the only
  certificates.
- No necessity witness for a hypothesis of the registered theorems.
- The deductive instance is inhabited at a one-point region. No market is exhibited whose
  region is a deductive region with more than one vertex.
- Nothing here is checked by anything but the Lean kernel; no reader has passed over the
  statements. The dispatch records that earlier hand-checked versions of the arc were found
  false twice; the versions formalized are the dispatch's, and whether they are the intended
  ones is a question about the definitions in `THEOREM.md` §0.

## Verification

- `~/.claude/scripts/safe-lake.sh build Workspace.Normativity.Contrib.ExactConditionsFloor`
  (which imports the other two modules): builds, no warning in the three modules.
- `~/.claude/scripts/safe-lake.sh build Workspace`: `Build completed successfully (4116 jobs)`.
- `python3.12 tests/audit_axioms.py`: `AXIOM AUDIT: 4017 results across 126 files, all within
  ['Classical.choice', 'Quot.sound', 'propext']`.
- `python3.12 tests/run.py`, on the tree at `bef7285d` (before this section was filled in):
  `ALL GREEN (80 project(s))`. It skips the Lean build unless `WORKSPACE_LEAN=1`; the build
  above is the separate run. Two earlier runs failed and were fixed: the wiki's bound claim
  count (deviation 18) and the pinned handle set (deviation 17).
- `python3.12 -m checkers.graph --root .`: `OK 2605 nodes`. `python3 -m checkers.workspace_state
  --check`: valid, 210 modern claims, 151 priorities. `python3.12 -m checkers.run`: 105 entries
  in the normativity registry, schema ok.
- A first run of the axiom audit failed on nine pre-existing modules with missing object
  files: the worktree's build cache was cloned from an older worktree and the audit elaborates
  against built imports. The full build above preceded the run reported.

## Items

Filed under the dispatch's scope, in *Normativity line — traderized enforcement*: 136 (an
exactly compliant market for a schedule of rational polytopes), 137 (between the reserve and
the obstruction), 138 (the frequency hypothesis from pseudorandomness), 139 (extraction).

## Registrations

`exact.account-preserves-criterion`, `exact.entailed-conditions-free`,
`exact.prefix-reserve-bound`, `exact.seller-obstruction`, `exact.tightening-floor-exploited`,
`exact.fresh-floor-exploited` (item 137); `exact.conditional-bridge` (item 138);
`exact.floor-market` (item 136). All `lean-proved`. A1 is recorded in the note of the first.

## Names, provisional

Types: `Bet`, `Condition`, `DualCertifiedMarket`, `PrefixReserve`, `FloorSchedule`. Notions:
`account`, `stake`, `Holds`, `Region`, `Entailed`, `AccountBounded`, `seller`, `floors`,
`tighteningFloor`, `freshFloor`, `Bridge.prior`, `Bridge.margin`, `Bridge.ratio`,
`Bridge.Frequency`, `liftDay`, `liftHist`, `liftStrategy`, `floorState`, `plainMarket`,
`oneFloor`, `constantFresh`, `pinSchedule`, `revealProcess`, `refuteProcess`, `assertProcess`.
Registry prefix `exact.`. Prose: *demanded bet*, *account*, *prefix reserve*, *floor market*.

## Outstanding maintainer actions

1. Merge pull request #146, or not: `gh pr merge 146 --squash`, carrying the Model
   attribution section into the squashed message. Auto-merge is off by the dispatch.

Nothing is reserved to `DECISIONS.md`'s queue. The round's choices are the dated entry
`2026-11-10--exact-conditions-as-dual-certified-interface`, agent-decided and reversible.

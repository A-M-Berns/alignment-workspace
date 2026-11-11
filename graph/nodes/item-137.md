---
id: item-137
kind: leaf
leaf_kind: task
action: "Close the gap between the prefix reserve bound and the seller obstruction: efficiency of the two exhibited sellers, exactness of the reserve bound by duality, and the finite-model equivalence."
who: agent
item: "137"
title: "Which conditions a logical inductor can honour exactly: between the reserve and the obstruction"
section: "Normativity line — traderized enforcement"
maintainer_order: 149
difficulty: "open"
heading_notes: ""
project: normativity
dispatchable: true
item_status: open
deliverable: "`lean-proved`; `EfficientlyComputable` for the two sellers, and either the duality theorem for the prefix reserve bound on a finite profile space or a fixture with a gap."
acceptance: "the Lean audit clean; `tighteningFloor_not_isLogicalInductor` and `freshFloor_not_isLogicalInductor` restated with no efficiency hypothesis; `oneFloor_reserve_bound` recovered as an instance of the duality theorem or shown strict."
work:
  - {kind: round, ref: projects/normativity/rounds/2026-11-10-exact-conditions-capital}
  - {kind: decision, ref: 2026-11-10--exact-conditions-as-dual-certified-interface}
context: ["lean/Workspace/Normativity/Contrib/ExactConditions.lean", "lean/Workspace/Normativity/Contrib/ExactConditionsReserve.lean", "lean/Workspace/Normativity/Contrib/OddsBankroll.lean", "projects/normativity/rounds/2026-11-10-exact-conditions-capital/THEOREM.md"]
author: "@claude-fable-5-2"
size: M
size_reason: "one item entry, three Lean modules of context"
version: 1
---
## Statement
Item 137, Which conditions a logical inductor can honour exactly: between the reserve and the obstruction, is delivered in the shape its entry states: `lean-proved`; `EfficientlyComputable` for the two sellers, and either the duality theorem for the prefix reserve bound on a finite profile space or a fixture with a gap.

## Source
ATTENTION.md, item 137 (Which conditions a logical inductor can honour exactly: between the reserve and the obstruction); its context: `lean/Workspace/Normativity/Contrib/ExactConditions.lean`, `lean/Workspace/Normativity/Contrib/ExactConditionsReserve.lean`, `lean/Workspace/Normativity/Contrib/OddsBankroll.lean`, `projects/normativity/rounds/2026-11-10-exact-conditions-capital/THEOREM.md`.

## Notes
Filed by the exact-conditions round (prompts/2026-11-10-exact-conditions-capital) within its dispatched scope; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
What a condition costs a dual-certified market is one scalar, the account
`Q_N(W) = Σ_{n ≤ N} Σ_j μ_{n,j} g_{n,j}(W)`. It is at most `2 + ε` at every live world
(`DualCertifiedMarket.account_le`), and if it is bounded below over live prefixes no
efficiently computable trader exploits the market (`no_efficient_trader_exploits`, registered
`exact.account-preserves-criterion`). Two things are proved about when it is bounded. A
**prefix reserve** — a mass on finitely many world profiles, shrinking day by day, each day's
mass on worlds live that day and averaging each of that day's rows to a nonnegative value —
bounds it below by `-U(1 - r)/r` at a profile retaining mass `r` (`reserve_bound`, registered
`exact.prefix-reserve-bound`); rows every live world satisfies cost nothing
(`exact.entailed-conditions-free`). Against any history satisfying a condition, with no
certificate, a staking whose account is bounded above and unbounded below makes the seller of
the demanded bets exploit (`Condition.seller_exploits`, registered `exact.seller-obstruction`),
and two conditions have such a staking: a floor tightening to one on a sentence that stays
undecided, and floors `1 - 2^-(n+1)` on fresh atoms each settled true the next day
(`exact.tightening-floor-exploited`, `exact.fresh-floor-exploited`). At a constant level
`c < 1` the fresh floors are honoured by an unexploited market (`constantFresh_unexploited`).
Wanted: (a) `EfficientlyComputable` for `(tighteningFloor φ).seller unitStake` and
`freshFloor.seller dayStake` against the pinned dependency's definition — one trade of a
rational constant per day — which the two `not_isLogicalInductor` forms take as a hypothesis;
(b) exactness of the reserve bound: for fixed `N` and a finite profile space, whether the
infimum of `Q_N(ω)` over multiplier sequences satisfying the day-by-day ceilings
`Q_n ≤ U` on profiles live at `n` equals the supremum over prefix reserves of
`-U(1 - r_N(ω))/r_N(ω)`, by linear-programming duality, or a fixture with a gap; (c) the
finite-model equivalence: for a condition constant in time on finitely many payoff profiles all
live forever, a compliant constant pricing against which no staking has an account bounded
above and unbounded below exists iff the region meets the relative interior of the hull of the
profiles; (d) the relation of `account_ge_neg_odds` to
`OddsBankroll.Account.netWorth_ge_neg_odds` as a reduction — the force layer's units are
intensity times violation, and whether they are multipliers of some dual-certified market is
not settled.

*Deliverable shape:* `lean-proved`; `EfficientlyComputable` for the two sellers, and either the duality theorem for the prefix reserve bound on a finite profile space or a fixture with a gap.
*Acceptance check:* the Lean audit clean; `tighteningFloor_not_isLogicalInductor` and `freshFloor_not_isLogicalInductor` restated with no efficiency hypothesis; `oneFloor_reserve_bound` recovered as an instance of the duality theorem or shown strict.
*Context:* `lean/Workspace/Normativity/Contrib/ExactConditions.lean`; `lean/Workspace/Normativity/Contrib/ExactConditionsReserve.lean`; `lean/Workspace/Normativity/Contrib/OddsBankroll.lean`; `projects/normativity/rounds/2026-11-10-exact-conditions-capital/THEOREM.md`.
*Consumed by:* item 139 (an extracted staking is a seller); item 126 (the bankroll across repeated reopenings is a reserve that releases mass at each reopening).

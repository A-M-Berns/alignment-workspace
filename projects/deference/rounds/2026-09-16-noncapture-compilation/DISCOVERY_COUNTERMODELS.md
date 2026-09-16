# Discovery countermodels

**Status:** `ci-only`.  Every row is an exact inquiry model in `src/attacks_discovery.py`,
evaluated by `tests/test_discovery.py`.  `W = 1/4`.  "Obstruction" is the repertoire cell
gap (unbounded budget); "minimax" is the exact budgeted value at the row's budget.

| # | attack | interface that catches it | obstruction | minimax @ budget | note |
|---|---|---|---|---|---|
| 1 | hidden counterreason, direct query | discovery, closed | 0 | 0 @ 1 | one query determines it |
| 2 | two reasons, one query | discovery (budget) | 0 | W @ 1 | the second reason is the worst case |
| 3 | four light distractors, one heavy hidden reason | discovery (prioritization) | 0 | 1/16 @ 1 | greedy by conditional mass asks the heavy one first |
| 4 | advisor floods with heavy false candidates | discovery (engine-owned candidate generation) | 0 | 0 @ 1 | false in every world ⇒ not on the frontier; FIFO over candidates would waste 3 queries |
| 5 | advisor raises the query's cost | discovery (exogenous costs: hypothesis) | 0 | W @ 1 (cheap: 0) | the obfuscated query is unaffordable |
| 6 | one test reveals two reasons | discovery (repertoire structure) | 0 | 0 @ 1 | the joint test beats two direct queries |
| 7 | discovering `for` creates a defeater obligation | discovery (defeat closure) | 0 | 0 @ 2 | `d` has conditional mass W once `for` is docketed; both obligations close |
| 8 | counterreason with the advisor's defeater on the docket | discovery (conditional mass) | 0 | 0 / W | with `e` docketed the frontier is empty; without, `c` is an obligation |
| 9 | redundant reasons | discovery (direct gain vs certificate) | 0 | W @ 1 | gap W; after one true answer the other's conditional mass is 0 |
| 10 | truth only by an expensive empirical test | discovery (budget); authentication if the test is the certificate | 0 | W @ 4 | closes at cost 5 |
| 11 | repertoire cannot distinguish the reason | discovery (repertoire obstruction) | **W** | W @ any | one cell holds both worlds |
| 12 | indistinguishable worlds, different values | discovery (information cell) | **W** | W @ any | the gap is exactly the value difference on the shared cell |
| 13 | discoverable, not in time | discovery (budget) / service if docketed late | 0 | W @ 2, 0 @ 3 | the boundary with service is the docket |
| 14 | the needle | discovery (budget; adaptivity useless) | 0 | W @ n−1, 0 @ n | no fractional progress |
| 15 | chain of levels | discovery (adaptivity) | 0 | 0 @ 2 adaptive, 1/8 nonadaptive | binary search |
| 16 | advisor controls stopping | discovery (engine-owned stopping) | 0 | W if stopped at once | the frontier is nonempty: stopping violates the obligation |
| 17 | honest, resource-bounded engine | discovery (budget) | 0 | W @ 1 | as 2 |
| 18 | reason outside the ontology | **ontology** | 0 | 0 | the worlds do not carry it; the theory does not see it |
| 19 | insufficient granularity | **ontology** | 0 | 0 | both worlds docket the one id |
| 20 | perfect discovery, service cut fails | **service** | — | — | second pass, case 1 |

## World manipulation, and which interface catches it

| the advisor … | is it discovery? | caught by |
|---|---|---|
| leaves a true reason undiscovered | yes | the frontier obligation; the cell gap if the repertoire cannot reach it |
| makes the counterreason false by changing the world | no | the **effect side**: the change is an effect, and relative to the changed world the docket is not missing anything (second pass, row 6 of the first pass) |
| hides evidence without changing the reason | no | **evidence soundness**: outcomes must be functions of the world; a tampered outcome is an authentication failure of the inquiry channel |
| alters which questions get asked | no | **engine-owned policy** (rows 4, 16) |
| alters the cost of discovering a counterreason | no | **exogenous costs** (row 5), a named hypothesis |
| alters the inquiry engine itself | no | the engine is a party of the ecosystem; this is the declared-transform / causal-contract wall, not a residual |

## What the rows establish

- The obstruction is real and exactly the cell gap (rows 11, 12): with an unbounded
  budget the residual is zero iff the repertoire separates what the verdict separates.
- The budget obstruction has no cut-like closed form: the needle (row 14) pins the
  minimax at the full residual until the last query, and adaptivity (row 15) changes the
  answer, so the value is a decision-tree quantity.
- The frontier is the obligation (rows 3, 4, 7, 8, 16): it prioritizes by conditional
  adverse mass, ignores what no world makes true, follows defeat, and is violated by
  early stopping.
- Discovery is type-clean against its neighbours: rows 13 (service), 10 (authentication),
  18–19 (ontology), and the world-manipulation table (effect side, evidence soundness).

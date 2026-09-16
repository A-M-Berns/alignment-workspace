# Countermodels, second pass: the service problem under pressure

**Status:** `ci-only`.  Every row is an exact instance in `src/attacks_second_pass.py`,
evaluated by `tests/test_supply.py`.  `W = 1/4` is the unit of adverse mass.  "Structural"
means the hypothesis the row isolates is one the theorem genuinely needs; "wishful"
marks a hypothesis the first pass had implicitly assumed and that this row shows must be
made explicit.

| # | attack | what it isolates | structural? | verdict on the instance |
|---|---|---|---|---|
| 1 | two reasons, one slot | capacity ≥ demand on the suffix cut | yes | cut excess 1; least miss `W` under any policy |
| 2 | high and low value, one slot | weighted, not counted, service | yes | least miss `1/8` (the low one); count would say 1 either way |
| 3 | protected high vs unprotected low, one slot | protect what you can serve | yes | serve the protected: audit on, charge `1/8`; serve the low: void |
| 4 | supplier knows both, can serve one | knowledge is not service | yes | least miss `W` |
| 5 | reason discovered at slot 3 with cost 2, deadline 4 | window capacity, not total | yes | total capacity 4, window capacity 1: cut at `s = 3` fails |
| 6 | authentication consumes capacity | cost includes authentication | yes | with it: one reason missed (`W`); without it: both served, `2W` moves to the authentication term |
| 7 | defeat | per-reason sensitivity, not per-weight | yes | defeater: weight 0, adverse 0, symmetric `W`; the counterreason's adverse mass is conditional |
| 8 | redundant evidence | static certificates are loose | yes | omitting both gains `W`, the adverse mass charges `2W` |
| 9 | serving one reveals another | discovery is policy-dependent | yes | as undiscovered: `1/2` discovery loss; served first: `0` |
| 10 | adversarial arrivals | the cut, not total capacity | yes | demand 3 = capacity 3, all released at slot 2: cut excess 2, miss `2W` |
| 11 | advisor floods the docket | supplier capacity independent of advisor load | yes | weighted service: miss `0`; FIFO: the counterreason is crowded out, miss `W` |
| 12 | advisor raises a reason's cost | exogenous cost profile | **wishful** | cost 1: cut holds; obfuscated to 3: cut fails; the bound must range over the cost-influence class |
| 13 | two suppliers | capacity adds for divisible service | yes | both instances feasible with capacity 2 |
| 14 | undiscoverable reason | discovery loss is outside the service theorem | yes | discovery `W`, service `0` |
| 15 | undeclared type | scope is external | yes | scope `W`, charged nowhere |
| 16 | comparator with unrealizable content | realizable comparator | yes | ideal regret `1/2`, realizable regret `0` |
| 17 | cost-2 reason vs two unit reasons, two slots | unit costs for the exact greedy | yes | greedy misses `1/2`, the optimum `3/8` |

## What the rows establish

**Structural hypotheses of the supply theorem** (rows 1, 2, 4, 5, 6, 10, 13): capacity
inside release windows is the resource; adverse weight is the objective; authentication
is part of the cost; several suppliers add.  Rows 5 and 10 are the two ways "enough
capacity in total" fails: late discovery and adversarial concentration; both are read off
the cut excess exactly.

**Structural hypotheses of the residual quantity** (rows 7, 8): the certificate is the
adverse sensitivity table of the program class, not its weight table; and no static
certificate is tight under redundancy, so the theorem's bound is a bound and the direct
discrepancy is the truth.

**Independence, made explicit** (rows 11, 12): the supplier's capacity must not be
consumable by the advisor (weighted service makes weight-0 flooding harmless; FIFO does
not), and the cost profile must not be the advisor's to raise.  Row 12 is the one
wishful hypothesis of the first pass: "an independent supplier" silently assumed
exogenous costs.  Without it the certified bound is a supremum over the advisor's
cost-influence class, which is a different and larger quantity.

**The comparator** (rows 9, 14, 16): discovery is not a property of the docket but of
the policy that runs on it; the discovery loss is outside the service theorem; and a
comparator carrying content no process could have produced states an ideal regret that
no supplier certifies.  The realizable theorem is against the discovered comparator.

**Scope** (row 15) is reported and not charged: the theorem does not see it.

**General costs** (row 17): greedy by weight is not optimal, the problem is
knapsack-hard, and the cut bound remains the exact lower bound on unserved cost.

## What no row breaks

- The identity and the steering bound (first pass) on every instance's induced trace
  (`tests/test_supply.py::Bridge`).
- The cut condition as the exact feasibility criterion, against exhaustive schedule
  search on random unit and general instances.
- The cut excess as the least unserved count, and the layer formula and greedy as the
  exact least weighted miss for unit costs, on random instances.
- The decomposition `Miss = discovery + service + authentication`, with scope outside.

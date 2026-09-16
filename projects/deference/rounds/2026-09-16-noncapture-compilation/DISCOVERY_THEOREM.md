# The discovery theorems: obstruction, budget, progress

**Status:** `ci-only`; third pass.  Lean: `ReasonDiscovery.lean` §§2–3.  Fixtures:
`tests/test_discovery.py::Obstruction`, `::Countermodels`.

## 1. The information-cell obstruction (exact, unbounded budget)

Let `~` be repertoire indistinguishability and `cell(ω)` its class.  For a cell `K`
define

```
gap(K)  :=  max_{ω ∈ K}  [ V(certain K) − V(Truth ω) ] .
```

**D1 (lower bound; `residual_ge_cellGap`, LEAN).**  For an antitone verdict, every sound
docket policy has, on some world of every cell, residual at least the cell's gap.  Proof:
the policy's docket on the cell is one set `D ⊆ certain(K)` (soundness and blindness),
so `V(D) ≥ V(certain K)` by antitonicity, and the residual on the worst world of the cell
is at least the gap.

**D2 (attainment; `exhaustive_attains_cellGap`, LEAN).**  The exhaustive policy, which
dockets the certain reasons of the cell, has residual at most the gap on every world of
the cell.

**Corollary (the obstruction).**  The least worst-case residual any policy achieves with
unbounded budget is exactly

```
Discovery*_∞  =  max_K gap(K)
```

over the repertoire's cells (`test_minimax_with_unbounded_budget_is_the_obstruction`,
random instances).  It is **zero iff the repertoire separates every pair of worlds whose
certain content differs in value**: `gap(K) = 0` iff `V(certain K) = V(Truth ω)` for all
`ω ∈ K`.  A repertoire that cannot tell two worlds apart leaves exactly the value
difference between the content they share and the content of the worse one (rows 11, 12).
This is the discovery analogue of the service cut: **information-cell diameter** in the
verdict.

## 2. With a budget: the minimax value

```
V(K, B)  =  min( gap(K),  min_{a : c(a) ≤ B, a splits K}  max_{o}  V(K ∩ f_a⁻¹(o), B − c(a)) )
```

(`Inquiry.minimax`).  It is the exact least worst-case residual of an adaptive policy
with budget `B` from cell `K` (checked against an enumeration of all decision trees,
`test_minimax_matches_exhaustive_decision_trees`); it is monotone in `B`, never below
the obstruction, and never above the best nonadaptive value
(`test_minimax_is_monotone_in_budget_and_above_the_obstruction`).  With
`B = Σ_a c(a)` it equals the obstruction.

**No closed form.**  The budgeted problem contains the minimax cost of identifying a
hidden element with direct queries, so the value is a decision-tree quantity: exact by
recursion, with no cut-like formula.  Two structural facts stand:

- **The needle** (row 14): `n` candidates, one true in each of `n` worlds and none in
  one more, direct queries only.  `V = W` for every budget below `n` and `0` at `n`.  The
  adversary answers "false" until the last query.  Hence **no fractional-progress
  hypothesis holds for direct-query repertoires**: no single query reduces the worst-case
  potential at all (`test_needle_no_fractional_progress`).
- **Adaptivity matters** (row 15): four nested worlds, level queries; adaptive binary
  search closes the residual with two queries, every fixed pair of queries leaves a cell
  of gap `1/8` (`test_adaptive_beats_nonadaptive`).  The adaptivity gap is real and
  unbounded in general (it is the gap between depth and size of a decision tree).

## 3. Progress, and what it needs

**D3 (potential decay; `potential_decay`, LEAN).**  If a potential `x_t` satisfies
`x_{t+1} ≤ (1 − γ)·x_t` at every step, then `x_k ≤ (1 − γ)^k x_0`; with actions of cost
at most `c` and budget `B` this is `x_T ≤ (1 − γ)^{⌊B/c⌋} x_0`, the explicit rate/budget
relation the dispatch asked for.

**What discharges its hypothesis.**  A **witness-completeness** property of the
repertoire: whenever the worst-case residual exceeds `ε`, some affordable action's every
outcome reduces it by a factor `1 − γ`.  This holds for repertoires with *aggregate*
tests (a level query on a chain halves the cell: row 15 with `γ = 1/2` in cell size) and
**fails for direct queries** (the needle: `γ = 0`).  So the honest statement is:

> a progress theorem exists exactly for repertoires whose actions split every
> high-residual cell by a fixed fraction in the worst outcome; direct queries on
> individual reasons do not, and for them the minimax value is the decision-tree
> depth, with the needle as the sharp lower bound.

The natural potential is the worst-case conditional adverse mass
`Pot_t := max_{ω ∈ K_t} Σ_{r ∈ Truth ω \ D_t} A_{r|D_t}` (`Inquiry.potential`): it is
monotone under refinement (cells shrink, dockets grow, conditional certificates fall) and
dominates the residual; but its decrease per query is not bounded below for direct
queries, which is the needle again.

## 4. The frontier as the obligation

`residual_le_zero_of_frontier_empty` (LEAN): an empty frontier forces residual `≤ 0` on
every consistent world.  So the engine's obligation at any time is the frontier
(`Inquiry.frontier`), and **"unresolved reason of positive conditional adverse mass ⇒ an
explicit inquiry obligation remains"** is a theorem, not a policy.  Greedy on the
frontier by conditional adverse mass (`greedy_frontier`) is the certified policy of the
fixtures: it asks about the heavy reason before the distractors (row 3), never asks
about a flooded candidate that no world makes true (row 4), and closes defeater
obligations as they arise (row 7).  It is not optimal in general (adaptivity, row 15).

## 5. Summary table

| statement | status |
|---|---|
| residual ≤ conditional adverse mass of the undiscovered | LEAN (`adverseAbove_union`) |
| empty frontier ⇒ residual ≤ 0 | LEAN |
| every sound policy ≥ cell gap on some world of each cell | LEAN |
| exhaustive policy attains the gap | LEAN |
| unbounded-budget minimax = max cell gap | FIX (random instances) + the two Lean bounds |
| budgeted minimax = decision-tree recursion; monotone; ≥ obstruction; ≤ nonadaptive | FIX |
| no fractional progress for direct queries (needle) | FIX, refutes the hypothesis |
| adaptive strictly beats nonadaptive | FIX |
| geometric decay under witness completeness | LEAN (`potential_decay`), hypothesis model-specific |

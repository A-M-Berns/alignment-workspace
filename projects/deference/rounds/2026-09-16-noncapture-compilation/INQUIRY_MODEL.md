# The inquiry model

**Status:** `ci-only`; third pass.  `src/inquiry.py`; Lean `ReasonDiscovery.lean` §2
(`Model`, `SoundPolicy`).

## 1. The minimal object

- **Worlds** `Ω`, finite: each fixes which adverse declared reasons are true,
  `Truth : Ω → Finset I`.  This is the engine's declared *hypothesis space* of reason
  states; it is part of the declared representation, and the theorem is relative to it.
- **Repertoire** `A` of inquiry actions, each with a cost `c(a)` and an outcome function
  `f_a : Ω → O`.  Running `a` in world `ω` reveals `f_a(ω)` and nothing else.  A direct
  query on `r` has `f(ω) = [r ∈ Truth(ω)]`; a test may reveal several reasons at once
  (row 6), or nothing (row 11).
- **Policy**: adaptive; a function from the history of outcomes (equivalently the
  current cell) to the next action or a stop, with total cost at most the budget `B`.
- **Cell** `K_t ⊆ Ω`: the worlds consistent with the outcomes observed so far.
- **Certain docket** `certain(K) := ⋂_{ω ∈ K} Truth(ω)`: what the evidence determines
  true.  A **sound docket** is any `D ⊆ certain(K)`; the docket cannot contain a reason
  the evidence has not determined, and it cannot depend on what the repertoire cannot
  reveal (`SoundPolicy.sound`, `SoundPolicy.blind`; `SoundPolicy.subset_certain`, LEAN).
- **Verdict** `V(S) := F(pro ∪ S)`, antitone in `S`.

That is the whole object.  Nothing probabilistic is assumed; the worst case over the cell
is the quantity.

## 2. What an inquiry reveals

An outcome partitions the current cell.  The information an action carries about the
residual is exactly how it splits the cell's *value profile*: two worlds that agree on
every action's outcome are in one cell forever, and a docket policy cannot tell them
apart.  The repertoire's **indistinguishability relation** `ω ~ ω'` (same outcome on
every action) is an equivalence, its classes are the finest cells any policy can reach,
and the whole obstruction theory lives on those classes (`DISCOVERY_THEOREM.md`).

## 3. The resource

Queries with costs against a budget, at one occurrence.  Time enters only through the
commitment deadline that fixes the budget; computation and attention are absorbed into
`c(a)`; money is `c(a)` when inquiry is purchased.  There is no separate "capacity per
period" as in the service model: an inquiry policy is a decision tree, not a schedule,
and its resource is the total cost of the path taken.  Where an engine has both a
per-period capacity and a deadline, the service model of the second pass applies to the
*routing* of what inquiry determines, and this model to the *determining*.

## 4. Which abstraction

The problem "choose actions adaptively to minimize the worst-case residual within a
budget" is a **minimax decision-tree / query-complexity** problem on a finite hypothesis
space.  It is not affordability (no shared slot, no liability account), not a bandit
(no stochastic reward, no exploration/exploitation), not active learning in the
statistical sense (no sample complexity; worst case over a finite class).  Its closest
named relatives are generalized binary search and adaptive set cover
(`DISCOVERY_RELATED_MATH.md`), and the workspace's own record already lists set cover
with delay and adaptive submodularity as the scheduler models for docketed inquiry
(`wiki/Normative-Record-and-Inquiry.md`).  The argumentation-theoretic content (defeat)
enters through the *objective*, the conditional adverse mass, not through the search.

## 5. Independence, stated

"Independent inquiry" means, formally, that the following are the engine's and not the
advisor's:

| the advisor must not control | what it would do otherwise | fixture |
|---|---|---|
| the outcome functions `f_a` | evidence tampering: outcomes no longer functions of the world | this is authentication / effect-side containment, not discovery (`DISCOVERY_COUNTERMODELS.md` §world manipulation) |
| the policy's action choice or its stopping | stop before the frontier is empty | row 16 |
| the costs `c(a)` | make a counterreason's query unaffordable | row 5 |
| the candidate set the engine spends queries on | flood with heavy false candidates | row 4 |
| the hypothesis space `Ω` | exclude the worlds where a counterreason is true | not a discovery failure but a representation one (the space is declared) |

The **weakest causal-independence condition** under which the theorem is meaningful:
the outcome functions are world-determined (evidence soundness), the policy is a
function of the history alone and runs until the frontier is empty or the budget is spent
(engine-owned selection and stopping), and the cost function and the candidate
prioritization are functions of the program's conditional adverse mass and the declared
repertoire, not of the advisor's submissions.  Under these, the advisor's only remaining
lever on discovery is the world itself, which is the effect side.

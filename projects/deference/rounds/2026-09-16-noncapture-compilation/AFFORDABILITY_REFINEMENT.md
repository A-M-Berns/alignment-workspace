# Affordability, refined: what the existing theory supplies and what is new

**Status:** `ci-only`; second pass.  The first pass said "deadline reason supply is the
timeliness side of affordability".  This file reads the affordability round
(`projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability/`) rather
than paraphrasing it, and states the interface at theorem level.

## 1. What the affordability theory is about, exactly

Its resource is a **liability budget**: enforcing a reason takes a trading position whose
losses are charged to a signed cumulative account; a date's cost `L_t(a)` is star-shaped
in the allocated authority `a`; persistence on a finite lifetime budget holds iff
`liminf_t L_t(1) = 0` (S1); with a uniform delay `H` and linear costs `w_s a`, a claim
stream is serviceable iff `Σ_t c_t · min_{s ∈ [t, t+H]} w_s ≤ B` (D4); feasibility against a
*given* service profile is the interval Gale–Hoffman condition (BD1) and FIFO is
optimal (BD2); several reasons compete because timely service costs a definite amount
(M1: budgets add); there is **no Hall condition in that model** because the budget is a
scalar shared resource and the force layer has no shared slot (N1).  There is no
missed-mass bound anywhere in it: DI1 is an all-or-nothing insolvency certificate, and
STS assumes the untransported residual vanishes.

## 2. What reason supply has that enforcement does not

A supplier that discovers, routes and authenticates reasons before a commitment deadline
has **two** resources:

| resource | shared how | feasibility form | source |
|---|---|---|---|
| capacity in release windows (`cap(t)` at slot `t`, usable by reasons released by `t`) | structurally: a slot serves whoever is released | suffix-cut condition (Hall on nested neighbourhoods) | new here (`SUPPLY_THEOREM.md`) |
| liability/underwriting budget (if service is itself enforcement) | scalarly: costs add | D4 with the window `[a_r, T)`: `Σ_r c_r · min_{s ∈ [a_r, T)} w_s ≤ B` | affordability round |

The first is where the Hall form lives and where the **missed-mass** theorem is: the
least unserved mass is the max cut excess (RS4).  The second is imported unchanged: if
each unit of service is an enforcement act with date price `w_s`, the supplier is
affordable on budget `B` iff D4 holds over the release windows, and by M1 the budgets of
several reasons add.  A supplier is affordable when both hold; either alone is not
enough (fixture: two unit reasons, one slot, unbounded budget: the cut fails; one reason,
ten slots, budget below its cheapest-date price: D4 fails).

## 3. Persistence versus timeliness, pressed

The first pass's claim survives and sharpens.  Persistence (S1) is about an unbounded
horizon and is budget-free; reason supply has a deadline at every occurrence, so it is
never persistence.  But "timeliness" in the affordability round means a *uniform delay
`H`* on a claim stream; reason supply is a *common deadline `T_n`* per occurrence with
reason-specific release times, i.e. windows `[a_r, T_n)` of different lengths.  That is
the difference between BD1's interval neighbourhoods and this round's nested ones, and it
is what makes the cut family a chain and the greedy exact.  The existing theory does
**not** already imply the bounded-delay service theorem for reasons; it implies the
budget half (D4 over the window) and stops at feasibility.

The dispatch's specific questions:

- *Are costs additive across reasons?*  Budget costs add (M1, separable case); capacity
  costs add within a slot up to `cap(t)` and are otherwise a cut constraint.
- *Is capacity fungible?*  Across slots, no (a slot's units expire); across suppliers,
  yes for divisible service (fixture 13).
- *Does service of one reason interfere with another?*  Through capacity in shared
  windows, yes; that is the cut.  Through the force layer, no (N1).
- *Are reasons divisible / partially serviceable?*  Preemptively across slots, yes
  (units); a partially served reason is not served (no partial credit), which is why the
  weighted problem is combinatorial.
- *Is there an optimal scheduling theorem?*  Yes: heaviest-available-first is optimal
  for unit costs, offline and online (RS4, RS6); for general costs the problem is
  knapsack-hard and the cut bound is the exact lower bound on unserved cost.
- *Which mathematical object?*  A bipartite transportation problem with nested
  neighbourhoods (a transversal matroid) for capacity, plus D4's additive budget.  Not the
  authority-underwriting geometry, which has no shared slot; not an online knapsack, since
  arrivals only add options and costs are known at release.

## 4. The interface, at theorem level

**Input from the ecosystem** at occurrence `n`: the docket (reasons raised, when, by
whom), the supplier's capacity profile and, where service is enforcement, the date
prices and budget.

**Output of the supply theorem**: the least achievable service loss `Miss*_n` (exact for
unit costs; a cut lower bound and a pseudo-polynomial optimum otherwise), as a
`Γ`-valid sentence "`D^A_n ≤ α_n` on the audited branch"; and the certified policy that
attains it (heaviest-available-first).

**Input to the steering theorem**: exactly that sentence family, as `hsupply` of
`li_noncapture`.

**What the normativity agenda must make small**, stated as quantities of this
interface: the cut excess of the docket at every occurrence (capacity in release windows,
not total capacity); the adverse mass released too late to serve (discovery timing); the
adverse mass never raised (discovery, outside the theorem); the authentication failure
mass; and, if the supplier is an enforcer, D4's window sum against its budget.

## 5. What is withdrawn from the first pass

- "Budgets add and reasons compete" was right for the budget resource and incomplete:
  the competition that decides the content residual is *capacity* competition inside
  release windows, and it has a cut characterization, which the budget does not.
- "Reason supply liveness is the affordability theory's timeliness case" is narrowed:
  it is the *common-deadline nested-window* case, which the affordability round did not
  treat, on top of its budget criterion, which it did.

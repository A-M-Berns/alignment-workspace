# The supply theorem: when the content residual is small, and why

**Status:** `ci-only`; second pass.  Lean: `lean/Workspace/Deference/Contrib/ReasonSupply.lean`
§2.  Fixtures: `src/supply.py`, `src/attacks_second_pass.py`, `tests/test_supply.py`.
Names are provisional (`AGENTS.md` standard 6).

## 1. The service problem, exactly

At evaluation occurrence `n` with commitment deadline `T_n`:

- a declared interface `I_n`; for each `r ∈ I_n` the world settles whether `r` is true;
- for each true declared `r`: its **release** `a_r ∈ ℕ ∪ {∞}`, the slot at which some
  supplier learns that `r` is true and relevant (`∞`: never before `T_n`, a *discovery
  failure*); its **cost** `c_r ∈ ℕ`, the capacity units needed to discover-route-
  authenticate it; its **adverse sensitivity** `A_r ≥ 0` (`CONTENT_RESIDUAL.md`); whether
  it is **protected**; whether authentication of a served `r` succeeds;
- the **supplier**: a process other than the advisor with capacity `cap(t)` units at slot
  `t < T_n`, which chooses which discovered reasons to serve.  A **schedule** assigns units
  to reasons at slots, none before release, none at or after `T_n`, within capacity; a
  reason is **served** when it receives `c_r` units before `T_n`.

The object of the theorem is the **missed adverse mass**

```
Miss_n := Σ_{r true declared, not served by T_n} A_r ,
```

which is exactly the content term `D^A_n` of the steering inequality against the
fully-informed comparator (`tests/test_supply.py::Bridge`).  "A route exists" (Robust
Openness) is not in this definition; "served before `T_n`" is.

## 2. The obstruction

Write `Cap(s) := Σ_{t ∈ [s, T)} cap(t)` and `Demand(s) := Σ_{r : a_r ≥ s} c_r` over the
discovered reasons.

**RS1 (the cut bound; LEAN `served_cut_le`, `unserved_ge_excess`).**  For every schedule
and every `s`, the service received by the reasons released at or after `s` is at most
`Cap(s)`; hence the cost left unserved among them is at least `Demand(s) − Cap(s)`.

**RS2 (necessity; LEAN `cut_of_servesAll`).**  Full service forces the **suffix-cut
condition** `∀ s: Demand(s) ≤ Cap(s)`.

**RS3 (sufficiency for unit service; LEAN `unit_servable_iff_cut`).**  With unit costs
and unit slots, a schedule serving every reason exists **iff** the suffix-cut condition
holds.  Proof: Hall's theorem on the neighbourhoods `[a_r, T)`; because they are nested,
Hall's condition for a set `S` is implied by the suffix cut at `min_{r∈S} a_r`.  For general
integer costs and capacities with preemption the same holds (max-flow/min-cut on the nested
network: every minimal cut is a suffix cut); it is checked against exhaustive schedule
search (`test_cut_condition_matches_exhaustive_general_schedules`) and not mechanized.

**RS4 (the exact least miss, unit costs; FIX, paper).**  The least number of reasons
left unserved is the **cut excess** `max_s (Demand(s) − Cap(s))⁺` (Hall's deficiency
form; `test_cut_excess_is_the_least_unserved_count`).  The servable sets form a
transversal matroid on nested neighbourhoods, so **largest adverse weight first, kept if
the cut condition still holds, is optimal** (`test_layer_formula_and_greedy_are_exact_for_unit_costs`),
and the least weighted miss has the closed form

```
Miss*  =  Σ_r A_r  −  Σ_j (A_(j) − A_(j+1)) · rank(top-j) ,
rank(S) = #S − max_s (#{r ∈ S : a_r ≥ s} − Cap(s))⁺ ,
```

with the reasons sorted by adverse weight.  This is the **exact dual obstruction** the
dispatch asked for: the best achievable content residual is a max over deadline cuts of
the demand that exceeds the remaining capacity, layered by weight.

**RS5 (general costs).**  With reason-specific costs the weighted problem contains
knapsack (one slot, costs as sizes), so it is NP-hard (`RELATED_MATH.md`); greedy by
weight is not optimal (fixture 17: greedy misses `1/2`, the optimum `3/8`); the cut bound
RS1 remains an exact lower bound on unserved *cost*, and the least weighted miss is a
pseudo-polynomial dynamic programme, computable from the docket.

**RS6 (online = offline for unit service).**  With unit costs and a common deadline,
serving at each slot the largest-weight discovered unserved reason attains the offline
optimum: the available set only grows, an idle slot is never better than serving, and an
exchange moves any higher-weight available reason forward
(`test_online_greedy_is_offline_optimal`).  The online gap of the affordability round's
OS1 comes from *prices revealed later*; the capacity model has no such input.

## 3. The theorem that makes `Miss_n` small

**Supply theorem.**  Let the supplier's discovered docket at `n` be `R_n` with releases,
unit costs and adverse weights, and let it serve by RS6.  Then

```
Miss_n  =  discovery_n  +  Miss*_n(R_n)  +  authentication_n ,
```

with `discovery_n` the adverse mass of true declared reasons never released before `T_n`,
`Miss*_n` the exact service loss of RS4 on the discovered docket, and `authentication_n`
the adverse mass of served reasons whose authentication fails.  In particular

```
Miss*_n = 0   iff   the suffix-cut condition holds for the discovered reasons of
                    positive adverse weight,
```

and `limsup_n Miss*_n ≤ ε` iff eventually a servable subset of the docket leaves adverse
mass at most `ε`, which the layer formula decides.

**What kind of statement this is.**  `Miss*_n` is a *computation on the log*: the
docket (who raised what, when), the costs and the capacity are log facts, the schedule
is a program.  So "the service loss at `n` is at most `α_n`" is a `Γ`-valid sentence, of
exactly the type the composition consumes (`COMPOSITION.md`).  `discovery_n` is not: it
depends on which true reasons nobody raised.  That is why the end-to-end theorem is
stated against the **discovered comparator** and the ideal one carries the discovery term
outside.

## 4. What the theorem exposes

- **Deadline competition is capacity competition.**  Two reasons with one slot before
  the deadline: exactly one is missed, and the weighted policy misses the lighter
  (fixtures 1, 2).  Total capacity is irrelevant; what matters is capacity *inside each
  release window* (fixture 5: capacity `4 ≥ 2` but the window has `1`; fixture 10:
  adversarial arrivals put all demand after the last slot).
- **Knowledge is not service** (fixture 4), **authentication is cost** (fixture 6: serving
  without authenticating moves the same mass to the authentication term), and
  **discovery is policy-dependent** (fixture 9: a reason revealed only by serving
  another).
- **Independence means two things**: the supplier's capacity is not consumed by the
  advisor's submissions (fixture 11: flooding is harmless under weighted service and
  fatal under FIFO), and the cost profile is not the advisor's to raise (fixture 12: an
  obfuscated counterreason breaks the cut).  Without the second, the bound must be taken
  over the advisor's cost-influence class.
- **Suppliers add** for divisible service (fixture 13).

## 5. Protected scope as a design parameter

`hybrid_bound` (LEAN): on the audited branch only the *unprotected* missing adverse mass
is charged; a missing protected reason turns the audit off (the evaluation voids, the
advisor's security is `0`).  Hence, for a protected set `P`:

```
steering advantage  ≤  Σ_{r ∉ P, missing} A_r      on audited worlds,
void mass           =  Pr[ some r ∈ P missing ] .
```

Total protected scope is the case `P = I`: no charge and a void whenever anything is
missing, which is desirable **exactly when the suffix-cut condition holds for all of `I`**
(then voids come only from discovery and authentication).  Otherwise the hybrid
dominates: **protect exactly a servable set of the largest adverse mass** (RS4's greedy
set), so that protected reasons are never missed by service, and charge the rest.
Fixture 3 is the unit of this: one slot, a protected high-value and an unprotected
low-value reason; serving the protected one keeps the audit on and charges `1/8`;
serving the other voids.  A risk-sensitive hybrid is the same rule with `A_r` replaced by
the designer's loss function of a missed `r`.

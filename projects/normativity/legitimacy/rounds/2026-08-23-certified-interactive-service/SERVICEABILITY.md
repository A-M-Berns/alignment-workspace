# Serviceability, joint serviceability, schedulability

Status: **research memo; unregistered**. Base definitions use
deterministic policies, adversarial environments, finite response sets,
and no fairness assumption; refinements are noted where they matter.

## Individual serviceability

DEFINITION. For liability `d` at history `h`:

```text
Servable(d, h)  iff  exists policy pi such that every Gamma-run
extending h consistent with pi reaches some finite t and certificate c
with Check_{sigma_d}(rho<=t, c).
```

For finite environments and finite-state monitors this is forced
reachability in the environment x monitor product (`forced_reach`), so
it is decidable there, and the attractor policy certifies within the
number of product states — the Koenig-style uniform bound: with finite
response sets, "eventually against every run" implies "within a
uniform bound". DERIVED; `test_winning_policy_bounds_time`. With
infinite branching the bound fails and `Servable` splits into bounded
and unbounded variants; the base version keeps finite branching.
Randomized policies are excluded from the base notion; nothing tested
needs them.

## Joint serviceability

DEFINITION. `JointlyServable(D, h)`: one policy forces eventual
certification of every occurrence in the finite multiset `D`. With
absorbing acceptance this is again plain reachability in the product
(`jointly_servable`).

COUNTEREXAMPLE (finite, solver-checked, no resource bound needed):
individually servable does not imply jointly servable. Interference
suffices — servicing `d1` moves the environment where `d2`'s
certificate is unreachable and conversely
(`test_individually_servable_but_not_jointly`). This strengthens the
budget-style separation: the failure is dynamical, not economic.

## Dynamic schedulability

Arrival streams are a different question from any fixed docket, and
the round separates four properties that a single "liveness" label
conflates:

1. **Individual feasibility** — each arriving occurrence is servable
   in isolation.
2. **Finite-docket joint feasibility** — `JointlyServable` of any
   fixed docket.
3. **Eventual service (no starvation)** under the arrival stream.
4. **Bounded latency / deadline compliance** under the arrival stream.

Findings under overload (arrival rate 2, capacity 1, every occurrence
individually servable in one step):

- Eventual service SURVIVES overload for deadline-free specs: FIFO
  services the n-th occurrence at a finite time while its waiting time
  diverges (`test_fifo_eventual_service_with_diverging_wait`).
  Overload refutes bounded latency, not liveness. This sharpens the
  predecessor round's overload note, which refuted an unconditional
  *deadline*, into a clean separation of properties 3 and 4.
  FINITE-TEST-SUPPORTED; the general FIFO statement is DERIVED
  (service index n at time ~n, arrival at n/2).

- Eventual service FAILS under overload for perishable specs
  (certificates valid only within a window of accrual): pigeonhole
  over receipts, checked exhaustively over every schedule at a small
  horizon (`test_perishable_specs_defeat_every_policy`).
  COUNTEREXAMPLE. So "unconditional dynamic liveness" is false exactly
  when specs carry deadlines — the property is spec-relative, which is
  why it cannot be a core law.

- Low cost and low latency are further independent axes: the SCD
  translation carries both cost kinds, and the predecessor round's
  two-competitive starving policy already separates competitive cost
  from nonstarvation; this round does not re-prove it.

DEFINITION (schedulability, stated but not developed):
`Schedulable(A_class, Gamma, capacity)` — every arrival stream in the
class admits a policy giving eventual certified service. The
perishable counterexample shows any positive theorem needs a load
bound relative to spec windows; finding the sharp condition is OPEN.

## Liveness targets by fragment

- Fixed finite docket, finite state: reachability (individual) and
  generalized reachability = reachability with absorbing acceptance
  (joint). DERIVED, solver-implemented.
- Recurrent finitely-typed coalescing service: Request-Response
  condition on the compiled arena
  (`tests/test_rr_compilation.py`); the paper's Buechi reduction and
  mean-payoff value theory then apply to the compiled game.
  FINITE-TEST-SUPPORTED at play level; strategy-level transfer
  CONJECTURE (not implemented).
- Identity-bearing multiplicity without coalescing: outside both;
  the open-occurrence count is an unbounded counter. OPEN whether a
  useful decidable fragment exists between coalescing RR and full
  unboundedness.

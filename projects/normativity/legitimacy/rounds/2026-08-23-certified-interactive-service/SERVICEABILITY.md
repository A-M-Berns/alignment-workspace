# Serviceability, joint serviceability, schedulability

Status: **research memo; unregistered**. Base definitions use
deterministic policies, adversarial environments, finite response sets,
and no fairness assumption; refinements are noted where they matter.

## The notion lattice

After the validity/closure split (`CERTIFICATION_CLEANUP.md`), the
word "service" is retired in favor of:

```text
ever-certifiable(d, h)      some continuation reaches Certifiable
forceable(d, h)             = Servable: a policy forces Certifiable
                            against every permitted response
timely-closable(d, h)       a policy forces reaching a moment where
                            some certificate is valid AND admissible
eventually-closed(d, rho)   on the actual run, the upstream record
                            performed the closure account
bounded-latency             quantitative annotation on any of these
```

Separations: ever vs forceable —
`test_unservable_when_adversary_can_evade` (some run certifies, none
forced); forceable vs timely-closable —
`test_deadline_in_admit_defeats_timely_closure_only`; timely-closable
vs eventually-closed — closure is an upstream act the layer cannot
perform (boundary, `HANDOFF.md`). For `LapseFree` specs, forceable
and timely-closable coincide, which is why the distinction was
invisible in the prior-art embeddings.

## Individual serviceability

DEFINITION. For liability `d` at history `h`:

```text
Servable(d, h)  iff  exists policy pi such that every Gamma-run
extending h consistent with pi reaches some finite t and certificate c
with ValidCert(sigma_d, rho<=t, c).
```

`Servable` targets HISTORICAL certifiability — the monitors' absorbing
acceptance is the monotonicity theorem in implementation form — not
present closure admissibility; for freshness-windowed `Admit` the two
differ and timely closability would need admissibility-aware monitors
(noted, not built).

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
certifiability of every occurrence in the finite multiset `D`. With
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
individually forceable in one step), stated in the notion lattice —
what overload defeats depends on where the deadline is typed:

- No deadline: eventual certifiability and eventual closure both
  SURVIVE overload under FIFO; only bounded latency fails — the
  waiting time of the n-th occurrence diverges
  (`test_fifo_eventual_service_with_diverging_wait`). This sharpens
  the predecessor round's overload note, which refuted an
  unconditional *deadline*. FINITE-TEST-SUPPORTED; the general FIFO
  statement is DERIVED (service index n at time ~n, arrival at n/2).

- Deadline in `Check` (a receipt-index window — citation-local, so
  the induced `Certifiable` is still monotone, merely time-barred):
  overload defeats FORCEABLE CERTIFIABILITY itself — pigeonhole over
  receipts, checked exhaustively over every schedule at a small
  horizon (`test_deadline_in_check_defeats_certifiability`).
  COUNTEREXAMPLE.

- Deadline in `Admit` (freshness-windowed closure): overload defeats
  TIMELY CLOSABILITY while every occurrence remains eventually
  certifiable — late historical service is real service history, just
  not a discharge instrument
  (`test_deadline_in_admit_defeats_timely_closure_only`).
  COUNTEREXAMPLE for the timely notion, POSITIVE for the historical
  one.

So "unconditional dynamic liveness" is false exactly when specs carry
deadlines, and which liveness notion fails is fixed by the deadline's
type — which is why none of this can be a core law.

- Low cost and low latency are further independent axes: the SCD
  translation carries both cost kinds, and the predecessor round's
  two-competitive starving policy already separates competitive cost
  from nonstarvation; this round does not re-prove it.

DEFINITION (schedulability, stated but not developed):
`Schedulable(A_class, Gamma, capacity)` — every arrival stream in the
class admits a policy giving the chosen liveness notion (eventual
certifiability, or timely closability — a schedulability claim must
name one). The deadline counterexamples show any positive theorem
needs a load bound relative to spec windows; finding the sharp
condition is OPEN.

## Liveness targets by fragment

- Fixed finite docket, finite state: reachability (individual) and
  generalized reachability = reachability with absorbing acceptance
  (joint). DERIVED, solver-implemented.
- Recurrent finitely-typed coalescing service: Request-Response
  condition on the compiled arena
  (`tests/test_rr_compilation.py`) — the RR condition is EVENTUAL
  HISTORICAL certifiability per coalesced occurrence, not timely
  closure; the paper's Buechi reduction and mean-payoff value theory
  then apply to the compiled game. FINITE-TEST-SUPPORTED at play
  level; strategy-level transfer CONJECTURE (not implemented).
- Identity-bearing multiplicity without coalescing: outside both;
  the open-occurrence count is an unbounded counter. OPEN whether a
  useful decidable fragment exists between coalescing RR and full
  unboundedness.

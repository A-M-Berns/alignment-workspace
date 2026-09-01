# Allocated service, realized force, and what is predictable

## 1. The within-round dependency structure

Extracted from the enforcement round's model and enforcement documents, not from
prose about them.

```text
  F_{t-1}: settled record D_{t-1}, price history P_{<t},
           the source's computable volume bound C^tf_t, maker slack eps_t
      |
      v
  (1) docket: which rows (c_j, r_j) are active at t                [predictable]
      |
      v
  (2) tolerance schedule delta_t                                   [predictable]
      |
      v
  (3) intensities  a_{t,j} = beta_{t,j} = (eps_t + C^tf_t)/delta_t^2   [predictable]
      |
      v
  (4) control law  kappa_t : P |-> sum_j a_{t,j} g_j(P) c_j        [predictable]
      |             continuous in P; a legal day-t Strategy
      |
      +--> (5) ordinary TradingFirm strategy tau_t : P |-> tau_t(P)
      |
      v
  (6) aggregate demand  zeta_t(P) = tau_t(P) + kappa_t(P)
      |
      v
  (7) MarketMaker fixed point  P_t   with  maxgain(zeta_t(P_t), P_t) <= eps_t
      |
      v
  (8) realized violation  d_{t,j} = g_j(P_t)                       [endogenous]
      realized position   E_t = kappa_t(P_t)                       [endogenous]
      realized force      f_{t,j} = a_{t,j} d_{t,j}                [endogenous]
      |
      v
  (9) settlement refines D_t; the live set A_t shrinks; the account
      increment is evaluated at each omega in A_t                  [later]
```

Three readings the graph settles.

**`beta` is genuinely predictable.** The source says so twice and for two
different reasons: the intensity "is a rational constant computed from
`p_{<=n-1}` before the strategy is emitted, and enters as `const`", and the
volume bound `M_n <= C^tf_n` is the source's own computable bound produced from
the belief history, so "the intensities can be chosen **adaptively at date `n`**
— set `beta_j = (eps_n + C^tf_n)/delta_n^2` for any schedule `delta_n`".

**The control is a law, not a position.** The same passage states the constraint
exactly: "What cannot be done is choosing `beta` from the observed violation: the
enforcement trader is a strategy, a function of prices, and its intensities are
fixed before the market maker picks a price." A day-`t` strategy is determined by
share coefficients that may depend continuously on the displayed prices, and that
continuity is what the fixed point's Brouwer step consumes. So the object chosen
from `F_{t-1}` is

    kappa_t : X_t -> U_t ,    continuous,

and the realized control `u_t = kappa_t(P_t)` is not `F_{t-1}`-measurable.

**Exactly one class of variables may depend on the contemporaneous price**: the
realized position and everything computed from it — the violation, the force, the
work, the account increment. The docket, the tolerance, the intensities and the
law may not.

## 2. The round's affordability definition is mistyped

`AFFORDABILITY.md` clause 1 requires `(w_t, u_t)` to be chosen from `F_{t-1}` with
`u_t = sum_r w^r_t zeta^r_t`. In the realization the round names, neither
coordinate is predictable: `zeta^r_t` is a function of `P_t`, and `w^r_t` was read
as `beta_{t,j} g_{t,j}(P_t)`, which is the violation at the fixed point.

This is not a presentational slip. Clause 2 asks for a transport plan whose
service marginal is `w`, and the composition theorem asks for `W^r_N -> infinity`.
Both are requirements on a quantity no scheduler can set. Two exact failures:

- **Perfect compliance.** Allocate `a_t = 1` at every date to a reason the
  reasoner never violates. Then `w_t = a_t d_t = 0` at every date, the service
  measure `nu_N` is division by zero, and the reason that received full attention
  forever is not merely recorded as starved — it has no service measure at all.
  `tests/test_service.py::RealizedForceIsNotService` raises on it.
- **Successful learning.** Allocate `a_t = 1` forever against a violation
  `d_t = 2^-t`. Then `A_N = N -> infinity` while `W_N = sum a_t d_t < 2`. The
  round's persistent-relevance condition fails exactly when the norm is being
  satisfied, which inverts what Answerability is trying to express.

## 3. The corrected types

    a_{t,j}       allocated authority           predictable, chosen
    kappa_t       control law, continuous       predictable, compiled from (docket, a)
    P_t           displayed state               the fixed point
    d_{t,j}       realized violation            endogenous
    f_{t,j}=a d   realized force                endogenous
    a d^2         work                          endogenous, and what the modulus bounds
    a d s(omega)  misfit charge at a world      endogenous, settled later

The schematic control type becomes

    kappa_t in ControlLaw_t ,   kappa_t chosen from F_{t-1} ,   u_t = kappa_t(x_t) ,

with `ControlLaw_t` carrying whatever regularity the engine's fixed point needs —
continuity, in the traderized case. This matches the construction rather than
being imposed on it, and it is the minimal change: the affordability witness stops
quantifying over realized controls and starts quantifying over the laws that
produce them.

## 4. Which quantity is "service"?

**Verdict: service is `a = beta`.** Five reasons, in the order of how much they
matter.

**It is the only predictable candidate.** A service obligation a scheduler cannot
meet is not an obligation. `A_N -> infinity` is schedulable; `sum a_t d_t ->
infinity` is a demand on the market's behaviour.

**It is total.** `nu^a_N` is defined whenever any authority was allocated. The
force measure is undefined exactly on the trajectories the theory most wants to
call well served.

**It tracks attention rather than failure.** Two dates with equal allocated
authority and violations `1/10` and `9/10` split the allocation measure evenly and
the force measure `1 : 9`. Saying the second date received nine times the service
because the reasoner was worse on it inverts the normative reading: the reasoner's
failure is not the reason's entitlement.

**It is what the enforcement theorem is about.** The modulus bounds
`sum_j a_{t,j} d_{t,j}^2` per date, which is `a`-weighted by construction. Nothing
in the traderized mathematics bounds an `f`-weighted quantity.

**It preserves the distinctions the workspace insists on.** Five objects, kept
apart:

| object | what it is | predictable |
|---|---|---|
| allocated authority `a` | attention, the scheduler's variable | yes |
| work `a d^2` | corrective effort actually expended | no |
| realized position `a d` | exposure taken at the fixed point | no |
| liability | the signed cumulative account over live worlds | settled later |
| funding | cumulative worst-case exposure an outside funder stands behind | no, and explicitly not the scarce resource |

The round collapsed the first three. The source's warning that intensity is not
funding is the fourth and fifth being kept apart, and it survives: what `a` buys
is not exposure but **conformance precision**, `d_j <= sqrt((eps_t + M_t)/a_j)`.
The adversarial fixture in which the realized position is identical across
`beta in {10, 100, 1000}` is the same point from the other side, and it is why
realized position cannot be the service variable.

## 5. Answerability's actual control

Of the three possibilities the dispatch lists, **free scheduling inside an
explicit capacity box** is what holds.

`beta` and the promised tolerance `delta` are in bijection at fixed
`(eps_t, C^tf_t)`, so choosing one is choosing the other, and either may be set on
any schedule. What bounds the choice is liability: inverting the round's
conformance/liability trade `delta_t >= (eps_t + M_t) D_t / b_t` against a per-date
allowance `b_t` gives

    a_t  <=  b_t^2 / ( (eps_t + M_t) D_t^2 )  =:  cap_t ,

with `D_t` the worst live-world exclusion depth. So Answerability chooses
`a_t in [0, cap_t]`, an interval — hence a convex capacity region in `a`-space,
which is the type the existence theory wanted and could not previously state.

Two caveats, both real. The cap comes from the per-date-supremum certificate,
which the source records as conservative relative to the worldwise account, so it
under-reports the available authority. And the bijection means allocating little
authority *is* promising a loose tolerance: a reason cheaply served is a reason
whose violation is cheaply tolerated, which is the right normative reading but
means "service" and "demandingness" are not independent dials.

## 6. What this does not establish

That a scheduler meeting `A^r_N -> infinity` for every persistent reason inside
the caps exists — that is the existence problem, now stated in the right space.
That the caps are tight; they invert a sufficient liability certificate. That
`beta > 0` is available for every reason at every date: the enforcement theorems
require positive intensity per enforced row, and a date's docket is finite.

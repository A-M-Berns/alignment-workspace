# Local authority capacity is not lifetime safety

## 1. Two objects

**Local authority capacity** `C_t(h_{t-1})` is a predictable set of allocations
available on date `t`. It is a fact about one date, computable before the market
maker picks a price.

**SafeCert** is a property of the realized account over the whole history:

    V_N(omega) >= -B     for every N and every omega live at N.

It is not predictable, not per-date, and not a set of allocations.

> Local capacity says what authority may be allocated now; SafeCert says whether
> the entire resulting reactive-control history remains underwritten.

Neither implies the other, and the round's earlier text ran them together.

## 2. Why they come apart, in both directions

**Capacity at every date does not give SafeCert.** Choose a per-date allowance
`b_t = 1` and allocate at the cap every date. Each date is inside its own local
capacity set by construction, and the account's floor is exactly the horizon.
`tests/test_reasonwise.py::LocalCapsAreNotLifetimeSafety` pins it at horizons up to
128, against the summable schedule where the same construction stays under `1`. The
missing ingredient is not per-date discipline but **summability**.

**SafeCert does not require staying inside the capacity set.** The cap inverts a
*worst-case* charge, `sqrt(a (eps_t + M_t)) · D_t`, taken over the worst live world
and the worst violation the modulus permits. A realized trajectory can exceed the
cap at many dates and still keep its account above the floor, because the realized
world is not the worst one and the realized violation is not the largest one. The
round already carries an instance of the same shape: a region excluding the sole
live world at every date, enforced forever, whose cumulative liability converges.

So the capacity set is a **predictable sufficient condition on one date's
contribution**, and nothing more.

## 3. Route A — conservative budget splitting

Choose a predictable allowance schedule `b_{t,j} >= 0` with
`sum_{t,j} b_{t,j} <= B` and allocate inside

    C_t^A  =  { a : a_{t,j} <= b_{t,j}^2 / ( (eps_t + M_t) D_{t,j}^2 ) } .

**Theorem C1.** Any policy with `a_t in C_t^A` at every date satisfies SafeCert at
budget `B`, and the per-row floors of `REASONWISE_ACCOUNTING.md` R1 hold with
`B_j = sum_t b_{t,j}`.

*Proof.* The date's worst-case charge on row `j` is
`sqrt(a_{t,j}(eps_t + M_t)) · D_{t,j} <= b_{t,j}` by the definition of the cap;
summing over rows and dates gives every prefix at least `-B`, and summing over
dates alone gives the per-row floor. `square`

This is the sum-of-suprema route. It is sufficient, it delivers R1's floors for
free, and the source records it as conservative: the criterion follows one world
through time while the certificate takes a fresh supremum at each date.

## 4. Route B — the signed account, spent against realized slack

Track the account and let earlier gains fund later losses. With

    sigma_t  =  B + min_{omega in A_{t-1}} V_{t-1}(omega)

the realized slack at the start of date `t`, put

    C_t^B(h_{t-1}, V_{t-1})  =  { a : sqrt(a_{t,j}(eps_t + M_t)) · D_{t,j}
                                      summed over j  <=  sigma_t } .

**Theorem C2.** Any policy with `a_t in C_t^B` satisfies SafeCert at budget `B`.

*Proof.* The date's worst-case total charge is at most the slack, so the account
cannot cross `-B` on that date; induct. `square`

C2 is the same inequality as C1 with the exogenous allowance replaced by the
realized slack, and it is **strictly larger** whenever the account has earned.
Because the cap is quadratic in the allowance, the gap is quadratic too: with
`B = 1`, budget `1` and depth `1/2`, splitting the lifetime budget over two dates
gives each a cap of `1`, while a first date that earns `1/4` leaves the second a
cap of `25/4` — a factor of `25/4`. `tests/test_reasonwise.py::SignedAccountBeats\
PerDateBudgeting` pins it.

Two honest limits. C2 gives no lower bound on `sigma_t`: an account that never
earns shrinks its own capacity to nothing, and the policy stalls with `A_N`
bounded. And the account earns exactly when `d > s` — when the reasoner is further
from the norm than the world is — so a controller that over-enforces past the
world's own misfit spends rather than earns. Pushing conformance below the
settlement friction is what costs money, which is the same fact
`LI_PROGRESS_FROM_SERVICE.md` records as the friction residual, seen from the
account side.

## 5. Route C — structural certificates with no allowance sequence

Three certificates already in the workspace discharge SafeCert without any `b_t`.

**World-inclusive rows.** If every live world satisfies every row then
`D_{t,j} = 0`, every increment is nonnegative, and the account never falls: the
capacity set is everything and `B = 0`.

**Covered underwriting.** A `theta`-covered mixture over the assessed profiles
whose barycenter lies in every active region gives the floor `U(1-theta)/theta`
directly, with no per-date accounting at all.

**Exposure-bounded schedules.** Finitely many active dates, or summable gross
inventory, bound the account by bounding the positions rather than the charges.

All three plug into the same interface: they are ways of establishing SafeCert, and
the composition theorem consumes only SafeCert. That is the point of keeping the
interface at "the account stays above a floor" rather than at "a per-date budget was
respected".

## 6. Which one the affordability definition should carry

The definition carries **SafeCert**, and the capacity sets are how a *policy*
establishes it. Writing a capacity set into the definition would make the
affordability of a history depend on which sufficient certificate its scheduler
happened to use, and would exclude Route C entirely.

The existence problem, correspondingly, is stated over policies constrained by
`C_t^B` (or `C_t^A` for the conservative version), not over histories constrained by
SafeCert — see `AFFORDABLE_SCHEDULING.md`.

## 7. What this does not establish

That `C_t^B` is nonempty above zero at every reachable state; it is exactly as
large as the accumulated slack, and nothing here shows the slack stays positive.
That the worst-case charge is tight — it is the certificate's charge, and the
realized one is smaller. That Route C's certificates are available for any
particular normative practice.

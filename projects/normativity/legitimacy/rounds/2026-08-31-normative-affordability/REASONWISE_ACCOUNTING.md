# From an aggregate cap to a reason-indexed one

## 1. The decomposition is by row, not by reason

The compiled position is `sum_j beta_j g_j(P) c_j`, so the enforcement book and
its assessed account decompose over **rows**:

    E_t = sum_j E_t^j ,     V_N(omega) = sum_j V_N^j(omega) .

Reasons are a partition of rows, so every statement below is about an arbitrary
subset `S` of rows and specializes to a reason. That is the cleaner
formulation the dispatch asks for: it needs no reason labels, it survives a
reason owning several rows, and it makes the constants uniform.

**Lemma R1 (subset ceiling).** Suppose at a live world `omega` and horizon `N`

    V_N(omega) <= U           (the aggregate market maker cap)
    V_N^j(omega) >= -B_j      for every row j, with sum_j B_j <= B_tot < infinity.

Then for every `S subseteq J`,

    V_N^S(omega) := sum_{j in S} V_N^j(omega)  <=  U + B_tot .

*Proof.* `V_N^S = V_N - V_N^{J\S} <= U + sum_{j not in S} B_j <= U + B_tot`. `square`

The bound is uniform in `S`, so `U_r = U + B_tot` for every reason — better than
the reason-specific `U + sum_{k != r} B_k` the dispatch proposed, and derived the
same way.

**The floors subsume the aggregate SafeCert.** Per-row floors give
`V_N = sum_j V_N^j >= -B_tot`, which is the preservation theorem's hypothesis with
`B = B_tot`. So a hypothesis list carrying per-row floors should not also carry an
aggregate floor.

## 2. Aggregate safety does not bound a reason book

**Countermodel A1.** Two rows, increments `+1` and `-1` at every date. The
aggregate account is identically zero, so the aggregate cap holds at `U = 0` and
the aggregate SafeCert holds at `B = 0`. The first book's ceiling is exactly the
horizon and the second's floor is exactly the horizon: neither is bounded.
`tests/test_reasonwise.py::AggregateSafetyDoesNotBoundAReasonBook` pins all four
quantities at horizons up to 64.

So R1's per-row floors are not decoration. Without them, one reason's authority can
be financed by another's unbounded losses while every aggregate condition holds,
and the reason-indexed ceiling — hence the reason-indexed Progress bound that runs
through it — is unavailable.

The normative reading, stated at the strength the mathematics supports: aggregate
solvency permits cross-subsidy between reasons, and cross-subsidy is what defeats
*this route* to a per-reason ceiling. It does not defeat per-reason Progress, which
Route III below obtains from the per-date modulus with no decomposition at all.
Separate underwriting is what buys the good constant, not what makes the conclusion
available.

## 3. Three routes to reason-indexed Progress, and none of them is the only one

Write `Q^S_N = sum_{t<N, j in S} a_{t,j} d_{t,j}^2` for a subset's cumulative work
and `A^S_N = sum a_{t,j}` for its allocated service. **Every work term is
nonnegative**, which is the structural fact all three routes use.

**Route I — per-row floors.** By R1, `Q^S_N <= U + B_tot + sum_{S} a d s^+(omega)`,
so the friction charge is the subset's *own*. This is the route with the best
residual and it is what §5 of `FIXED_ERA_THEOREM.md` uses.

**Route II — aggregate cap only.** `Q^S_N <= Q_N <= U + sum_{J} a d s^+(omega)`,
because dropping nonnegative terms only decreases the left side. No floors needed,
but the residual is the *aggregate* misfit charge divided by the subset's own
allocation, so a reason with a small allocation inherits every other reason's
friction.

**Route III — unconditional modulus.** The per-date enforcement modulus gives
`sum_j a_{t,j} d_{t,j}^2 <= eps_t + M_t` at every date with no world quantifier at
all, so `Q^S_N <= S_N := sum_{t<N}(eps_t + M_t)`. This needs nothing but the market
maker's contract and a nonempty region, and it costs a growing constant instead of
`U + B_tot`.

So a reason-indexed Progress statement never *requires* the decomposition: Route
III always applies. What the decomposition buys is the constant — `U + B_tot`
rather than `S_N`, which is what turns a rate of `S_N/A^r_N` into `1/A^r_N` and
therefore what decides whether a reason with modest allocation progresses at all.

## 4. Growing and countable dockets

R1 needs `sum_j B_j <= B_tot` over every row ever active before `N`. Three
consequences.

**Countably many reasons are fine, with summable budgets.** A reason arriving late
must be granted a small liability budget. That is not a service restriction: by the
square-root exposure relation the charge is `sqrt(a (eps + M)) · s^+`, so a small
budget still buys divergent allocated service provided the row's misfit decays.
Budget and service are decoupled, which is what makes summability affordable.
`tests/test_reasonwise.py::SubsetCapFromComplementaryFloors` exhibits a
three-row instance with total floor under `1/2`.

**A single global budget may be split dynamically.** The floors need to hold at
every horizon, so a predictable assignment `B_j(N)`, nondecreasing in `N` with
`sum_j B_j(N) <= B` for every `N`, discharges R1 with `B_tot = B`. This is strictly
more flexible than fixed per-row budgets and is the right interface: Answerability
allocates authority, and the affordability layer allocates liability budget, both
predictably.

**What fails is an unbounded number of non-shrinking budgets.** With `B_j = b > 0`
for infinitely many rows, `B_tot = infinity` and R1 is vacuous; Route III still
applies, so Progress survives at the worse constant.

## 5. Aggregate Sustainable Progress, stated separately

There is a clean aggregate theorem and it should not be forced through reason
labels.

**Theorem A2 (pooled Progress).** With `nu^a_N` the allocated-service measure over
all active row-dates, `A_N -> infinity` and either the aggregate cap or the
modulus,

    E_{nu^a_N}[d]  <=  || s^+(omega) ||_{L^2(nu^a_N)}  +  sqrt( U / A_N ) ,

and unconditionally `<= sqrt(S_N / A_N)`.

**Corollary A3 (share route).** If in addition `liminf_N A^S_N / A_N >= rho > 0`
then `E_{nu^{a,S}_N}[d] <= sqrt( (1/rho) · Q_N / A_N )`. The share condition is now
a condition on *predictable* quantities, so unlike the version this round first
wrote it is something a scheduler can guarantee.

**The strongest condition under which an aggregate cap gives every persistent
reason Progress** is therefore: `A^r_N -> infinity` for each `r`, together with
either (i) per-row floors summing to a finite `B_tot`, or (ii) a positive
asymptotic allocation share for each `r`, or (iii) `A^r_N / S_N -> infinity`.
These are incomparable — (i) is a liability condition, (ii) and (iii) are
scheduling conditions — and (iii) requires nothing beyond the market maker's
contract.

## 6. What this does not establish

That the per-row floors hold; they are hypotheses, and whether a schedule can
maintain them is `AFFORDABLE_SCHEDULING.md`. That `U = C + B_F` is the right
constant outside the current composition. That reasons partition rows in any
practice's docket — the theory permits a row to serve several reasons, in which
case the subsets overlap and R1 still applies to each but the budgets are shared.

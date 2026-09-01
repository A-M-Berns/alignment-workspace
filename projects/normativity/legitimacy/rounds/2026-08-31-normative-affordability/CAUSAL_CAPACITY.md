# Causal capacity: the rate region was the wrong object

## 1. The convexity claim is false, and the error is diagnosable

`AFFORDABLE_SCHEDULING.md` §6 claimed that the sustainable authority-rate region

    A = { lambda : some causal SafeCert policy has liminf_N A^r_N / N >= lambda_r }

is convex because policies can be time-shared. That is wrong, and not for the
history-dependence reason the dispatch suspected.

**Time-sharing convexifies a renewable per-date resource. The liability budget is
a consumable stock.** Interleaving two policies splits the stock, and authority is
*quadratic* in the stock — `A^max = B^2/(min q)^2` by `PERSISTENT_AFFORDABILITY.md`
P2 — so splitting a budget in half quarters the authority it buys. Convexity was
imported from queueing, where the shared resource is a per-slot server that
replenishes every date and where interleaving is therefore free.

**The exact counterexample is two lines.** Two rows, friction `1` each, lifetime
budget `2`. The achievable cumulative-authority pairs are
`{(x_1^2, x_2^2) : x_1 + x_2 <= 2}`. So `(4, 0)` and `(0, 4)` are achievable and
their midpoint `(2, 2)` is not: it needs `x_1 = x_2 = sqrt(2)` and
`2 sqrt(2) > 2`. `tests/test_reasonwise.py::ConcentrationBeatsSplitting` pins the
arithmetic.

So the correction is not a caveat: the time-sharing argument is invalid, because
what it needs is a renewable per-date resource and what the theory has is a stock.

**What the counterexample establishes, exactly**, is that the *finite-horizon
cumulative-authority frontier* `{(x_r^2)_r : sum_r x_r <= B}` is non-convex. It
does **not** establish that the long-run rate region is non-convex, and the earlier
sentence claiming `A` is non-convex wherever non-degenerate is withdrawn: under a
floored friction every long-run rate is zero and `A = {0}`, which is convex, and
under fast-decaying friction `A = R_+^R`, also convex. The rate region's geometry is
model-dependent, and §2 argues it is the wrong object to be studying at all.

## 2. And where it is degenerate, it is uninformative

Worse, the rate region is usually trivial, and trivial in a way that hides the
property the theory actually needs.

**If the friction is floored,** `q_t >= q_0`, then `sum_t a_t <= (B/q_0)^2` at
every horizon, so `A_N/N -> 0` and `A = {0}`.

**If the friction decays fast,** say `q_t = 2^-t`, then `a_t = t^2` is affordable
and `A_N/N -> infinity`, so `A = R_+^R` for any finite or countable reason set,
by splitting the budget geometrically.

**In between, `A = {0}` while the theory's requirement holds.** Take
`q_t = 1/log t`. The schedule `a_{t_k} = k` at `t_k = e^{k^2}` has charge
`sum_k k^{1/2}/k^2 < infinity` and `sum_k k = infinity`, so the reason is
persistently served — but `A_N ~ (log N)/2`, so the rate is zero and `A` records
nothing.

Persistence is `sum_t a_t = infinity`; positive rate is `A_N = Omega(N)`. The
composition theorem consumes the first. The rate region sees only the second, and
reports `{0}` in the regime the theory most cares about.

**The hierarchy worth keeping.** The finite-horizon cumulative-authority frontier
is a real object and is often non-convex. The persistence set is simple in the
exogenous conservative benchmark. The long-run rate region is model-dependent and
is not consumed by the composition theorem, so it is de-emphasized rather than
repaired.

## 3. The right object: the persistence region

Define

    P  =  { S subseteq R : some causal SafeCert policy has A^r_N -> infinity
                           for every r in S } .

Three facts, and together they say `P` has no interesting structure — which is the
result.

**Downward closed.** Serving a subset is easier; allocate zero to the rest. This is
the one closure property that is automatic, and it is the one the earlier text
should have claimed instead of convexity.

**Determined by a per-reason predicate.** By P1, `r` is individually persistable
iff `liminf_t q^r_t = 0`.

**Closed under countable unions.** P1 does not mention the budget, so splitting `B`
as `B 2^{-r}` leaves every reason's criterion intact. Hence

    P  =  2^{R*} ,     R* = { r : liminf_t q^r_t = 0 } .

`P` is the full power set of the persistable reasons: a principal down-set, with no
Hall-type condition, no capacity region, and no convexity question.
`tests/test_persistence.py::ManyReasonsDoNotCompeteForPersistence` exhibits five
reasons on geometric tranches of one budget, each still diverging.

**Persistence does not compete.** The quadratic dependence on the budget is real
and shapes the finite-horizon frontier; it does not touch the qualitative property
the composition theorem consumes.

## 4. When does time-sharing work?

**Theorem C1.** Suppose the liability allowance is a *renewable flow* rather than a
stock: a predictable `b_t > 0` with `sum_t b_t = infinity` bounds the charge on
date `t`, and the account is reset or replenished so that only the per-date
constraint binds. Then the long-run achievable rate region is convex, and the
convex combination of two achievable rate vectors is achieved by block
interleaving with block lengths in the corresponding ratio.

*Proof sketch.* With only a per-date constraint the feasible set of long-run
averages is the closed convex hull of the per-date achievable set, and block
interleaving realizes any point of that hull in the limit, since the per-date
constraint is satisfied inside each block and there is no state carried between
blocks. `square`

The hypothesis is exactly what fails in the traderized setting: liability is a
lifetime floor on a signed account, not a per-date renewable allowance. Two further
sufficient structures would restore it, and neither is established here — an
account that provably replenishes at a positive rate, or a per-era reset of the
budget at era boundaries, which is a cross-era question this round has excluded.

**What is genuinely automatic**, with no hypothesis at all, is downward closure of
both `A` and `P`. Everything else about `A` needs C1's flow hypothesis.

## 5. The scalar slack is not sufficient state

Route B of `CAPACITY_VS_SAFETY.md` uses `sigma_t = B + min_{omega live} V_{t-1}(omega)`.
That scalar is not a sufficient statistic, because the world attaining the minimum
can leave the live set.

**Countermodel.** Two worlds. Profile one has `V(w1) = V(w2) = 0`; profile two has
`V(w1) = 0`, `V(w2) = 10`. Both have slack `1` at floor `B = 1`. Settlement then
removes `w1`. The first profile still has slack `1`; the second has slack `11`, and
since viable authority is `slack^2/(m D^2)`, the viable sets differ by a factor of
`121`. `tests/test_persistence.py::TheScalarSlackIsNotSufficientState`.

So the sufficient statistic is **the account profile restricted to the live set**,
and the minimum compresses it only when settlement carries no information about
which world is worst — for instance when the live set never shrinks, or when the
profile is constant on it. Any dynamic-programming formulation of affordability has
to carry the profile, which makes the state space as large as the live set. That is
a real obstacle to a viability-kernel treatment and is worth knowing before anyone
attempts one.

## 6. What this does not establish

Anything about the long-run rate region's geometry beyond the two degenerate
regimes of §2; the non-convexity established here is of the finite-horizon
cumulative-authority frontier. That the persistence region is the *only* useful
object; a quantitative theory would want the growth rate of `A^r_N`, which does
compete. That
the profile cannot be compressed under some structural hypothesis on settlement;
none is offered here.

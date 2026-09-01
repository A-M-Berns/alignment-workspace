# Bounded-delay affordability: the minimum-cost service problem

## 1. The problem, and why feasibility is not the obstacle

When the service profile is *chosen* rather than given, transport feasibility is
free — set `a_s` to whatever the plan places there. The whole content is the cost:

    Cost_H(c, L)  =  inf { sum_s L_s(a_s) : (a, T) is a bounded-delay plan } .

`L_s` is increasing, vanishes at zero and is star-shaped. On the sharp traderized
charge's linear branch, `L_s(a) = w_s a` with `w_s = s_s^2/4`, which is the regime
every fixture here uses.

## 2. The structure of an optimal plan

**Lemma D1 (no splitting; needs concavity).** With every `L_s` concave, no claim
gains by dividing its mass between two legal dates. Moving `delta` of a claim's mass
from `s_1` to `s_2` changes the cost by
`-[L_{s_1}(A_1) - L_{s_1}(A_1 - delta)] + [L_{s_2}(A_2 + delta) - L_{s_2}(A_2)]`,
whose derivative in `delta` is `-L'_{s_1}(A_1 - delta) + L'_{s_2}(A_2 + delta)`.
Both terms are nonincreasing in `delta` because the costs are concave, so the cost
is a concave function of `delta` and attains its minimum at an endpoint — all of the
mass at one date. `square`

**Star-shapedness is not enough here, and the earlier proof of D1 was wrong.** It
compared cost *levels* at the two dates, which is valid only when neither date
carries other load; with other load the comparison is between *increments*, which
star-shapedness does not control. Two legal dates each already carrying load `1`,
a claim of mass `2`, and the star-shaped non-concave cost `min(a,1)` up to `2` then
`a/2`: the atomic assignment costs `3/2 + 1 = 5/2` and the even split costs
`1 + 1 = 2`. `tests/test_joint_service.py::SplittingCanBeatAtomicAssignment`.

**Lemma D2 (monotone service; needs equal claim masses).** With all claim masses
equal, an optimal plan can be taken to serve claims in arrival order: if `i < j` are
served at `s_i > s_j` then each date is legal for both claims, by the computation of
`BOUNDED_DELAY_TRANSPORT.md` BD2, and swapping equal masses leaves both dates' loads
unchanged, hence leaves the cost unchanged.

**With unequal masses a crossed assignment can strictly win, even for concave
costs.** Claim one of mass `1` at date `1` with window `[1,3]`, claim two of mass
`10` at date `2` with window `[2,4]`; date two's cost `min(a, 1 + a/100)` saturates
and date three's `a/2` does not. Crossed — the big claim at the saturating date —
costs `1/2 + 11/10`; monotone costs `1 + 5`.
`tests/test_joint_service.py::CrossedAssignmentCanBeatMonotone`.

**Theorem D3 (exact minimum cost, for concave costs and equal claim masses).**
`Cost_H` is the shortest path in the directed acyclic graph whose vertices are claim
indices and whose edge `i -> j+1` has weight

    min { L_s( sum_{k=i}^{j} c_k )  :  s in [t_j, t_i + H] } ,

present only when `t_j <= t_i + H`. `min_cost_dp` computes it.

**The hypothesis hierarchy**, with each theorem at its exact strength:

| result | needs |
|---|---|
| persistence S1 | star-shaped |
| finite-horizon concentration S2 | star-shaped |
| no splitting D1 | concave |
| monotone runs D2, hence D3 | concave **and** equal claim masses |
| closed form D4 | linear |

D4 needs neither, because a linear cost is load-independent and each unit of claim
mass is priced separately.

## 3. The closed form on the linear branch

**Theorem D4.** If `L_s(a) = w_s a` then

    Cost_H(c)  =  sum_t  c_t · min_{s in [t, t+H]} w_s ,

achieved by serving each claim at the cheapest date in its own window.

*Proof.* Each claim's mass must be carried at some legal date, costing at least
`c_t` times the window minimum; the per-claim plan attains it, and by D1 no
splitting improves on it. `square`

So on the linear branch the answer is a **sliding-window minimum**, and batching is
worth nothing — a linear cost has no volume discount, so the only decision is which
date each claim uses. `min_cost_dp` and `min_cost_linear` are checked to agree on a
dip sequence at every delay from `0` to `4`.

Batching earns its keep only past the branch point `4 m_s / s_s^2`, where the sharp
charge becomes strictly concave and a larger batch is cheaper per unit than two
smaller ones at the same date. D3 covers that case and D4 does not.

## 4. The affordability criterion, for every claim stream at once

D4 is uniform in the claim process, so the three cases the dispatch separates are
one formula.

> **Bounded-delay affordability.** On the linear branch, a claim stream `c` is
> serviceable within delay `H` on lifetime budget `B` if and only if
>
>     sum_t c_t · min_{s in [t, t+H]} w_s   <=   B .

**Unit claims** `c_t = 1`: the criterion is that the sliding-window minima are
summable. **Bounded claims** `c_t <= C`: the same, weighted. **Sparse claims**: the
same, with most terms absent — a claim stream of density `rho` needs the window
minima summable only along its own arrivals.

**The `H -> infinity` reading is withdrawn.** An earlier version of this section
read the limit of D4 as the unconstrained persistence criterion. That is false:
`EVENTUAL_VS_UNIFORM_SERVICE.md` E1 exhibits a weight sequence with `liminf w_t = 0`
— so unconstrained persistence holds and eventual full service costs under `1/2` —
for which `Cost_H = infinity` at every finite `H`, because the gaps between cheap
dates diverge. So `lim_H Cost_H` can strictly exceed the unbounded-delay cost, and
neither equals the persistence criterion. The three problems separate, and E1 and E2
give both separations.

Equality holds when the gaps between cheap dates are bounded by some `G`: then every
window at `H >= G` contains a cheap date and `Cost_H = Cost_infinity`. Claim density
and cheap-date density meet in the sliding window, and the *spacing* of the cheap
dates is what decides whether a uniform deadline can reach them.

## 5. This is not the old disjoint-window theorem

`SERVICE_ADMISSIBLE_EXISTENCE.md` A1 gave a condition on the minima of a **fixed
disjoint blocking**. D4 is the minimum over a **sliding** window, and the two differ
by up to a factor of `H+1`: a block of `H+1` consecutive claims contributes `H+1`
sliding minima, each at least the block minimum. A1 is therefore a correct upper
bound on the truth and not the criterion, and where the two disagree it is because
A1 fixes where the block boundaries fall while the optimum chooses.

A1 also assumed a uniform per-window service floor rather than an actual claim
stream. D4 needs no floor: the claims supply the mass.

## 6. Persistence without serviceability

The separation the pass was looking for is exact. Take date weights pinned at `1`
except at multiples of `16`, where they are `4^-k`, and unit claims.

- **Unconstrained persistence holds**: the geometric tranche schedule of
  `ONLINE_EXISTENCE.md` spends under one unit of budget and allocates without
  bound, because `liminf w_t = 0`.
- **Bounded-delay service at `H = 3` fails**: most claims never see a dip, the
  sliding-window minimum is `1` for at least three quarters of the dates, and the
  cost exceeds `180` by date `240` and grows linearly with the horizon.
- **Widening the deadline to the dip spacing restores it**: at dips every `4` dates
  and `H = 3`, the whole cost is under `4`.

`tests/test_bounded_delay.py::PersistenceWithoutServiceability` pins all four
statements.

So the round's slogan is earned rather than asserted: **unconstrained affordability
asks whether cheap opportunities exist; serviceability asks whether they fall
inside the windows in which the reason is owed an answer.**

## 7. What this does not establish

That `Cost_H` is computable in the closed loop, where `w_s` depends on the policy.
That the DP of D3 is efficient for large horizons — it is quadratic in the number
of claim dates. That non-uniform deadlines preserve the run structure; D2's
exchange uses a uniform `H`. That claims are fungible, which D1 and D2 both use.

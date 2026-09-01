# Bounded-delay affordability: the minimum-cost service problem

## 1. The problem, and why feasibility is not the obstacle

When the service profile is *chosen* rather than given, transport feasibility is
free — set `a_s` to whatever the plan places there. The whole content is the cost:

    Cost_H(c, L)  =  inf { sum_s L_s(a_s) : (a, T) is a bounded-delay plan } .

`L_s` is increasing, vanishes at zero and is star-shaped. On the sharp traderized
charge's linear branch, `L_s(a) = w_s a` with `w_s = s_s^2/4`, which is the regime
every fixture here uses.

## 2. The structure of an optimal plan

**Lemma D1 (no splitting).** No claim gains by dividing its mass between two legal
dates. By star-shapedness, `L_{s_1}(m_1) + L_{s_2}(m_2) >= (m_1/m) L_{s_1}(m) +
(m_2/m) L_{s_2}(m) >= min(L_{s_1}(m), L_{s_2}(m))` for `m = m_1 + m_2`, and both
dates are legal for the whole mass.

**Lemma D2 (monotone service).** An optimal plan can be taken to serve claims in
arrival order. If `i < j` are served at `s_i > s_j`, then `s_j` is legal for `i`
and `s_i` is legal for `j` — the computation of `BOUNDED_DELAY_TRANSPORT.md` BD2 —
so the two dates may be exchanged.

Together: **an optimal plan partitions the claims into consecutive runs, each run
served whole at a single date legal for every claim in it.** A run `[i..j]` has a
legal date iff `t_j <= t_i + H`, and its legal window is `[t_j, t_i + H]`.

**Theorem D3 (exact minimum cost).** `Cost_H` is the shortest path in the directed
acyclic graph whose vertices are claim indices and whose edge `i -> j+1` has weight

    min { L_s( sum_{k=i}^{j} c_k )  :  s in [t_j, t_i + H] } ,

present only when `t_j <= t_i + H`. `min_cost_dp` computes it.

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

**The interpolation back to unconstrained persistence is exact.** As `H` grows the
window `[t, t+H]` grows, the minimum falls, and in the limit it is the infimum over
the tail. So `liminf_t w_t = 0` makes every term zero and the sum vanishes: the
unconstrained criterion of `SHARP_PERSISTENCE.md` is the `H -> infinity` limit of
D4. Claim density and cheap-date density meet in exactly one place, the sliding
window, and nowhere else.

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

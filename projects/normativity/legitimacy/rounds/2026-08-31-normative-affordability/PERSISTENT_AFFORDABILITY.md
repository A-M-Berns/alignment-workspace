# Persistent affordability under the conservative charge

Scoped to the **conservative** worst-case charge and to an **exogenous** friction
sequence. `SHARP_PERSISTENCE.md` generalizes the criterion to an arbitrary
star-shaped date cost and corrects §5 below; `CLOSED_LOOP_EXISTENCE.md` says what
survives when the friction depends on the policy.

## 1. The sequence problem

Write `m_t = eps_t + M_t` for the date's slack-plus-volume, `D_t` for the worst
live exclusion depth of the row, and

    q_t := D_t sqrt(m_t)

for the date's **friction**. The conservative worst-case charge for allocating
authority `a_t` is `sqrt(a_t m_t) D_t = q_t sqrt(a_t)`. Substituting
`x_t = sqrt(a_t)`, a schedule is persistent and affordable on lifetime budget `B`
exactly when

    sum_t x_t^2 = infinity        and        sum_t q_t x_t <= B .

## 2. The answer

**Theorem P1.** Such an `x >= 0` exists if and only if

    liminf_t q_t = 0 .

*Proof.* If `q_t >= q_0 > 0` then `sum_t x_t <= B/q_0`, so `x_t -> 0` and
`x_t <= C := sup x`, whence `sum x_t^2 <= C sum x_t < infinity`. Conversely, if
`liminf q_t = 0`, choose `t_1 < t_2 < ...` with `q_{t_k} <= 2^-k` and set
`x_{t_k} = B 2^{-(k+1)} / q_{t_k} >= B/2`, zero elsewhere. Then
`sum q x = B sum 2^{-(k+1)} <= B` and `sum x^2 >= sum_k B^2/4 = infinity`. `square`

**Theorem P2 (the finite-horizon optimum).** For a finite prefix,

    max { sum_{t<N} a_t : conservative charge <= B }  =  B^2 / ( min_{t<N} q_t )^2 ,

attained by putting the entire budget on a single least-friction date.

*Proof.* The feasible set `{x >= 0 : <q, x> <= B}` is a simplex with vertices `0`
and `(B/q_t) e_t`; `sum x_t^2` is convex, so its maximum over a polytope is at a
vertex, and the largest vertex value is `B^2/(min q)^2`. `square`

P2 implies P1 and quantifies it: cumulative authority through `N` is bounded by
`B^2` over the square of the smallest friction seen so far, so it diverges exactly
when the running minimum tends to zero. Both are exact in
`tests/test_persistence.py::TheExactOptimum` and `::PersistenceIffTheFriction\
DipsToZero`, including a brute-force check over a rational grid that no split beats
the vertex.

## 3. What the answer is not

The dispatch asked whether the condition is `q in l^2`. It is not, and no `l^p`
condition is equivalent to it.

- `q in l^2` implies `q_t -> 0` implies `liminf q_t = 0`, so `l^2` is
  **sufficient** and far from necessary.
- `q_t = 1/sqrt(t)` is not in `l^2` and satisfies P1, so failing `l^2` blocks
  nothing.
- The only failure is `q` bounded away from zero. `q_t -> 0` arbitrarily slowly
  still works, and so does a `q` that is `1` everywhere except on a sparse set
  where it dips.

**Block constructions do beat naive ones, and P2 says by how much.** Spreading the
budget over `n` dates of equal friction `q` gives `n (B/(nq))^2 = B^2/(n q^2)`;
concentrating gives `B^2/q^2`. Concentration wins by the factor `n`, which is the
same convexity that makes P2's optimum a vertex.

**The dual reading.** `sup { ||x||_2 : x >= 0, <q,x> <= B } = B / inf_t q_t`. The
characterization is that this dual norm is infinite, and the "certificate" of
failure is a uniform positive lower bound on the friction — a single number.

## 4. Interpretation

`q_t` is small when the norm's exclusion of the still-live worlds is shallow, or
when the market's slack and the ordinary traders' volume are small. So:

> A normative constraint admits unbounded total authority on a finite lifetime
> liability budget **iff there are infinitely many dates on which enforcing it is
> nearly free** — iff its friction with the settled possibilities dips arbitrarily
> close to zero infinitely often.

Not "decays". Dips. The optimal schedule waits for those dates and spends a
geometric tranche of the budget on each, and does nothing in between.

Three consequences worth separating.

**Persistence is budget-free.** P1 does not mention `B`. Any positive lifetime
budget buys persistence when the friction dips, and no budget buys it when the
friction is floored. Only the *rate* of divergence scales with `B`, quadratically.

**Persistence does not compete across reasons.** Splitting `B` geometrically among
countably many reasons leaves each one's criterion untouched, so every individually
persistable reason can be served simultaneously with all the others. There is no
Hall-type condition and no capacity region to check.
`tests/test_persistence.py::ManyReasonsDoNotCompeteForPersistence`.

**The burden moves to transport.** A schedule that enforces only on sparse
low-friction dates satisfies affordability and leaves large gaps, so the
claim-weighted conclusion now rests entirely on the transport stability constants
`(L_r, eps_r)` across those gaps. Affordability and service fidelity pull in
opposite directions here, and the sparse optimum is exactly where they conflict.

## 5. Does the conservative qualification matter? — yes

The sharp worst-case per-date charge, minimizing the increment `a d (d - s)` over
the violations the modulus permits, is

    L(a)  =  a s^2 / 4                     for  a <= 4 m / s^2
             sqrt(a m) s - m               for  a >  4 m / s^2 ,

continuous at the join, where it equals `m`. It is smaller than the conservative
`sqrt(a m) s` everywhere, and *linear* rather than square-root for small `a`.

**It does not, and the earlier claim that it does is withdrawn.** What the
argument establishes is only the case `s_t >= s_0 > 0` and `m_t <= m_bar`: there,
on the small-`a` dates `sum a_t s_0^2/4 <= B` bounds `sum a_t`, and on the large-`a`
dates the square-root term bounds `sum sqrt(a_t)`, so `sum a_t < infinity`. The
conclusion that the *criterion* is unchanged is false.

The counterexample is `s_t = 1/t` with `m_t = t^4`. Then `q_t = s_t sqrt(m_t) = t`,
so `liminf q_t = infinity` and P1 says the reason is not conservatively affordable
at any budget; but `L_t(1) = s_t^2/4 = 1/(4t^2)` is summable, so the *constant*
allocation `a_t = 1` is sharply affordable forever, with total charge under `1/2`.
`tests/test_sharp_cost.py::TheReviewCounterexample`.

`SHARP_PERSISTENCE.md` gives the correct theorem for a general star-shaped date
cost: persistence is achievable iff `liminf_t L_t(1) = 0`. It specializes to
`liminf q_t = 0` for the conservative charge — so P1 and P2 stand exactly as stated
— and, for the sharp one, to `liminf_t min(s_t^2, s_t sqrt(m_t)) = 0`, which
reduces to `liminf s_t = 0` exactly under a floor on the engine scale `m_t`. The two
criteria agree when `m_t` is bounded above and below, which is the case this section
had in mind and did not state.

The sharp charge is still a worst case over the market's response, and
`SIGNED_VS_CONSERVATIVE.md` shows the realized account can be far better than
either.

## 6. What this does not establish

That `q_t` dips for a norm a practice actually produces — that is the non-vacuity
question, and the round's statics generate forever-unvindicated trajectories with
decaying depth for affine demands only. That the sparse optimum is normatively
acceptable; P1 is about affordability alone. That the characterization survives
when the friction is not observable in advance — `ONLINE_EXISTENCE.md`. That
anything here bears on the signed account, which is a different and larger class.

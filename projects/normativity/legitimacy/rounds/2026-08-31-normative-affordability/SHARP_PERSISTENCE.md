# Persistence under a general date cost

## 1. The primitive

A date's **cost function** `L_t : [0, infinity) -> [0, infinity)` charges the
liability account for allocating authority `a` on date `t`. The two instances in
this round are

    conservative   L_t(a) = q_t sqrt(a) ,        q_t = D_t sqrt(m_t)
    sharp robust   L_t(a) = a s_t^2 / 4          for a <= 4 m_t / s_t^2
                            s_t sqrt(a m_t) - m_t  beyond

with `m_t = eps_t + M_t` and `s_t = D_t` the worst live exclusion depth. Both are
increasing, vanish at zero, and are **star-shaped**: `L_t(a)/a` is nonincreasing,
so

    L_t(a) >= a L_t(1)   for a <= 1 ,      L_t(a) <= a L_t(1)   for a >= 1 .

Star-shapedness is implied by concavity with `L(0) = 0` and is the only structural
property either theorem below uses — S1 and S2 both, the second because
star-shapedness of `L` is star-shapedness of its inverse in the reverse sense. The
sharp charge is concave, hence star-shaped: it is linear with slope `s^2/4` up to
the branch point and has derivative `s sqrt(m)/(2 sqrt(a))` beyond, which equals
`s^2/4` at the join and decreases after it.

## 2. The theorem

**Theorem S1 (persistence).** Let each `L_t` be increasing, star-shaped, with
`L_t(0) = 0`, and let `B > 0`. There exists `(a_t)` with `a_t in [0, infinity)`,

    sum_t a_t = infinity      and      sum_t L_t(a_t) <= B

if and only if

    liminf_t L_t(1) = 0 .

*Sufficiency.* Choose `t_1 < t_2 < ...` with `L_{t_k}(1) <= B 2^{-(k+1)}` and put
`a_{t_k} = 1`, zero elsewhere. The charge is at most `B` and the allocated total
diverges. Star-shapedness is not used.

*Necessity.* Suppose `L_t(1) >= c > 0` for all `t >= T`, and let `(a_t)` have
charge at most `B`. Split the dates after `T`. Where `a_t <= 1`, star-shapedness
gives `L_t(a_t) >= a_t L_t(1) >= c a_t`, so those allocations sum to at most `B/c`.
Where `a_t > 1`, monotonicity gives `L_t(a_t) >= L_t(1) >= c`, so there are at
most `B/c` such dates, each carrying a finite allocation. The total is finite.
`square`

**The reference level is immaterial.** Star-shapedness gives
`L_t(1) <= L_t(lambda) <= lambda L_t(1)` for `lambda >= 1` and the reverse pair for
`lambda <= 1`, so `liminf_t L_t(lambda) = 0` for one positive `lambda` iff for all.

**The budget is immaterial.** `B` does not appear in the criterion. Any positive
lifetime budget buys persistence when the criterion holds, and none buys it when it
fails; only the *rate* of divergence scales with `B`.

## 3. What it says about the two charges

**Conservative.** `L_t(1) = q_t`, so S1 reproduces the earlier criterion
`liminf_t q_t = 0` exactly. That result is unchanged and correctly scoped.

**Sharp robust.** `L_t(1) = s_t^2/4` whenever `s_t^2 <= 4 m_t`, and
`s_t sqrt(m_t) - m_t` otherwise. The two branches have a single envelope:

**Lemma S3.** `(1/4) min(s^2, s sqrt(m))  <=  L(1)  <=  min(s^2, s sqrt(m))`.

*Proof.* If `s^2 <= m` then `min = s^2` and `L(1) = s^2/4`, giving the ratio `1/4`.
If `m < s^2 <= 4m` then `min = s sqrt(m)` and `L(1) = s^2/4`, whose ratio to the
minimum is `s/(4 sqrt(m)) in (1/4, 1/2]`. If `s^2 > 4m` then `min = s sqrt(m)` and
`L(1) = s sqrt(m) - m`, whose ratio is `1 - sqrt(m)/s in (1/2, 1)`. `square`

So

    sharp-robust persistence  <==>  liminf_t min(s_t^2, s_t sqrt(m_t)) = 0 ,

and there are **two independent routes to a cheap date**: a shallow exclusion, and
an engine that is easy to move. A norm with a fixed exclusion depth `s_t = 1` against
a vanishing engine scale `m_t -> 0` is persistently enforceable with no depth decay
at all — `L_t(1) = sqrt(m_t) - m_t -> 0` — and
`tests/test_sharp_cost.py::TheReferenceCostIsNotDepthOnly` pins it.

**The criterion reduces to the depth alone exactly under a floor on the engine
scale.** If `m_t >= m_0 > 0` then `min(s^2, s sqrt(m)) >= s min(s, sqrt(m_0))`, which
is bounded away from zero whenever `s_t` is, so

    m_t >= m_0 > 0    ==>    sharp-robust persistence  <==>  liminf_t s_t = 0 .

`m_t = eps_t + M_t` is the market maker's slack plus the ordinary volume bound, so
the floor holds whenever the ordinary traders do not go silent. The unqualified
depth-only statement an earlier version of this section made is withdrawn.

**The two criteria are different, and the round's earlier claim that they agree is
withdrawn.** `PERSISTENT_AFFORDABILITY.md` §5 asserted the characterization was
unchanged under the sharp charge; it proved only the case `s_t` bounded below. The
counterexample is `s_t = 1/t`, `m_t = t^4`: then `q_t = t` diverges, so the
conservative criterion fails outright, while `L_t(1) = 1/(4t^2)` is summable, so a
*constant* allocation `a_t = 1` is sharply affordable forever.
`tests/test_sharp_cost.py::TheReviewCounterexample` pins every quantity, including
that the allocation stays on the linear branch.

So the two criteria coincide when `m_t` is bounded above and below, and otherwise
differ in both directions: the conservative one can fail while the sharp one holds
(`s_t = 1/t`, `m_t = t^4`), and the sharp one can hold with no depth decay at all
(`s_t = 1`, `m_t -> 0`).

## 4. The finite-horizon optimum

**Theorem S2.** Under the same hypotheses as S1 — increasing, star-shaped,
`L_t(0) = 0`, with `L_t^{-1}(B) = sup{a : L_t(a) <= B}` — for any horizon `N`,

    max { sum_{t<N} a_t  :  sum_{t<N} L_t(a_t) <= B }  =  max_{t<N} L_t^{-1}(B) ,

attained by spending the whole budget on one date.

*Proof.* Parametrize by the budget split `b_t` with `sum b_t <= B`; the mass bought
is `sum_t f_t(b_t)` with `f_t = L_t^{-1}`. Star-shapedness of `L_t` is exactly
star-shapedness of `f_t` in the reverse sense — `f_t(b)/b` nondecreasing, since
`f_t(b)/b = a/L_t(a)` at `a = f_t(b)` — so `f_t(b) <= (b/B) f_t(B)` for `b <= B`,
and

    sum_t f_t(b_t)  <=  (1/B) (max_t f_t(B)) sum_t b_t  <=  max_t f_t(B) .

The vertex `b = B e_{t*}` attains it. `square`

The same computation bounds the infinite-horizon supremum by `sup_t L_t^{-1}(B)`,
so the achievable totals are governed by a single date even over an infinite
horizon.

**Instances.** Conservative: `L_t^{-1}(B) = (B/q_t)^2`, so
`A_N^max = B^2 / (min_{t<N} q_t)^2` — the earlier P2, now a corollary. Sharp:
`L_t^{-1}(B) = 4B/s_t^2` while `B <= m_t`, and `(B + m_t)^2/(s_t^2 m_t)` beyond, so
`A_N^max` is `Theta(1 / min_{t<N} s_t^2)` in both branches.

## 5. Two criteria, and they are not the same

S1 characterizes persistence; S2 characterizes the finite-horizon optimum. They are
related but distinct:

    persistence  ==>  sup_t L_t^{-1}(B) = infinity ,

because `liminf L_t(1) = 0` and star-shapedness give `L_t(A) <= A L_t(1) <= B` for
a suitable `t` at every `A`. **The converse fails.** Take `L_t(a) = a` for
`a <= 1` and `1 + (a-1)/t` beyond — star-shaped, with `L_t(1) = 1` at every date,
so no dip and no persistence. Yet `L_t^{-1}(2) = 1 + t` is unbounded: the supremum
of achievable totals is infinite while no single schedule achieves an infinite
total, because reaching a large total needs a large allocation on one date and only
finitely many dates can each carry a charge bounded below.
`tests/test_sharp_cost.py::TheFiniteHorizonOptimum::test_an_unbounded_optimum_does_\
not_imply_persistence`.

For both charges of interest the two criteria coincide — conservative
`L_t(1) = q_t` against `L_t^{-1}(B) = (B/q_t)^2`, sharp `s_t^2/4` against
`4B/s_t^2` — so the distinction bites only for cost families with a kink. It is
worth recording because it is the difference between "arbitrarily much authority is
purchasable" and "unbounded authority is purchasable by one schedule".

## 6. What this does not establish

That `s_t` dips for a norm a practice produces. That the sharp charge is itself
tight — it is the worst case over the market's response, and
`SIGNED_VS_CONSERVATIVE.md` shows the realized account can be far better. That
anything here survives when the friction depends on the policy —
`CLOSED_LOOP_EXISTENCE.md`. That persistence is service-admissible —
`SERVICE_ADMISSIBLE_EXISTENCE.md` shows it usually is not.

# Affordability pays for the settlement-friction residual

## 1. The two quantities are one quantity

The fixed-era bound carries a settlement-friction residual

    F_r(a)  =  limsup_N  inf_{omega in A_N}
               ( sum_{t<N} a^r_t [s^r_t(omega)^+]^2 / A^r_N )^{1/2} ,

and a liability charge which, on the sharp robust cost's linear branch, is

    L_t(a_t)  =  a_t D_t^2 / 4 ,        D_t = sup_{omega in A_t} s^+_t(omega) .

The depth the charge is computed from is the **supremum over live worlds** of the
same deficit whose weighted mean square the residual is built from. So the residual's
numerator is dominated termwise by four times the charge.

**Theorem SS1.** Fix a row `r`. Suppose **(N) nested assessment** — `A_N subseteq
A_t` for every `t <= N` — that every date's allocation is on the linear branch,
`a^r_t <= 4 m_t / (D^r_t)^2`, and that the lifetime charge satisfies
`sum_t L^r_t(a^r_t) <= B_r`. Then for every horizon `N` and **every**
`omega in A_N`,

    sum_{t<N} a_t [s^+_t(omega)]^2   <=   sum_{t<N} a_t D_t^2   =   4 sum_{t<N} L_t(a_t)   <=   4B .

Hence if `A_N -> infinity`,

    sup_{omega in A_N} || s^+(omega) ||_{L^2(nu^a_N)}   <=   2 sqrt( B / A_N )  ->  0 ,

and in particular `F_r(a) = 0`.

*Proof.* `D^r_t` is a supremum over `A_t`, so `s^{+,r}_t(omega) <= D^r_t` requires
`omega in A_t`. Hypothesis (N) supplies exactly that for every `t <= N`. The middle
equality is the linear branch; the last is the budget. Divide by `A^r_N` and take
square roots. `square`

**The two live-world sets are not the same set, and (N) is what relates them.** The
charge at date `t` is computed against `A_t`, the worlds live *then*; the residual at
horizon `N` is evaluated at `A_N`, the worlds live *at the end*. Settlement only
removes continuations and never restores them, so `A_N subseteq A_t` and a world
surviving to `N` was already scored by every earlier date's certificate. Without (N)
the theorem is false as stated: a world admitted after `t` was never bounded by
`D^r_t`, and nothing in the budget covers it. (N) is not an extra assumption on the
world — it is the settlement interface's own monotonicity, discharged in the
deductive case by `A_N = PC(D_N)` with a growing deductive state.

With (N) in place the quantifiers point the right way for the second reason too: the
charge is computed against the *worst* world of `A_t` and the residual is evaluated
at *some* world of `A_N`, so the conservative direction of the liability certificate
is what makes the residual free. The conclusion is stronger than `F_r` needs — it
holds at the supremum over `A_N`, not just the infimum.

**Row indexing.** Every quantity above is indexed by the row: `D^r_t` is the depth of
`r`'s row, `a^r_t` its allocation, `B_r` its budget. Only `m_t` is shared, and it is
shared as a *ceiling* on the whole date, so a multi-row schedule must satisfy the
branch condition against its aggregate allocation — see
`REASONWISE_ACCOUNTING.md` R1 and `MULTIREASON_SERVICEABILITY.md`.

`tests/test_joint_service.py::LiabilityIsTheFrictionNumerator` pins the identity
termwise, the uniform bound, and the vanishing mean square along a schedule whose
allocation reaches `8184` on a budget of `1`.

## 2. What that does to the end-to-end theorem

Feeding `F_r(a) = 0` into `FIXED_ERA_THEOREM.md` F2 and F3:

**Theorem SS2 (sharp affordable service).** Under the hypotheses of SS1, together
with `A^r_N -> infinity`, an adapted transport plan with constants `(L_r, eps_r)`
and vanishing residual density,

    E_{nu^{a,r}_N}[d]   <=   ( 2 sqrt(B) + sqrt(U + B_tot) ) / sqrt(A^r_N) ,

and therefore

    limsup_N  E_{mu^r_N}[d^r]   <=   eps_r .

If the plan has delay at most `H` and the reason's defect has temporal modulus
`omega`, then `eps_r <= omega(H)` and

    limsup_N  E_{mu^r_N}[d^r]   <=   omega(H) .

> Once the learner can persistently afford the reason under the sharp worldwise
> liability certificate on its linear branch, the only remaining asymptotic error is
> how much the reason can change while waiting to be serviced.

This is a material simplification. The round had been carrying two residuals as
independent obstructions; on the linear branch one of them is paid for by the same
budget that makes the service affordable, and the other is the deadline's price.

## 3. The square-root branch, where it fails

Past the branch point the charge saturates: `L_t(a) = D_t sqrt(a m_t) - m_t` grows
like `sqrt(a)` while the friction numerator `a D_t^2` grows like `a`. Inverting,

    a_t D_t^2  =  ( L_t(a_t) + m_t )^2 / m_t ,

an *identity*, not an estimate. So writing `l_t = L_t(a_t)` for the charge actually
spent, the friction numerator on this branch is exactly `sum_{t<N} (l_t + m_t)^2/m_t`
and the residual vanishes precisely when

    ( 1 / A_N )  sum_{t<N}  ( l_t + m_t )^2 / m_t   ->   0 .

That is the exact condition, and it is what an earlier version of this section
compressed to the slogan "only when `m_t` is summable". The slogan is wrong in both
directions. Summability is not necessary: with `l_t = 0` the numerator is `sum m_t`,
which may diverge while `A_N` diverges faster. And it is not sufficient on its own
either, since `m_t -> 0` makes each term `(l_t + m_t)^2/m_t >= l_t^2/m_t` blow up
when the charge does not vanish at least as fast.

Two regimes make it concrete. With `m_t` **bounded below** by `m_* > 0`, each date
contributes at least `m_*`, so the numerator grows at least linearly in the number of
such dates and vanishing needs `A_N` to outgrow it — which the branch condition
`a_t > 4 m_t / D_t^2` forbids from being automatic. With `m_t -> 0` and the charge
spread evenly, the ratio `l_t^2/m_t` diverges term by term.

**The failure is not hypothetical, and it is exactly the second route to cheap
enforcement.** `SHARP_PERSISTENCE.md` §3 records two ways a date can be cheap: a
shallow exclusion (`D_t` small) and an easily moved engine (`m_t` small). SS1 uses
the first. On the second — `D_t = D > 0` fixed with `m_t -> 0` — persistence is
affordable, every date is on the square-root branch, and if every live world is
excluded by at least `sigma > 0` then `F_r >= sigma` however long the service runs.
This **counterregime survives the correction above**: it is the `D_t >= sigma`,
`m_t -> 0` corner, where the exact condition fails for the second of the two reasons
just given.

So:

> **Cheap enforcement is not always conforming enforcement.** A norm that is cheap
> to enforce because it is nearly satisfied by the live worlds drives the displayed
> defect to zero. A norm that is cheap to enforce because nobody is trading against
> it does not.

**Corollary SS3.** On the linear branch, a norm that permanently excludes *every*
live world by at least `sigma > 0` cannot be persistently and affordably enforced:
SS1 gives `sigma^2 A_N <= 4B`, so `A_N <= 4B/sigma^2` is bounded. Persistent
affordable enforcement on that branch therefore *entails* that the norm is
asymptotically compatible with something still live.

## 4. Scope

SS1's hypothesis is `a_t <= 4 m_t / D_t^2` at every date — the allocated authority
does not exceed what the market's own slack and opposing volume can absorb. That is
a checkable predictable condition, not an assumption about the world, and it is the
regime in which the enforcement modulus's linear term is the binding one.

Where the schedule crosses the branch point on finitely many dates the conclusion
survives with the constant enlarged by those dates' contributions; where it crosses
on infinitely many dates with `m_t` bounded below, SS1 does not apply and §3's
failure is available.

## 5. What this does not establish

That the linear branch is where a real schedule sits. That the bound is tight — SS1
bounds the residual at the *supremum* world, and `F_r` takes an infimum, so the true
residual may vanish faster. That the analogous statement holds for the conservative
charge: there `L_t(a) = D_t sqrt(m_t a)` and the same inversion gives
`a D^2 = L^2/m`, so a bounded charge bounds the numerator only under a summability
condition on `L_t^2/m_t`, which is weaker than the linear branch's identity and is
not pursued here.

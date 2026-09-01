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

**Theorem SS1.** Suppose every date's allocation is on the linear branch,
`a_t <= 4 m_t / D_t^2`, and the lifetime charge satisfies `sum_t L_t(a_t) <= B`.
Then for every horizon `N` and **every** live world `omega`,

    sum_{t<N} a_t [s^+_t(omega)]^2   <=   sum_{t<N} a_t D_t^2   =   4 sum_{t<N} L_t(a_t)   <=   4B .

Hence if `A_N -> infinity`,

    sup_{omega in A_N} || s^+(omega) ||_{L^2(nu^a_N)}   <=   2 sqrt( B / A_N )  ->  0 ,

and in particular `F_r(a) = 0`.

*Proof.* `s^+_t(omega) <= D_t` at every live `omega` by definition of the supremum;
the middle equality is the linear branch; the last is the budget. Divide by `A_N`
and take square roots. `square`

The quantifiers point the right way and it is worth saying why. The charge is
computed against the *worst* live world, and the residual is evaluated at *some*
live world; a bound at the worst dominates a bound at any, so the conservative
direction of the liability certificate is exactly what makes the residual free. The
conclusion is stronger than `F_r` needs — it holds at the supremum, not just the
infimum.

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

so a bounded charge bounds the numerator only when `m_t` is summable. With `m_t`
bounded below, each date on this branch contributes at least `4 m_t` to the
numerator, and the sum diverges.

**The failure is not hypothetical, and it is exactly the second route to cheap
enforcement.** `SHARP_PERSISTENCE.md` §3 records two ways a date can be cheap: a
shallow exclusion (`D_t` small) and an easily moved engine (`m_t` small). SS1 uses
the first. On the second — `D_t = D > 0` fixed with `m_t -> 0` — persistence is
affordable, every date is on the square-root branch, and if every live world is
excluded by at least `sigma > 0` then `F_r >= sigma` however long the service runs.

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

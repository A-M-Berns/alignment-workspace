# Sharp Timely Service

The canonical positive result of this round. Everything it consumes is proved
elsewhere here; this document assembles it with exact hypotheses and constants.

## 1. Notation, and one collision resolved

The round has used `D` for two things. Here:

    D_t^r     the worst live exclusion depth of r's row at date t, sup over A_t
    Dbar_r    the bound on the defect, 0 <= d^r <= Dbar_r

`m_t = eps_t + M_t` is the date's market-maker slack plus ordinary volume bound,
`a^r_t` the allocated authority, `A^r_N = sum_{t<N} a^r_t`, `c^r_t` the claim
stream with `C^r_N` its partial sums, and `nu^{a,r}_N` the allocated-service
measure.

## 2. Hypotheses

**(S) Service.** An adapted transport plan `T^r` from claims to allocated
authority, with `A^r_N -> infinity`, service parsimony `W^r_N <= K_r C^r_N`, and
residual density `R^r_N / C^r_N -> 0`.

**(L) Sharp-linear affordability.** Every date's allocation stays on the sharp
charge's linear branch, `a^r_t <= 4 m_t / (D^r_t)^2`, and

    sum_t  (1/4) a^r_t (D^r_t)^2   <=   B_r .

Finitely many exceptional dates are permitted, their contribution absorbed into
`B_r`.

**(M) MarketMaker ceiling.** The reason's enforcement book obeys
`V^r_N(omega) <= U_r` at every live `omega`, with `U_r = U + B_tot` from the
aggregate cumulative cap and the complementary rows' liability floors
(`REASONWISE_ACCOUNTING.md` R1).

**(N) Nested assessment.** `A_N subseteq A_t` for `t <= N` — settlement removes
continuations and never restores them. This is the settlement interface's own
monotonicity and is what lets a world live at `N` be scored against `D^r_t`.

**(T) Temporal stability.** `d^r_t <= L_r d^r_s + eps_r(t,s)` whenever
`T^r(t,s) > 0`.

## 3. The theorem

**Theorem STS (finite horizon).** Under (S), (L), (M), (N) and (T), for every `N`,

    E_{mu^r_N}[d^r]
        <=  L_r K_r ( 2 sqrt(B_r) + sqrt(U_r) ) / sqrt(A^r_N)
            +  epsbar^r_N(T)
            +  Dbar_r · R^r_N / C^r_N ,

where

    epsbar^r_N(T)  =  (1 / C^r_N)  sum_{t,s}  T^r_N(t,s) eps_r(t,s)

is the **claim-normalized** transport error.

*Proof.* By (N), a world live at `N` is live at every `t < N`, so
`s^{+,r}_t(omega) <= D^r_t` there; hence by (L)

    sum_{t<N} a^r_t [s^{+,r}_t(omega)]^2  <=  sum_{t<N} a^r_t (D^r_t)^2
                                          =  4 sum_{t<N} L_t(a^r_t)  <=  4 B_r

for **every** `omega in A_N`, which is `SHARP_SERVICEABILITY.md` SS1. So
`|| s^+(omega) ||_{L^2(nu^{a,r}_N)} <= 2 sqrt(B_r / A^r_N)`. Feeding that into
`FIXED_ERA_THEOREM.md` F2 —
`E_{nu}[d] <= || s^+(omega) ||_{L^2(nu)} + sqrt(U_r / A^r_N)` — gives

    E_{nu^{a,r}_N}[d^r]  <=  ( 2 sqrt(B_r) + sqrt(U_r) ) / sqrt(A^r_N) .

The claim-weighted step is `SERVICE_TRANSFER.md` T3 in its edge-dependent
normalized form. `square`

**Corollary STS-1 (asymptotic).**

    limsup_N  E_{mu^r_N}[d^r]   <=   limsup_N  epsbar^r_N(T) .

**Corollary STS-2 (uniform delay).** If the plan has delay at most `H` and the
reason has temporal modulus `omega_r`, then `epsbar^r_N(T) <= omega_r(H)` and

    limsup_N  E_{mu^r_N}[d^r]   <=   omega_r(H) .

**Corollary STS-3 (exact preservation).** If `eps_r(t,s) = 0` on the plan's
support then `E_{mu^r_N}[d^r] -> 0`.

The constants are checked in `tests/test_timely.py::TheCanonicalBound`, including
the composed right-hand side and the asymptotic collapse to the transport term.

## 4. What has been compressed, and what has not

The generic fixed-era theorem carries **two** residual mechanisms: settlement
friction `F_r(a)` and transport distortion. Under (L), the first vanishes — the
same liability budget that keeps the learner unexploitable also drives the
service-weighted misfit to zero, because the charge is computed from the supremum
of the very deficit the residual averages.

    generic affordability          ==>  Progress up to  F_r(a) + epsbar
    sharp-linear affordability     ==>  F_r(a) = 0
    Sharp Timely Service           ==>  Progress up to  epsbar alone

**`F_r` stays in the generic schematic theorem**, and the square-root branch is
why: with the exclusion depth floored and the engine scale vanishing, service is
cheaply persistent and the residual stays positive
(`SHARP_SERVICEABILITY.md` §3). Hypothesis (L) is exactly the boundary.

## 5. The one-sentence form

> If Answerability's claims can be transported onto sufficiently timely,
> sharp-linearly affordable enforcement dates, then the same liability budget that
> preserves the learner also drives settlement friction away, leaving only the
> semantic change incurred while the reason waited to be answered.

Every clause of that sentence is a hypothesis or a conclusion above: *transported*
is (S) and the plan, *timely* is the delay bounding `epsbar`, *sharp-linearly
affordable* is (L), *preserves the learner* is the preservation theorem consuming
the same `B_r`, *settlement friction away* is SS1, and *semantic change while
waiting* is `epsbar^r_N(T)`.

## 6. What this does not establish

Existence of a plan satisfying (S) and (L) simultaneously — that is
`BOUNDED_DELAY_AFFORDABILITY.md` and `AFFORDABLE_SCHEDULING.md`, and it is where
the round's remaining open questions live. Certification of (T)'s constants, which
has no mechanism. That (L) holds in the closed loop, where `m_t` and `D^r_t`
respond to the policy. That `U_r` is the right constant outside the current LI
composition.

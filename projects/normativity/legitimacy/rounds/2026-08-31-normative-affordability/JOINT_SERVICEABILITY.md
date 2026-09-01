# The joint objective: liability, friction, timeliness

## 1. Three quantities, and the residual they produce

A service schedule `(a, T)` controls three things at once:

    liability            sum_s L_s(a_s)
    settlement friction  F_r(a), built from sum_s a_s r_s with r_s = D_s^2
    transport error      eps(T) = sum_{t,s} T(t,s) eps(t,s)

and the fixed-era bound is

    limsup_N E_{mu^r_N}[d^r]   <=   L_r K_r F_r(a)  +  eps(T) .

The earlier frontier treated `F_r` as a property of the norm. It is not: it is the
misfit landscape `s^r_t(omega)` — which the norm and settlement supply — **evaluated
under the chosen schedule**. A scheduler that services a reason on dates where the
norm is nearly satisfied gets a small residual; one that services it on dates of
deep exclusion does not.

    settlement-misfit landscape   =  environment and norm input
    settlement-friction residual  =  that landscape read against the service measure

## 2. The optimization

For one reason at a finite horizon:

    choose  a >= 0 and a legal transport plan T
    subject to  sum_s L_s(a_s) <= B ,   sum_t T(t,s) <= a_s ,
                T(t,s) > 0 => t <= s <= t + H
    minimising  Residual(a, T)  =  L_r K_r F_r(a)  +  eps(T) .

Write `BestResidual(B) = inf over affordable admissible plans of Residual`.

Two facts make this tractable in the regime that matters.

**On the sharp linear branch the first two objectives are proportional.** By
`SHARP_SERVICEABILITY.md` SS1, `sum_s a_s r_s = 4 sum_s L_s(a_s)`, so the friction
numerator is not an independent objective at all: it is four times the liability
already being budgeted. Any affordable persistent schedule has `F_r(a) = 0`, and

    BestResidual(B)  =  inf { eps(T) : (a,T) affordable, A_N -> infinity } .

**So the joint problem collapses to a pure timeliness problem** in that regime. The
three-way trade the round expected is a two-way trade between spending and waiting.

## 3. The linear-regime assignment problem

Attach a multiplier `lambda` to the budget and `mu` to the friction numerator. The
objective becomes separable over claims, because with linear date costs every unit
of claim mass is priced independently:

    score(t, s)  =  lambda w_s  +  mu r_s  +  eps(t, s) ,

and each claim at `t` sends its whole mass to the legal date minimising the score.
That is an interval assignment problem: every claim chooses among the dates in
`[t, t+H]` according to a combined **underwriting + semantic-friction + delay**
price.

**Proposition JS1 (two prices, not three).** On the sharp linear branch
`r_s = 4 w_s`, so

    score(t, s)  =  (lambda + 4 mu) w_s  +  eps(t, s) ,

and the friction price is not a separate dial. Checked exactly over a grid of
multipliers and claim-date pairs in
`tests/test_joint_service.py::TheCombinedScoreHasTwoPrices`.

So the "reason service market" has exactly two prices: what underwriting costs, and
what waiting costs. The cheapest-liability date is not in general the best date —
the same fixture shows the optimum moving from the farthest, cheapest date to the
nearest one as the delay price rises.

**Proposition JS2 (the Pareto frontier).** Varying the single combined price traces
the finite-horizon Pareto frontier between total liability and total transport
error, and each point of it is computed by one pass of per-claim minimisation over
the window. No dynamic programming is needed on the linear branch, because D4's
per-claim separation survives the extra objective.

## 4. Where the collapse does not happen

Two regimes keep three genuine objectives.

**Past the branch point**, `r_s` and `w_s` are no longer proportional — the charge
saturates while the friction numerator does not — so the friction price is a real
third dial and `SHARP_SERVICEABILITY.md` §3's failure applies.

**When the reason's misfit landscape is not the same as the charge's depth.** SS1
uses that the charge is computed from `D_t = sup_omega s^+_t(omega)`, the same
deficit the residual is built from. A realization whose liability is charged on a
different quantity — a support-capacity route rather than the deficit route, for
instance — breaks the proportionality and restores the third objective.

## 5. Multi-reason, corrected

`MULTIREASON_SERVICEABILITY.md` M1's additivity needs a hypothesis the document
stated loosely. Three levels, and only the first is additive:

1. **separate rows and separate accounts:** the costs add exactly, and the joint
   condition is `sum_r Cost^r <= B`;
2. **separate rows, one worldwise robust account:** the joint charge is
   `sup_omega sum_r l_r(omega) <= sum_r sup_omega l_r(omega)`, so the true cost is
   **subadditive** and the additive test is conservative — an economy of scope
   supplied by the world quantifier, not by any sharing of rows;
3. **shared rows:** one enforcement position answers several reasons, so the cost is
   subadditive again and by a different mechanism.

In all three the failure direction is the same: the additive test is *sufficient*
for joint serviceability and is not an impossibility certificate. That is patched
into M1.

## 6. What this does not establish

That `BestResidual(B)` is computable outside the linear branch. That the Lagrangian
separation is exact rather than a relaxation for a hard budget — it traces the
Pareto frontier, and recovering a specific budget requires the usual multiplier
search, which for a linear objective and a linear budget is exact but for the
concave-branch cost is not. That the misfit landscape is available to a scheduler at
the time it must choose; the round's position is that the deductive channel probably
supplies it and the empirical one does not.

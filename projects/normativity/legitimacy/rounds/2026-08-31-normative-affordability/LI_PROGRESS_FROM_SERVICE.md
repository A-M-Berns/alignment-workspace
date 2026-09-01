# Progress from allocated service

## 1. Standing objects

Rows `j` active at date `t`, with allocated authority `a_{t,j} > 0`, violation
`d_{t,j} = g_{t,j}(P_t)`, and signed misfit `s_{t,j}(omega) = r_j - <c_j, omega>`
at an assessment world. Write `s^+ = max(0, s)`, the exclusion deficit. Put

    A_N = sum_{t<N, j} a_{t,j} ,   nu^a_N = a / A_N ,   Q_N = sum a d^2 = A_N E_{nu^a}[d^2] .

Three inherited facts, none of them new here.

**(M) Modulus.** `sum_j a_{t,j} d_{t,j}^2 <= eps_t + M_t` at every date, from the
market maker's contract, a cube point of `K_t`, and `||tau_t||_1 <= M_t`.
Kernel-checked as `weighted_square_le_slack_add_volume`.

**(C) Cumulative cap.** `V_N(omega) <= U` for every `omega` live at `N`, where
`V_N(omega) = sum_{t,j} a_{t,j} d_{t,j} (d_{t,j} - s_{t,j}(omega))` is the
enforcement position's cumulative assessed value, and `U = C + B_F` is the maker's
cap plus the ordinary trading firm's floor.

**(S) SafeCert.** `V_N(omega) >= -B` for every date and every live `omega`.

## 2. Three work bounds

**Theorem P1 (unconditional).** `Q_N <= S_N := sum_{t<N} (eps_t + M_t)`.

*Proof.* Sum (M). `square`

**Theorem P2 (compatible world).** If some `omega_0` live at `N` satisfies every
row enforced before `N` — `s_{t,j}(omega_0) <= 0` throughout — then `Q_N <= U`.

*Proof.* `V_N(omega_0) = Q_N - sum a d s(omega_0) >= Q_N`, and (C) bounds the left
side by `U`. `square`

**Theorem P3 (friction).** For every `omega` live at `N`, with
`R_N(omega) = sum_{t,j} a_{t,j} s^+_{t,j}(omega)^2`,

    sqrt(Q_N)  <=  sqrt(R_N(omega))  +  sqrt(U) .

*Proof.* By (C), `Q_N <= U + sum a d s(omega) <= U + sum a d s^+(omega)`, and
Cauchy–Schwarz on the weights `a` gives `sum a d s^+ <= sqrt(Q_N) sqrt(R_N)`. Put
`q = sqrt(Q_N)`, `R = R_N`. Then `q^2 <= U + q sqrt(R)`. If `q <= sqrt(R)` the
claim holds; otherwise `(q - sqrt(R))^2 <= q(q - sqrt(R)) <= U`. `square`

Dividing by `sqrt(A_N)` turns P3 into a triangle inequality between two `L^2`
norms against the same measure:

    || d ||_{L^2(nu^a_N)}  <=  || s^+(omega) ||_{L^2(nu^a_N)}  +  sqrt( U / A_N ) .

## 3. The Progress theorem

**Theorem P4 (service-weighted Progress).** For every `omega` live at `N`,

    E_{nu^a_N}[d]  <=  || s^+(omega) ||_{L^2(nu^a_N)}  +  sqrt( U / A_N ) ,

and unconditionally `E_{nu^a_N}[d] <= sqrt(S_N / A_N)`. Hence if
`A_N -> infinity` and `inf_{omega live at N} || s^+(omega) ||_{L^2(nu^a_N)} -> 0`,
then `E_{nu^a_N}[d] -> 0`.

*Proof.* `E[d] <= sqrt(E[d^2])` by Cauchy–Schwarz, then P3 or P1. `square`

Four readings.

**One compatible live world still suffices, and gives the fast rate.** Under P2
the residual is zero and `E_{nu^a_N}[d] <= sqrt(U / A_N)`: a constant over the
square root of allocated service, with no hypothesis about the other live worlds.
Progress reads the account at the best world; liability reads it at the worst.

**The exact friction condition** is that the `a`-weighted mean-square exclusion
deficit vanishes at some persistently live world. Not that the norm is true, not
that every world satisfies it — that one world does, in the weighted `L^2` sense.

**Nothing is lost by the quadratic form.** Violations are bounded by the row's
largest attainable violation `D`, and `E[d]^2 <= E[d^2] <= D E[d]`, so the linear
and quadratic statements vanish together. Only the rate differs: the modulus is a
statement about `d^2`, so the honest rate is `A_N^{-1/2}` and a linear-in-`d`
premise would have been an extra assumption, not a sharper conclusion.
`tests/test_service.py::ModulusGivesQuadraticProgress` pins both directions.

**The Brier reading sharpens the interpretation.** For a row with unit normal,
`a d^2 = a · dist(P_t, K_t)^2`, and `dist(x, K)^2 = min_{q in K} Br_x(q)`. So `Q_N`
is the `a`-weighted cumulative Brier excess of the displayed prices over the norm,
and P2 says that excess is bounded by a constant. `E_{nu^a}[d^2] -> 0` is a
weighted-regret statement, which is why the `L^2` triangle inequality of §2 is the
natural form.

**The core minimum caps what force can buy.** A certified core minimum `theta`
gives `s^+ <= (1 - theta) diam` uniformly, hence
`|| s^+ ||_{L^2(nu^a)} <= (1 - theta) diam` and

    limsup_N E_{nu^a_N}[d]  <=  (1 - theta) · diam ,

with no hypothesis about which worlds are live. Depth of the reference bounds the
residual, and tightening the endorsed region does not raise it — the same
precision-independence the round recorded, now as a Progress floor rather than a
liability ceiling.

## 4. Liability is sublinear in allocated authority

**Proposition P5.** At any date and world, the misfit charge obeys

    a_{t,j} d_{t,j} s^+_{t,j}(omega)  <=  sqrt( a_{t,j} (eps_t + M_t) ) · s^+_{t,j}(omega) ,

by (M). So doubling the authority allocated to a row multiplies its worst-case
charge by at most `sqrt(2)`, not by `2`.

This is the mechanism behind the behaviour the theory wants. Allocated service may
diverge on a finite lifetime liability budget, because the market's own response
reduces the realized force as compliance improves: the violation the position
trades on is bounded by `sqrt((eps + M)/a)`, so buying more authority buys
precision at a square-root price in exposure.

**Corollary P6.** With `eps_t + M_t <= c` and `s^+_t(omega) <= sigma_t`, the
schedule `a_t = t^p`, `sigma_t = t^{-q}` is persistent and affordable whenever
`p >= -1` and `q > p/2 + 1`: `A_N -> infinity` while the cumulative charge
`sum_t sqrt(c) t^{p/2 - q}` converges.

Exact instances in `tests/test_service.py::CapacityInAuthoritySpace`: a per-date
allowance `1/(t+1)^2`, summable to under `2`, buys authority
`cap_t = 16^t/(t+1)^4` under a depth halving twice per date, and a trajectory at
the cap has allocation over `10^6` by date twelve with cumulative charge under `2`.

## 5. Coercivity: the schematic Actionability layer

Projection force does not deliver `g >= gamma d`. It delivers work `a d^2`. Rather
than force every realization into a linear form, take the modulus as a parameter.

**Theorem P7 (coercive Actionability).** Suppose the engine guarantees
`Work_N := sum_{t} a_t phi(d_t) <= C_N` with `phi : [0, D] -> [0, infinity)`
convex, `phi(0) = 0` and `phi` strictly increasing. If `A_N -> infinity` and
`C_N / A_N -> 0`, then

    E_{nu^a_N}[d]  <=  phi^{-1}( C_N / A_N )  ->  0 .

*Proof.* Jensen: `phi(E_{nu}[d]) <= E_{nu}[phi(d)] = Work_N / A_N <= C_N/A_N`, and
`phi` is invertible on its range. `square`

Without convexity a power lower bound suffices: if `phi(d) >= c d^p` with `p >= 1`
then `E_{nu}[d] <= (C_N / (c A_N))^{1/p}`.

This **simplifies** the stack rather than generalizing it. The old linear form is
`phi(d) = gamma d`, giving `E[d] <= C_N/(gamma A_N)`; projection enforcement is
`phi(d) = d^2`, giving `E[d] <= sqrt(C_N/A_N)`. One theorem, two realizations, and
the residual and the rate both read off `phi`. The minimal conditions are exactly
the ones Jensen and inversion need: `phi` convex with `phi(0) = 0` and strictly
increasing on the defect's range.

## 6. Comparison with the round's `w = beta d` formulation

| | `w = a d` (round) | `a = beta` (here) |
|---|---|---|
| predictable | no | yes |
| defined under perfect compliance | no — division by zero | yes |
| persistent relevance schedulable | no | yes |
| what the engine bounds | nothing directly | `sum a d^2`, per date, kernel-checked |
| force bound used | linear, assumed | quadratic, proved |
| Progress rate | none stated | `A_N^{-1/2}`, or the friction residual |
| friction residual | `E_nu[s]` | `|| s^+ ||_{L^2(nu^a)}` |
| liability in the service variable | linear | square-root |

Nothing in the round's account algebra is withdrawn: the identity
`V_N(omega) = sum a d (d - s(omega))` is the same object, and the earlier
sandwich between defect and misfit is that identity read in the wrong variable.
What changes is which measure Progress is stated against, and with it whether
Answerability can ask for the thing the theorem consumes.

## 7. What this does not establish

That a schedule with `A^r_N -> infinity` inside the capacity box exists for every
persistent reason simultaneously — that is affordability existence, now posed in
`a`-space. That the friction residual ever vanishes for a norm a practice
actually produces; the round's statics can generate forever-unvindicated
trajectories with summable charge, but that is a displayed family rather than a
theorem about sources. That `U` is the right constant outside the current LI
composition. None of §2–§5 is in Lean; (M) and the liability identity are, and the
inequalities built on them here are not.

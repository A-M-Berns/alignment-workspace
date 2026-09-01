# The fixed-era normative learner theorem

One era: one settled semantics, one evaluator, no ontology revision. Everything
below is a composition statement — it consumes an authority schedule and produces
Progress plus preservation, and it does not assert that such a schedule exists.

**Frozen.** No later pass in this round reopened it, and none should without an
actual contradiction: subsequent work is existence and characterization, which
consume this statement rather than amend it. `README.md` records the freeze and
what it covers.

## 1. Coercive Actionability, at its weakest hypothesis

**Theorem F1.** Let `0 <= d_t <= D`, `a_t >= 0`, `A_N = sum_{t<N} a_t > 0`, and
`Work_N = sum_{t<N} a_t phi(d_t)` with `phi : [0, D] -> [0, infinity)`. Write
`phǐ(eps) = inf_{d >= eps} phi(d)`.

1. *(qualitative)* If `Work_N / A_N -> 0` and `phǐ(eps) > 0` for every `eps > 0`,
   then `E_{nu^a_N}[d] -> 0`. Conversely, if `phǐ(eps) = 0` for some `eps > 0`,
   there is a trajectory with `Work_N/A_N -> 0` and `E_{nu^a_N}[d] >= eps`.
2. *(quantitative, no regularity)*
   `E_{nu^a_N}[d] <= inf_{eps > 0} [ eps + D · (Work_N/A_N) / phǐ(eps) ]`.
3. *(quantitative, convex)* If `phi` is convex with `phi(0) = 0` and strictly
   increasing, `E_{nu^a_N}[d] <= phi^{-1}( Work_N / A_N )`.

*Proof.* (1) and (2): `phi >= phǐ(eps) · 1[d >= eps]`, so
`nu^a_N(d >= eps) <= (Work_N/A_N)/phǐ(eps)` and
`E[d] <= eps + D · nu^a_N(d >= eps)`. For the converse put all mass on points
where `phi` is small and `d >= eps`. (3) Jensen and invertibility. `square`

So **convexity and monotonicity are not needed for convergence**; the exact
condition is that `phi` be bounded away from zero away from zero, and it is
necessary as well as sufficient. What convexity buys is the rate: for
`phi(d) = d^2`, (3) gives `sqrt(Work/A)` where (2) gives only `(Work/A)^{1/3}`.
Projection enforcement is `phi(d) = d^2`; the older linear form is
`phi(d) = gamma d`. One theorem, both realizations, and the rate reads off `phi`.

**With friction.** The engine typically bounds `Work_N` only up to a charge:
`Work_N <= Friction_N + O(1)`. Substituting into (3) with `phi(d) = d^2` and
applying Cauchy–Schwarz to the charge is exactly §2 below.

## 2. The finite-horizon inequality

Fix a reason `r` owning rows `J_r`. Write, over `t < N` and `j in J_r`,

    A^r_N = sum a_{t,j} ,  nu^{a,r}_N = a / A^r_N ,
    Q^r_N = sum a_{t,j} d_{t,j}^2 ,  R^r_N(omega) = sum a_{t,j} s^+_{t,j}(omega)^2 .

**Theorem F2 (service-weighted, finite horizon).** Under the hypotheses of §3, for
every `omega` live at `N`,

    E_{nu^{a,r}_N}[d]  <=  || s^+_r(omega) ||_{L^2(nu^{a,r}_N)}
                           +  sqrt( (U + B_tot) / A^r_N ) ,

and unconditionally `E_{nu^{a,r}_N}[d] <= sqrt( S_N / A^r_N )` with
`S_N = sum_{t<N}(eps_t + M_t)`.

*Proof.* `REASONWISE_ACCOUNTING.md` R1 gives `V^r_N(omega) <= U + B_tot`, and
`V^r_N(omega) = Q^r_N - sum a d s(omega) >= Q^r_N - sum a d s^+(omega)`. Cauchy–
Schwarz on the weights gives `sum a d s^+ <= sqrt(Q^r_N R^r_N)`, so
`Q^r_N <= (U + B_tot) + sqrt(Q^r_N R^r_N)`; with `q = sqrt(Q^r_N)` either
`q <= sqrt(R^r_N)` or `(q - sqrt(R^r_N))^2 <= q(q - sqrt(R^r_N)) <= U + B_tot`.
Either way `q <= sqrt(R^r_N) + sqrt(U + B_tot)`. Divide by `sqrt(A^r_N)` and apply
`E[d] <= sqrt(E[d^2])`. The unconditional form replaces R1 by the per-date modulus.
`square`

**Theorem F3 (claim-weighted, finite horizon).** With an adapted transport plan
for `r` satisfying the claim marginal, service feasibility against `a^r`, stability
`(L_r, eps_r)` on its support, the service-to-claim cap `K_r`, and residual density
`rho^r_N`,

    E_{mu^r_N}[d^r]  <=  L_r K_r ( inf_{omega live at N} || s^+_r(omega) ||_{L^2(nu^{a,r}_N)}
                                   + sqrt( (U + B_tot) / A^r_N ) )
                         +  eps_r  +  D rho^r_N .

*Proof.* `SERVICE_TRANSFER.md` T3 against `nu^{a,r}`, then F2. `square`

**Corollary F4 (asymptotic).** If `A^r_N -> infinity` and `rho^r_N -> 0`,

    limsup_N E_{mu^r_N}[d^r]  <=  L_r K_r F_r  +  eps_r ,
    F_r := limsup_N inf_{omega live at N} || s^+_r(omega) ||_{L^2(nu^{a,r}_N)} .

**Preservation.** The per-row floors give `V_N(omega) >= -B_tot`, which is the
preservation theorem's hypothesis, so no efficiently computable trader exploits the
modified market and each has assessed net worth at most `1 + B_tot`.

## 3. Hypotheses, by layer

| hypothesis | layer |
|---|---|
| claim stream `c^r_t`, `C^r_N -> infinity` | Answerability / standing |
| predictable `a^r_t >= 0`, and `A^r_N -> infinity` | service scheduling |
| adapted transport plan with claim marginal, feasibility against `a^r`, cap `K_r`, `rho^r_N -> 0` | service scheduling |
| stability `d_t <= L_r d_s + eps_r` on the plan's support | semantic transport |
| the docket's rows are priceable and each region is nonempty in the cube | force / Actionability |
| the compiled law is continuous and legal; the maker's contract holds at slack `eps_t` against ordinary volume `M_t` | learner Uptake |
| per-row floors `V^j_N(omega) >= -B_j` at every live `omega`, `sum_j B_j <= B_tot` | affordability / safety |
| bounded liability implies no efficiently computable trader exploits the modified market | substrate preservation |

Two entries the previous statement carried are gone. The **aggregate SafeCert** is
implied by the per-row floors. **"Common region nonempty"** has moved out of the
affordability definition and into the force interface, where it belongs: it is a
precondition for the enforcement inequality to have a region point to evaluate at,
a property of the docket rather than of the schedule.

## 4. Dependency graph

```text
  priceable rows, nonempty regions
            |                       docket
            v
  predictable a_t  ---->  compiled continuous law kappa_t
            |                       |
            |                       v
            |            MarketMaker fixed point P_t
            |                       |
            |            +----------+-----------+
            |            |                      |
            |            v                      v
            |     per-date modulus        cumulative cap U
            |     sum a d^2 <= eps+M            |
            |            |                      |
            |            +---- F2 ---+          |
            |                        |          |
  per-row floors B_j  --> R1 --------+          |
            |                        v          v
            |             service-weighted Progress    aggregate floor
            |                        |                      |
   transport plan ---- F3 -----------+                      v
                                     |            preservation: LI survives
                                     v
                     claim-weighted Sustainable Progress
```

## 5. `F_r = 0` versus a persistently compatible world

These are not the same condition and the round should not say they are.

**Sufficient.** If some `omega_*` is live at every horizon and satisfies every
serviced row, then `s^+_r(omega_*) = 0` throughout and `F_r = 0`. This also gives
the fast rate: `E_{nu^{a,r}_N}[d] <= sqrt((U + B_tot)/A^r_N)`.

**Not necessary.** `F_r = 0` is a weighted-average asymptotic condition and can
hold with no compatible world at all. Take two live worlds and rows that alternate
which one they exclude, with the exclusion depth decaying: each world's weighted
`L^2` misfit tends to zero, so `F_r = 0`, while neither world satisfies all the
rows and no third world is live.

**Compactness does not close the gap.** With `A_N` nested and compact, a sequence
of near-optimal worlds has a limit point in the intersection, but a small weighted
`L^2` norm does not give a pointwise-small misfit at every date — only on dates
carrying non-negligible allocation. The limit world may violate rows of small
weight.

**A necessary condition, separately.** From the account floor,
`sup_{omega} E_{nu^{a,r}_N}[s_r(omega)] <= E_{nu^{a,r}_N}[d] + B_tot/A^r_N`, so
service-weighted Progress forces the *signed* mean misfit to vanish at every live
world. That is a different quantity from `F_r`: a mean rather than a root-mean-
square, and signed rather than positive-part. Sufficiency and necessity are stated
separately here because they are genuinely different conditions.

## 6. Is the construction complete?

**Yes, for the fixed era, with one verification debt.**

Conditional on a service-faithful authority schedule, per-row liability floors, and
the two residual assumptions, every arrow from Answerability's claim stream to
claim-weighted Progress and to LI preservation is proved: the docket compiles, the
law is legal and continuous, the fixed point exists, the modulus and the cap are
theorems of the construction, R1 makes the cap reason-indexed, F2 and F3 are the
two inequalities above, and preservation is the source's Theorem 9.

The debt is that preservation is unconditional only in the deductive instance; the
generalized live-world lift carries a transcription obligation recorded in the
enforcement round's proof-closure document. That is verification, not a missing
arrow.

The unresolved hypotheses are **inputs**, not gaps in the composition:

- a schedule with `A^r_N -> infinity` inside the capacity, for every persistent
  reason at once;
- the per-row floors;
- `F_r` and `eps_r`, whose values are properties of the norm and of the reason.

`construction/composition != existence != necessity` — and this document is the
first of the three.

## 7. What this does not establish

Existence of the schedule, which is `AFFORDABLE_SCHEDULING.md`. Necessity of
bounded liability, still `PRIORITIES.md` item 40. Any statement across eras: the
transport residual `eps_r` here is a within-era deferral residual, and cross-era
transport needs a semantic bridge nothing here supplies. That `F_r` is ever zero
for a norm a practice produces.

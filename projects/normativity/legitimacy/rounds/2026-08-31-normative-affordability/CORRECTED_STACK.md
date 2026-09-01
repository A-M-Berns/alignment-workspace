# The corrected stack

Six schematic results and one realization line. Everything the round proved that
is not listed here is either subsumed or was withdrawn by `FOLLOWUP_REPORT.md`.

## Schematic

### S1 — Service Transfer, and its exact characterization

For bounded defect **arrays**, `E_{nu_N}[d] -> 0` together with `mu ◁ nu` gives
`E_{mu_N}[d] -> 0`; and contiguity is necessary, with indicator arrays extremal.
Contiguity equals asymptotic uniform absolute continuity. For `N`-independent
defect sequences the exact condition is fixed-set contiguity, which is strictly
weaker; one-step delay separates them. A pointwise density bound gives the
quantitative form with no asymptotics.

*Use.* A characterization, and the route to take when nothing is known about the
defect. Not an interface.

### S2 — Deferred Service Transfer

A transport plan `T(t,s) >= 0` with claim marginal `(T1)`, service feasibility
`(T2)`, stability `d_t <= L d_s + eps` on the plan's support `(T3)`, a
service-to-claim cap `W_N <= K C_N` and vanishing residual gives

    E_{mu_N}[d]  <=  L K E_{nu_N}[d]  +  eps  +  D R_N / C_N .

*Use.* The Answerability-to-Progress interface. **Incomparable to S1**: it proves a
density bound on the transported claim measure `mu~`, not on `mu`, and neither
route implies the other.

### S3 — Claim-weighted Sustainable Progress, staged

    (P1)  engine-side premises        ==>  E_{nu^r_N}[d^r] -> 0
    (P2)  (P1) + S2                   ==>  limsup_N E_{mu^r_N}[d^r] <= eps_r

with equality to `0` when transport stability is exact. `(P2)` has no engine
parameter and composes with any `(P1)`.

### S3a — Coercive Actionability

If the engine guarantees `sum_t a_t phi(d_t) <= C_N` with `C_N/A_N -> 0`, then
`E_{nu^a_N}[d] -> 0` **exactly when** `phi` is bounded away from zero away from
zero — `inf_{d >= eps} phi(d) > 0` for every `eps > 0`. Convexity is not needed for
convergence; it buys the rate, `E[d] <= phi^{-1}(C_N/A_N)` by Jensen against
`(C_N/A_N)^{1/3}` without it. The linear form `phi(d) = gamma d` and projection
enforcement's `phi(d) = d^2` are the two instances. `FIXED_ERA_THEOREM.md` F1.

### S3b — Subset ceiling

An aggregate cap plus per-row liability floors summing to `B_tot` gives every
subset of rows the *uniform* ceiling `U + B_tot`. Aggregate safety alone does not:
two books with increments `+1` and `-1` have an identically zero aggregate and no
reason-level ceiling at all. `REASONWISE_ACCOUNTING.md`.

### S4 — Joint Actionability

Individual Actionability, additive aggregation, nonnegative weights and a nonempty
common region `intersect_r K^r != empty` give
`inf_{v ∈ intersect_r K^r} <sum_r w^r zeta^r, v - p> >= sum_r w^r gamma_r d^r`.

*Use.* Engines whose control is open-loop or whose gain certificate is
reason-relative. **Not required when the control is recomputed at the realized
state**, which is the reactive case and includes the traderized compiler.

### S5 — SafeCert

A safety certificate is a functional `rho_h` of the control history, evaluable at
the history at which the control is chosen, whose safe class is prefix-closed and
which satisfies a consistency property strong enough that a certificate issued at
`h` is not revoked at any `h' ⊒ h`. The interface obligation is

    SafeCert_D(kappa)  ==>  PreservedUptake(D^kappa) .

Predictability of the controller forces the *evaluability*; it does not force
worst-case robustness. **T5** — non-revocation — holds when `rho_h` is a supremum
over a family that shrinks under settlement, and is a different statement for a
measure-carrying engine.

### S6 — Affordability

An **affordability witness** at `h` is a predictable `(a_t, kappa_t)` — allocated
authority per reason, and the control law compiled from it — such that an adapted
transport plan with declared constants matches each persistent reason's claim
stream to `a^r`, and the realized history `u_t = kappa_t(x_t)` lies in the safe
class. **Affordability** is the existence of such a witness. Nonemptiness of the
common region is a force-interface precondition, not part of this definition.

*Existence.* T7 stands as a **strong sufficient** theorem: convex per-round
response sets, a convex liability functional, bounded arrival rates and a
pointwise self-financing control outpacing arrivals make max-weight scheduling a
witness with budget `0`. It carries no necessity claim; the necessary condition is
the account condition itself, and the useful sufficient certificates are the
existing liability-regime taxonomy.

*Overload.* A Farkas pair with positive deficit on any settlement-consistent path
refutes affordability. Sound, not complete.

## The composition target, with every premise attributed

> **Sustainable Progress.** Let `r` be a reason persistent on a tail, with bounded
> defect `0 <= d^r <= D`. Assume
>
> | premise | layer |
> |---|---|
> | claim weights `c^r_t` with `C^r_N -> infinity` | Answerability / standing |
> | `W^r_N -> infinity` | service scheduling |
> | an adapted plan `T^r` with `(T1)`, `(T2)`, cap `K_r`, residual density `-> 0` | service scheduling |
> | stability `(T3)` with constants `(L_r, eps_r)` | semantic transport |
> | coercive Actionability `sum_t a_t phi(d_t) <= Work_N` with `phi` bounded away from zero away from zero | force / Actionability |
> | the engine bounds `Work_N` — in LI, the per-date modulus and the cumulative cap | learner Uptake |
> | per-row liability floors summing to `B_tot`, which imply the aggregate floor | affordability / safety |
> | `SafeCert(kappa) ==> PreservedUptake(D^kappa)` | substrate preservation |
>
> Then `limsup_N E_{mu^r_N}[d^r] <= eps_r`, with equality to `0` when `eps_r = 0`,
> and the engine's protected guarantee holds throughout.

The proof is S3: the first six rows give `(P1)`, the transport rows give `(P2)`,
and the last two keep the engine's guarantee alive while the control runs.

**The intensity variable.** `w^r_t` is the *allocated* authority: the share of
service assigned to `r` and, in the realization, the enforcement multiplier
`beta`. It is predictable. The magnitude of force actually applied is `w^r_t d^r_t`
and is endogenous — the engine decides how hard the allocated authority has to
push. `SERVICE_FORCE_TYPING.md` carries the audit; the earlier reading, which took
the position magnitude as the service variable, is withdrawn there.

## Logical Induction instantiation, line by line

| stack object | LI instance |
|---|---|
| priced state `p` | the market's displayed prices `P_t` on the fragment `Phi_t` |
| admissible region `K^r_t` | the reason's rational row system, one row family per reason |
| live assessment set `A_t` | `PC(D_t)`, or `Omega_t^live` in the generalized lift; nested, so it shrinks |
| position `zeta^r_t` | the compiled violation-proportional position `sum_j beta_j g_j(P_t) c_j` |
| defect `d^r_t` | the row violation `g_j(P_t)` at the displayed price |
| misfit `s^r_t(omega)` | the row's signed misfit `r_j - <c_j, omega>` at an assessment world; its positive part is the deficit that bounds liability |
| allocated service `a^r_t` | the enforcement multiplier `beta_{t,j}`, equivalently the promised tolerance `delta_t`; predictable, and bounded by a per-date capacity `b_t^2/((eps_t + M_t) D_t^2)` |
| realized force | `beta_{t,j} g_{t,j}(P_t)`, endogenous at the fixed point |
| Actionability | **a theorem, not a premise**: the per-date modulus `sum_j a_{t,j} d_{t,j}^2 <= eps_t + M_t`, kernel-checked |
| Uptake | **a theorem, not a premise**: the market maker's cumulative cap gives `omega(sum_{i<=n} E_i) <= U = 1 + B_F` at every live world |
| service-weighted Progress | `E_{nu^a_N}[d] <= \|s^+(omega)\|_{L^2(nu^a_N)} + sqrt(U/A_N)`, and `<= sqrt(S_N/A_N)` unconditionally |
| affordability account | `V_N(omega) = sum_{t,j} a_{t,j} d_{t,j}(d_{t,j} - s_{t,j}(omega))`, signed and cumulative, an identity at every world |
| SafeCert | `V_N(omega) >= -B` for every date and every live `omega` |
| substrate preservation | bounded liability implies no efficiently computable trader exploits the modified market, each with assessed net worth at most `1 + B` |
| joint response | rows add inside one compiled position; interference is a budget split, `U_j = 1 + B_F + sum_{k != j} B_k` |
| service transport | **not realized**; `(T1)`–`(T3)` remain schematic and the scheduler that supplies them is not part of the traderized construction |

Two lines are worth reading twice.

**Actionability and Uptake are not premises in LI.** They are the liability
identity and the maker's fixed-point cap. What remains a genuine hypothesis is the
account floor, and the whole affordability question is whether it holds.

**The conclusion is sharper and weaker than the schematic's.** Sharper: an
explicit rate, `A_N^{-1/2}` in the allocated service, and an explicit residual.
Weaker: the residual is the norm's own weighted mean-square exclusion of the
still-live worlds, not zero. Force drives conformance exactly to the level at
which the norm is consistent with what can still be true.
`LI_PROGRESS_FROM_SERVICE.md` has the inequalities.

## What is deleted

**Self-financing**, as a named condition. It was a fifth name for the
world-compatible regime, presented as necessary; it is sufficient and not
necessary, and the four-regime taxonomy already covers the ground.

**Per-reason Uptake from the criterion.** Withdrawn; the criterion does not
quantify over the enforcement position, which is in the price-setting aggregate and
is not required to be efficiently computable.

**Contiguity as a derived consequence of transport.** Withdrawn; what is derived is
a density bound on the transported claim measure.

**`J_t`'s third coordinate**, already retired by the round.

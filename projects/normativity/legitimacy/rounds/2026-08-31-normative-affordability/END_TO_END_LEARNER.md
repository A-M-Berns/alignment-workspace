# The end-to-end normative learner

## 1. The chain

```text
  Answerability claim stream           c^r_t,  C^r_N -> infinity
            |                          [standing]
            |  transport plan T^r, adapted, both marginals predictable
            v
  Allocated service                    a^r_t,  A^r_N -> infinity
            |                          [scheduling]
            |  compiled control law kappa_t : P |-> sum a g(P) c
            v
  Reactive LI force                    d^r_t = g(P_t) at the fixed point
            |                          [engine]
            |  modulus + cumulative cap
            v
  Service-weighted Progress            E_{nu^a}[d] -> friction residual
            |                          [engine]
            |  transport stability (T3)
            v
  Claim-weighted Sustainable Progress  limsup E_{mu^r}[d^r] <= L K F_r + eps_r
```

## 2. The theorem

> **Sustainable Progress.** Fix a reason `r` persistent on a tail with bounded
> defect `0 <= d^r <= D`. Under the premises below, for every `omega` live at `N`,
>
>     E_{mu^r_N}[d^r]  <=  L_r K_r ( || s^+(omega) ||_{L^2(nu^{a,r}_N)}
>                                    + sqrt( U_r / A^r_N ) )
>                          + eps_r + D R^r_N / C^r_N ,
>
> hence
>
>     limsup_N E_{mu^r_N}[d^r]  <=  L_r K_r F_r  +  eps_r ,
>
> where `F_r = limsup_N inf_{omega} || s^+(omega) ||_{L^2(nu^{a,r}_N)}` is the
> **settlement-friction residual** and `eps_r` the **transport residual**. Both
> vanish exactly when the norm is asymptotically compatible with some persistently
> live world and deferred service is exactly defect-preserving.

| premise | layer |
|---|---|
| claim weights `c^r_t` with `C^r_N -> infinity` | Answerability / standing |
| `a^r_t` chosen from `F_{t-1}`, inside the capacity box `a^r_t <= cap_t` | service scheduling |
| `A^r_N -> infinity` | service scheduling |
| adapted plan `T^r` with claim marginal, service feasibility against `a^r`, cap `K_r`, residual density `-> 0` | service scheduling |
| stability `d_t <= L_r d_s + eps_r` on the plan's support | semantic transport |
| the docket's rows are priceable and `K_t != empty` in the cube | force / Actionability |
| the compiled law is continuous and the market maker's contract holds at slack `eps_t` against ordinary volume `M_t` | learner Uptake |
| `V_N(omega) >= -B` for every date and every live `omega` | affordability / safety |
| bounded liability implies no efficiently computable trader exploits the modified market | substrate preservation |

The proof is three inherited steps and one new one. Force and Uptake give the
modulus and the cumulative cap; `LI_PROGRESS_FROM_SERVICE.md` P4 turns them into
the service-weighted statement against `nu^{a,r}`; `SERVICE_TRANSFER.md` T3 carries
that to the claim measure; and the safety premise keeps the substrate's guarantee
alive while the control runs.

**The two residuals are different objects and must not be merged.** `eps_r` is a
claim about the reason: the defect at the claim date is controlled by the defect at
the service date. `F_r` is a claim about the norm: its exclusion of the still-live
worlds vanishes in the weighted mean square. A scheduler can influence neither.

## 3. Affordability, retyped

An **affordability witness** at a history `h` is a predictable sequence
`(a_t, kappa_t)` such that:

1. `a_t >= 0` lies in the capacity box, and `kappa_t` is the control law compiled
   from the docket and `a_t` — continuous, hence a legal day-`t` strategy;
2. for every persistent reason, an adapted transport plan with declared constants
   matches the claim stream to `a^r`;
3. the realized controls `u_t = kappa_t(x_t)` produce an account
   `V_N(omega) >= -B` at every date and every live `omega`;
4. the engine's guarantee survives, by the preservation theorem.

> **Affordability chooses authority; the engine determines how much force that
> authority must exert.**

The viability problem therefore has two coupled dynamics with different inputs:

    b^r_{t+1}  =  max(0, b^r_t + c^r_{t+1} - a^r_t)         backlog, consumes a
    V_{t+1}(omega)  =  V_t(omega) + a_t d_t (d_t - s_t(omega))   account, consumes u_t

The backlog is driven by a predictable variable and the account by an endogenous
one, and the coupling runs one way: `a` sets the capacity within which `d` is
determined, and `d` then sets what the account is charged.

**T7 survives with its safe set moved into `a`-space.** Its max-weight step
schedules a predictable variable, which is now correct rather than accidental, and
the safe region is `{a : a_t <= cap_t}` — an interval per row, hence convex, so
the drift argument is unchanged. What is new is that the endogenous reduction of
force makes existence *easier*: by P5 the charge is `O(sqrt(a))`, so a divergent
allocation can sit inside a finite lifetime budget. The claim the round could not
state before is now exact and exhibited:

> A persistent reason can receive divergent service mass `sum_t a_t = infinity`
> while consuming finite total liability, because the realized corrective force
> dies away as compliance improves.

`tests/test_service.py::CapacityInAuthoritySpace` exhibits it at exact rationals;
`successful_learning` is the simplest instance, with constant authority, geometric
violation, allocation `N` and force mass under `2`.

## 4. What actually remains

### Already concrete

Settlement interface and its no-claw-back monotonicity. The row compiler, its
priceability test and the legality audit of the compiled position. The reactive
control law and the market maker's fixed point. The per-date enforcement modulus
(`weighted_square_le_slack_add_volume`) and the enforcement inequality
(`weighted_square_le_pair`), both kernel-checked. The liability identity and the
signed cumulative account. Bounded-liability preservation, unconditional in the
deductive instance.

### Closed by this pass

The service typing: `a = beta`, predictable, with realized force endogenous, and
the control typed as a law rather than a position. The Answerability-to-LI service
interface: transport now matches the claim stream to a predictable allocated-service
stream. Service-weighted Progress with an explicit rate `A_N^{-1/2}` and an explicit
friction residual. The capacity region in `a`-space. The sublinearity of liability
in allocated authority, which is why persistent service is affordable at all. The
coercivity form of Actionability, which subsumes the linear and quadratic cases in
one theorem.

### Still missing — mathematics

1. **Necessity of bounded liability** (item 40). Still the load-bearing gap.
2. **An affordable schedule.** With the capacity box and the `a`-space viability
   problem both stated, the question is now well posed and unanswered: does a
   schedule with `A^r_N -> infinity` for every persistent reason exist inside the
   caps, against an adversarial docket arrival process?
3. **Transport stability certificates.** `(T3)`'s constants have no construction,
   and across an era boundary no candidate mechanism at all.
4. **`C_t` versus `K_t`** (item 39): whether normative statics produce a credal
   constraint or only a price demand.
5. **Whether a practice's endorsements are priceable.** The round exhibits the
   failure and not its frequency, and the statics generate the good trajectories
   only for affine demands, not sentence-shaped ones.
6. **A causal overload certificate**, in the potential form, after item 40.

### Verification debt, not missing mathematics

The generalized live-world TradingFirm lift's transcription obligation; the
modified market's computability. Lean for §2–§5 of `LI_PROGRESS_FROM_SERVICE.md`,
which are elementary given two kernel-checked inequalities. Non-vacuity witnesses
for the retyped affordability definition.

## 5. The success criterion, answered

> What exact predictable object does Answerability control in a traderized logical
> inductor, and why does persistent service of that object imply Progress while
> bounded liability preserves the learner?

Answerability controls the **docket and the intensity vector `a_{t,j} = beta_{t,j}`**,
equivalently the promised tolerance schedule, chosen from the record through the
previous date and bounded by a per-date liability allowance. It does not control
the displayed price, the violation, the realized position, or the force.

Persistent service of `a` implies Progress because the market maker's contract
bounds the `a`-weighted squared violation per date, so divergent `A_N` drives the
`a`-weighted mean-square violation to zero up to the norm's own misfit with the
still-live worlds, at rate `A_N^{-1/2}`.

Bounded liability preserves the learner because the enforcement position's
cumulative assessed value staying above a floor is exactly the hypothesis of the
preservation theorem, and it is compatible with divergent `A_N` because the charge
grows like the square root of the authority rather than linearly.

The remaining type mismatch is closed. What is left is not a typing question but
three mathematical ones: whether bounded liability is necessary, whether an
affordable schedule exists, and what certifies transport stability.

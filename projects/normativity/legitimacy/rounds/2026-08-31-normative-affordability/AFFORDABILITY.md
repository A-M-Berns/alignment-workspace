# Normative Affordability and Sustainable Progress

## 1. The revised definition

An **affordability witness** at a history `h` is a causal sequence
`(a_t, kappa_t)`, each chosen from `F_{t-1}`, together with an adapted family of
transport plans `T^r` and declared constants, such that at every date:

1. **Legality.** `a_t >= 0` is the allocated authority per reason and `kappa_t` is
   the control law compiled from the docket and `a_t`, carrying whatever
   regularity the engine's response needs. The **realized** control is
   `u_t = kappa_t(x_t)` and is not predictable.
2. **Service fidelity.** For each persistent reason `r`, `T^r` satisfies the
   transport conditions `(T1)`–`(T3)` of `SERVICE_TRANSFER.md` against the
   allocated-service stream `a^r`, with constants `(L_r, eps_r, K_r)` and residual
   density tending to zero. `T^r(t, s)` is fixed by `F_s`: the plan commits when
   the service is delivered, not at the horizon.
3. **Safety.** The realized `kappa = (u_t)_t` lies in the prefix-closed,
   settlement-antitone safe class at budget `B`. A *local* authority-capacity set
   is one way a policy establishes this and is not the condition itself —
   `CAPACITY_VS_SAFETY.md` keeps the two apart, and exhibits a policy inside its
   capacity at every date whose lifetime account is unbounded below.

`SERVICE_FORCE_TYPING.md` is the audit behind clause 1: the service variable is
the *allocated* authority, and the control is a law rather than a position,
because neither the realized position nor the realized force is available at the
date the round's control must be chosen.

**Normative Affordability** at `h` is the existence of such a witness.

Three changes from the candidate definition, each with its reason.

**Contiguity is gone.** Clause 2 replaces `mu^r_N ◁ nu^r_N` with a transport
plan. The two are **incomparable** routes to the same conclusion, not one deriving
the other: contiguity is exactly the right *characterization* (T1, T2) when
nothing is assumed about the defect, and the wrong primitive, because it is not
checkable at a finite horizon, not quantitative, and violated by bounded-delay
service, which the theory has no reason to forbid. What the plan proves is a
density bound on the *transported* claim measure, and it buys that with `(T3)`, a
hypothesis about the reason rather than about the schedule.

**The `q` coordinate is gone.** The reason-indexed object Uptake scores is the
reason's own position, already determined by clause 1.

**The certificate `C` is gone as a separate argument.** Membership in the safe
class is the certificate; a presentation of that class — an account, a risk
functional — is an engine declaration, not an argument of the definition.

**The service variable is allocated, not realized.** Reading `w_t` as the realized
force makes clause 2 a demand on the engine's behaviour rather than on the
scheduler, and leaves the service measure undefined exactly where the reason is
perfectly satisfied. `SERVICE_FORCE_TYPING.md` §2 exhibits both failures.

**Nonemptiness of the common region has moved out.** It is a precondition for the
enforcement inequality to have a region point to evaluate at — a property of the
docket, not of the schedule — so it belongs to the force interface. Keeping it here
made every affordability statement carry a hypothesis about what the reasons demand
of each other rather than about what the reasoner can afford.

## 2. The composition theorem

**Theorem T6 (Sustainable Progress).** Fix a reason `r` persistent on a tail, with
claim weights `c^r_t`, `C^r_N -> infinity`, and a bounded defect `0 <= d^r <= D`.
Assume an affordability witness, and:

- **(Act)** single-reason Actionability at the realized state:
  `g^r_t >= gamma_r d^r_t` with `gamma_r > 0`, where `g^r_t` is the reason's gain
  at the state the aggregate control actually produced. The traderized realization
  supplies a *friction* form of this rather than the clean one — the gain is at
  least `w^r_t (d^r_t - e^r_t)`, with `e` the misfit between the norm and the live
  assessment worlds — so the margin is `1` and the residual is a subtracted misfit.
  `FOLLOWUP_REPORT.md` §B3 carries the consequence: there the conclusion is that
  the defect converges to the misfit rather than to `0`;
- **(Upt)** per-reason Uptake:
  `limsup_N ( sum_{n<N} w^r_n g^r_n ) / W^r_N <= 0`. Here `w` is *allocated*
  service; the traderized instance supplies a coercive rather than linear form,
  `sum_n w^r_n phi(d^r_n) <= C_N` with `phi(d) = d^2`, and
  `LI_PROGRESS_FROM_SERVICE.md` P7 is the theorem that consumes either.

Then

    limsup_N  E_{mu^r_N}[d^r]  <=  eps_r ,

and in particular `E_{mu^r_N}[d^r] -> 0` when the transport is exactly stable
(`eps_r = 0`). The engine's protected guarantee holds throughout, by clause 3.

*Proof.* By (Act), `gamma_r sum_{n<N} w^r_n d^r_n <= sum_{n<N} w^r_n g^r_n`.
Dividing by `W^r_N` and applying (Upt), `limsup_N E_{nu^r_N}[d^r] <= 0`; the
quantity is nonnegative, so it tends to `0`. Clause 2 and Theorem T3 give

    E_{mu^r_N}[d^r] <= L_r K_r E_{nu^r_N}[d^r] + eps_r + D R^r_N / C^r_N ,

and the first and third terms vanish. `square`

The conclusion the dispatch boxes — `E_{mu^r}[d^r] -> 0` outright — is therefore
**not** what the premises give. Transport buys the claim-weighted conclusion up to
the transport error, and only exact stability across the deferral closes the gap.
That residual is the honest price of allowing deferred service at all, and it is
the sharpest form this round can defend.

### The aggregate-Uptake route

If Uptake is available only for the aggregate control, replace (Upt) by

- **(Upt-agg)** `limsup_N ( sum_{n<N} G_n ) / W^total_N <= 0` for the aggregate
  gain `G_n` of `JOINT_ACTIONABILITY.md` §2, and
- **(Share)** `liminf_N W^r_N / W^total_N > 0`.

Then Theorem T4 gives `G_n >= sum_r w^r_n gamma_r d^r_n`, every term is
nonnegative, and (Share) converts the aggregate density bound into the per-reason
one; the rest is unchanged. Route A uses Actionability at the realized state and
no share condition; route B uses T4 and a share condition. Neither dominates:
route B survives an engine with no per-trader guarantee, route A survives an
unboundedly growing reason set.

## 3. Premise removal

Each countermodel removes one premise and leaves the others intact.

**(i) No service fidelity.** `SERVICE_TRANSFER.md` C1: bounded-deficit Surface
Fairness, one exposed surface in a two-surface rotation, defect entirely on the
unexposed dates. Actionability, Uptake and safety hold vacuously on the exposed
dates; `E_{nu_N}[d] = 0` exactly and `E_{mu_N}[d] = 1/2`. The dilution variant C2
attacks the same premise from the other side, by padding rather than starving, and
is what the parsimony cap `K` exists to stop.

**(ii) No Actionability margin.** With `gamma_r = 0` the inequality
`gamma_r sum w d <= sum w g` is vacuous, and a control with `g^r_n = 0` on every
date satisfies Uptake with equality while `d^r_n = D` throughout. The margin is
the only thing converting a bound on gain into a bound on defect.

**(iii) Individual but not joint Actionability.**
`JOINT_ACTIONABILITY.md` J1: two reasons, individually actionable with gains
exactly at the margin, regions jointly satisfiable, and the aggregated position's
gain against reason 1's own region equal to `-1/8`. If the theorem's Actionability
premise is read against reason-relative admissible regions rather than at the
realized state against a common one, the composition fails with every other
premise intact.

**(iv) No safety certificate.** Drop clause 3 and let the enforcement intensity
grow without bound. The gain inequality is easier to satisfy, not harder, so
Actionability survives; what fails is Uptake, because the engine's guarantee was
conditional on the added control's bounded exposure. The traderized instance is
the liability taxonomy's unsupported shifting authority: repeated refinancing
makes cumulative liability unbounded, and the preservation theorem's hypothesis is
simply absent.

**(v) Retrospective rather than predictable scheduling.** This one does not fail
where the dispatch expects. Let `u_t` be chosen from `F_t` — after round `t`'s
settlement. Service fidelity is untouched: the transport plan's marginals are
unaffected by *when* the control was chosen. What breaks is Uptake. A position
taken with the settlement in hand collects a positive value every round at zero
risk, so its account is bounded below by zero and any *actual-path* safety
predicate passes it, while the modified engine is exploited by construction and
`Uptake(D^kappa)` is false. Predictability is therefore a guard on the safety and
learning premise, and it is the second guard there: robustness of the account
(`SAFECERT.md` §2) and adaptedness of the control are independent, and each
without the other admits the countermodel the other blocks.

## 4. What the decomposition earns

The five removals hit five different mathematical objects — a measure comparison,
a positive constant, a choice of scoring set, a bounded functional, and a
filtration. That is the evidence the decomposition is not a restatement of one
condition in five vocabularies. It is also the evidence for one choice:
**contiguity and the transport plan are alternative discharges of one
obligation**, and the definition above carries the checkable one.

## 5. What this section does not establish

That a witness exists — `EXISTENCE_AND_DUALITY.md`. That `eps_r = 0` is
achievable for any reason type; the exact-stability case is stated, not
constructed. That the countermodels are exhaustive for their premises: each shows
the premise is not removable, not that it is the weakest hypothesis in its slot.

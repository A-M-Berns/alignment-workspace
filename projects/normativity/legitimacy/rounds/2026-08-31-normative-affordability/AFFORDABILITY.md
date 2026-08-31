# Normative Affordability and Sustainable Progress

## 1. The revised definition

An **affordability witness** at a history `h` is a causal sequence `(w_t, u_t)`,
each chosen from `F_{t-1}`, together with an adapted family of transport plans
`T^r` and declared constants, such that at every date:

1. **Joint feasibility and legality.** `(w_t, u_t) in J_t(h_{t-1})` — that is,
   `w_t >= 0`, `u_t = sum_r w^r_t zeta^r_t` lies in the admissible control set,
   and the common region `K_t(h_{t-1}) = intersect_r K^r_t(h_{t-1})` is nonempty.
2. **Service fidelity.** For each persistent reason `r`, `T^r` satisfies the
   transport conditions `(T1)`–`(T3)` of `SERVICE_TRANSFER.md` with constants
   `(L_r, eps_r, K_r)` and residual density tending to zero. `T^r(t, s)` is fixed
   by `F_s`: the plan commits when the service is delivered, not at the horizon.
3. **Aggregate safety.** `kappa = (u_t)_t` lies in the prefix-closed, settlement-
   antitone safe class at budget `B`.

**Normative Affordability** at `h` is the existence of such a witness.

Three changes from the candidate definition, each with its reason.

**Contiguity is gone.** Clause 2 replaces `mu^r_N ◁ nu^r_N` with the transport
plan that derives it. Contiguity is exactly the right *characterization* (T1, T2)
and the wrong primitive: it is not checkable at a finite horizon, it is not
quantitative, and it is violated by bounded-delay service, which the theory has no
reason to forbid.

**The `q` coordinate is gone.** The reason-indexed object Uptake scores is the
reason's own position, already determined by clause 1.

**The certificate `C` is gone as a separate argument.** Membership in the safe
class is the certificate; a presentation of that class — an account, a risk
functional — is an engine declaration, not an argument of the definition.

## 2. The composition theorem

**Theorem T6 (Sustainable Progress).** Fix a reason `r` persistent on a tail, with
claim weights `c^r_t`, `C^r_N -> infinity`, and a bounded defect `0 <= d^r <= D`.
Assume an affordability witness, and:

- **(Act)** single-reason Actionability at the realized state:
  `g^r_t >= gamma_r d^r_t` with `gamma_r > 0`, where `g^r_t` is the reason's gain
  at the state the aggregate control actually produced;
- **(Upt)** per-reason Uptake:
  `limsup_N ( sum_{n<N} w^r_n g^r_n ) / W^r_N <= 0`.

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
condition in five vocabularies. It is also the evidence for one merge: **contiguity
and the transport plan are not two requirements**, and the definition above
carries only the second.

## 5. What this section does not establish

That a witness exists — `EXISTENCE_AND_DUALITY.md`. That `eps_r = 0` is
achievable for any reason type; the exact-stability case is stated, not
constructed. That the countermodels are exhaustive for their premises: each shows
the premise is not removable, not that it is the weakest hypothesis in its slot.

# The exact Service-Value Liability target

## Scope

This pass does not alter the Progress schematic. It asks whether the added authority
needed by one concrete realization preserves the generalized Logical Induction
criterion while enforcing the service-value comparisons consumed by Uptake.

Fix date `n`, a finite fragment `Phi_n`, displayed prices `P_n`, a nonempty closed
convex region `K_n`, and a nearest point

\[
q_n=\Pi_{K_n}(P_n).
\]

The calibrated projection authority uses intensity `lambda_n>=0` and portfolio

\[
\zeta_n=\lambda_n(q_n-P_n).
\tag{1}
\]

The realized enforcement position is `zeta_n`, not the available scalar intensity
alone. At an assessed world `omega`, with service-value payoff vector
`S_n(omega)`, its day value and cumulative net worth are

\[
E_n(\omega)=\langle\zeta_n,S_n(\omega)-P_n\rangle,
\qquad
E_{\le N}(\omega)=\sum_{n\le N}E_n(\omega).
\tag{2}
\]

Small tolerance may make `lambda_n` large. It does not by itself make `zeta_n` or
`E_{<=N}` small.

## What preservation consumes

`EnforcementPreservation.no_efficient_trader_exploits` takes exactly

\[
\exists B<\infty\ \forall N,\omega,
\quad Live_N(\omega)\Longrightarrow E_{\le N}(\omega)\ge-B.
\tag{BL}
\]

It then bounds the ordinary realized TradingFirm above by `1+B` at every live
assessment and contradicts Trading Firm Dominance. The proof uses a uniform constant,
not a rate.

A sublinear allowance `E_{<=N}(omega)>=-o(N)` does not instantiate the theorem. The
definition of exploitation is bounded downside and merely unbounded upside, not
linear-rate upside. An `o(N)` subsidy may itself be unbounded and therefore leaves the
existing contradiction open. A weaker preservation theorem would require a stronger
rate-sensitive exploitation criterion or a new dominance proof; neither is currently
available.

Thus `(BL)` is genuinely the minimal safety condition for the current downstream
theorem, even if another future criterion might consume less.

## Service-Value Liability Problem

> Find checkable conditions on the assessed payoff vectors `S_n(omega)`, normative
> regions `K_n`, live/plausible sets, and ordinary Budgeter process such that `(BL)`
> holds simultaneously with the vanishing-tolerance conformance schedule required by
> Progress.

The condition must tolerate some assessed worlds outside `K_n`; otherwise it is only
the already-proved zero-liability case.

## Exact upstream status

| statement | status | exact source/boundary |
| --- | --- | --- |
| projection force and nonnegative day value at every admitted point | **proved theorem** | `ProjectionForce.force_inequality`, `value_nonneg_of_mem` |
| zero cumulative liability when every historical region admits the assessed point | **proved theorem** | `ProjectionBudget.cumValue_nonneg_of_forall_mem` |
| generic projection liability inequality | **proved theorem** | `ProjectionForce.liability_inequality`; cumulative form in `ProjectionBudget` |
| homothetic-core per-date charge and summable-charge preservation | **proved theorem** | `ProjectionCore.core_day_value_ge`, `core_netWorth_ge_of_summable`; positive core alone does not sum |
| arbitrary changing rational polytopes can be enforced at finite tolerance | **proved theorem** | `RationalConstraintSchedule.conformance_of_constraints` and `criterion_of_constraints` |
| added authority plus uniform assessed lower bound preserves non-exploitation | **proved theorem** | `EnforcementPreservation.no_efficient_trader_exploits` |
| ordinary TradingFirm has live-world floor `-2` | **proved theorem** | `AssessmentFirm.tradingFirmTrader_netWorth_floor` |
| priced aggregate has cumulative value `<1` at every PC world | **proved theorem** | source `marketMaker_netWorth_lt_one`, used by `EnforcementPreservation.realizedFirm_netWorth_le` |
| one-coordinate stationary interior affordability under containment, margin, and no cross-coordinate subsidy | **model-supported conjecture** | open PR50 C0; six of eight promotion steps lack Contrib support |
| centered point peg is tolerance-independent; near-vertex liability scales as inverse margin | **model-supported conjecture** | PR50 exact fixtures, unregistered |
| summable set-gap motion is affordable | **model-supported conjecture** | PR50 bounded-gap probe; no general theorem |
| homothetic core is necessary for affordability | **counterexample** | PR50 `K={1/2}` fixture |
| separately affordable coordinates compose | **counterexample** | PR50 two-coordinate pump-and-drain fixture |
| per-date compatible mixtures compose across time | **counterexample** | the same pump: covered mixtures exist per era, but no common one exists |
| multi-coordinate joint-margin theorem | **open conjecture upstream of this pass** | PR50 `FOLLOWUP_STOCK.md` items 1--3 |

PR50 is read at open-PR head
`fa22b8a21cbd2bde81efe4cb0cd13d5551bbd51d`. Nothing in this round changes PR50 or
promotes its fixture grades.

## A new route from existing theorems

The key additional observation is that projection admits fractional comparison
points. Let a finite set of live assessed worlds `Omega_N` carry a probability
distribution `mu_N`, and define the barycenter valuation

\[
\bar S_{\mu_N}=\sum_{\omega\in\Omega_N}\mu_N(\omega)S(\omega).
\]

If this one barycenter lies in every historical region `K_k`, `k<=N`, then
`cumValue_nonneg_of_forall_mem` gives

\[
\sum_\omega\mu_N(\omega)E_{\le N}(\omega)
=E_{\le N}(\bar S_{\mu_N})\ge0.
\tag{3}
\]

Linearity supplies the equality. This is the input to the Common-Mixture theorem in
`JOINT_MARGIN.md`.


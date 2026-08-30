# Report: Service-Value Liability hard pass

## Executive result

The common compatible mixture hypothesis is true in a stronger and cleaner form than
the PR50 flow heuristic suggested.

One uniformly covered mixture whose barycenter lies in every enforced region makes
the projection authority's cumulative mixture value nonnegative. The MarketMaker's
cumulative cap and the ordinary TradingFirm's proved live-world floor independently
bound the authority above at every assessed world. A finite weighted-sum argument then
forces a uniform lower bound:

\[
\boxed{
E_{\le N}(\omega)
\ge-(C+B_F)\frac{1-\theta}{\theta}.}
\]

With current workspace constants `C=1`, `B_F=2`, the bound is
`-3(1-theta)/theta`. It is independent of tolerance and has no explicit dimension
factor. It allows several simultaneous repair directions and worlds that individually
violate the normative rows.

PR50's pump passes the critical negative test in the right way. Each low/high era has
a compatible mixture with coverage `3/40`, but the disjoint psi bands admit no single
mixture through time. The pump violates temporal common compatibility rather than
refuting the theorem.

## Governing questions

### 1. What exact bounded-liability property is required?

The current preservation theorem requires one finite constant `B` such that for every
horizon and live assessed world,

\[
E_{\le N}(\omega)\ge-B.
\]

The authority portfolio is `zeta_n=lambda_n(Pi_{K_n}(P_n)-P_n)` and its cumulative
net worth is the sum of `zeta_n dot (S_n(omega)-P_n)`. A sublinear but unbounded loss
does not instantiate `EnforcementPreservation`: exploitation requires merely
unbounded upside, not a positive asymptotic rate.

### 2. What is PR50's one-coordinate plausibility margin mathematically?

It is the loss per unit opposing inventory at a live throttling vertex, paired with
the authority's loss per absorbed unit at the billing vertex. It converts the
Budgeter's worldwise floor into a flow cap. For a binary point peg `{c}`, it is also
exactly the minimum mass `min(c,1-c)` of the unique compatible mixture. For a strict
interior interval `[lo,hi]`, PR50's margin is `min(lo,1-hi)`, whereas optimal mixture
coverage is `1/2-dist(1/2,K)`; the latter is at least the former but can be larger.

### 3. Is it captured by a compatible assessed-world mixture?

Exactly for binary point pegs, and qualitatively in PR50's strict-interior regime.
Not numerically for general intervals. Direct margin controls all peg locations and a
flow direction; mixture coverage selects one barycenter and controls aggregate
authority liability.

### 4. Does one covered compatible mixture eliminate cross-coordinate recycling?

Yes, at the aggregate-liability level. The proof does not need to show that every
ordinary trade depletes a per-coordinate account. Projection makes the authority
nonnegative in the common mixture potential; MarketMaker plus the TradingFirm floor
bounds authority gains elsewhere, so no covered world can carry unbounded authority
loss. Ordinary traders may recycle internally, but it cannot break the resulting
global lower bound.

### 5. Does PR50's cross-subsidy witness violate the condition?

Yes. In each era, product means `(1/2,3/20)` and `(1/2,17/20)` give full support with
coverage `3/40`. But the low psi interval ends at `1/5` and the high interval begins
at `4/5`; no single expectation lies in both. The condition fails persistently at the
temporal seam.

### 6. Can a useful Common-Mixture Affordability theorem be proved?

Yes. If aggregate market value is at most `C`, ordinary firm value is at least
`-B_F`, and one `theta`-covered mixture gives nonnegative authority value, then

\[
E_{\le N}(\omega)\ge-(C+B_F)(1-\theta)/\theta.
\]

Current named Lean theorems provide every market/accounting premise. Only the finite
weighted-sum packaging is not yet formalized. The theorem permits arbitrary dimension,
finite simultaneous constraints, and arbitrary region motion so long as the same
retrospectively compatible barycenter survives.

### 7. Can a recycling coefficient characterize a wider safe regime?

Algebraically, yes. If `E(omega)<=U`, coverage is `theta`, worst liability is `L`, and
the mixture potential satisfies

\[
\Lambda_N\ge-S-\kappa L_N,
\]

then `kappa<theta` gives

\[
L_N\le\frac{S+(1-\theta)U}{\theta-\kappa}.
\]

With normalized `r=kappa/theta`, the threshold is `r<1`. Common compatibility is
`kappa=0`. What remains open is a checkable derivation of `kappa` from general moving
constraint and settlement geometry. PR50's unbounded pump necessarily violates every
uniform below-threshold certificate.

### 8. Does stochastic-repair structure help?

It reduces every normative requirement to a bounded zero-sum direction and makes the
compatibility test a finite linear feasibility problem. Several common-target or
disjoint repair rows can share one covered mixture. But structure does not make
compatibility automatic: an acyclic comparison can conflict with correlated
settlements, and positive cycles can make the semantic region empty.

### 9. Is directional repair-security enforcement sufficient?

Yes. Progress only consumes lower bounds on `u_x^T hat v`; it does not need global
distance to a full polytope. Each direction can be enforced as an underlying-value
portfolio or a rescaled `[0,1]` difference security. Multiple directions remain
subject to one joint mixture condition; separate scalar affordability does not
compose.

### 10. Does time multiplexing reduce liability?

Only when every recurrent row shares one common potential or switching costs have a
separate summable bound. Otherwise it moves recycling across time. PR50's alternating
bands are already a time-multiplexed counterexample: each era is covered, but repeated
disjoint switches recharge the attack. Surface Fairness does not make the set-gap sum
finite.

### 11. Is world inclusion merely sufficient, or semantically natural?

It is a strong sufficient condition and gives exact zero liability. It can be natural
for normative-status securities whose settlement rules independently encode protocol
facts. It is generally circular for descriptive future-evaluator securities if it is
imposed solely to guarantee current normative rows. The common-mixture theorem is
strictly weaker and allows disagreeing worlds.

### 12. Are normative rows being imposed on the wrong security type?

Sometimes. Descriptive evaluator securities create a real compatibility problem
because future evaluation can contradict present norms. Normative-status securities
may justify the rows but need a status-to-service-gain bridge. Synthetic learning
scores avoid settlement liability but are control signals, not predictions. The
compiler must type these semantics rather than treating them as interchangeable.

### 13. Can direct certified losses avoid liability?

Yes. Choose predictably any rational `v_n in K_n` and feed the repair learner
`ell_n=1-v_n`. Regret bounds the gain at `v_n`, and robust gain is no larger than that
gain, so signed Uptake follows directly. This retains the schematic robust-unanimity
condition but loses market aggregation, calibration, and the Logical Induction
interpretation. It is a fallback realization, not a reason to abandon the market
route now that the common-mixture fragment survives.

### 14. What is the strongest nonzero-liability realization justified?

A finite simultaneous family of Answer-Mode repair directions, enforced either
directionally or as one polytope, with one support-local assessed distribution of
coverage `theta>0` whose barycenter satisfies every active and historical row. The
authority bound is `3(1-theta)/theta`, independent of enforcement tolerance. This is
a proved paper theorem by composition of current workspace results, not merely a PR50
fixture claim.

### 15. What exact mathematical problem remains?

Characterize when a typed descriptive service-value compiler guarantees a covered
point in

\[
K_{\le N}\cap C_\theta(S(Live_N))
\]

at every horizon, or derive a schedule-local potential-deficit coefficient
`kappa<theta` when this retrospective intersection is empty. Moving evaluator
settlements and potential switching are the hard general case. PR50's summable
set-gap conjecture is one candidate subfragment, not yet a theorem.

### 16. Should this block merging PR69 as a research checkpoint?

No. PR69 now contains a stable schematic, a meaningful finite multi-repair
bounded-liability route, and an exact diagnosis of the principal counterexample
outside that route. The remaining problem should block any claim that arbitrary
descriptive value-security enforcement is settled. It should not block merging a
research checkpoint that states the condition and debt explicitly.

## Final assessment

The common-mixture result closes Service-Value Liability for a genuine basic Progress
fragment, including several simultaneous repairs. It does not settle arbitrary moving
regions, future-evaluator disagreement, or all possible Answer-Mode settlement
semantics. The value-security architecture survives; its compiler must expose covered
compatibility as an explicit realization certificate.

### `SERVICE-VALUE-LIABILITY-CLOSED-FOR-BASIC-PROGRESS`


# Specialization to Progress repair directions

## What Progress actually consumes

For defective source mode `x`, an Answer-Mode certificate provides a probability
distribution `mu_x` over acceptable responses and direction

\[
u_x=\mu_x-e_x,
\qquad \sum_i(u_x)_i=0.
\]

The finite repair-kernel proof needs only

\[
u_x^\top\hat v_n\ge\gamma_x-\tau_n
\tag{7}
\]

on the service dates where the reason applies. It does not need every coordinate of
`hat v_n` to be close to every point of a large normative polytope.

If the repair sends source mass `p_n(x)` along `u_x`, then `(7)` gives

\[
\langle\Phi(p_n)-p_n,\hat v_n\rangle
\ge\sum_xp_n(x)(\gamma_x-\tau_n).
\]

Confidence-rated modification regret therefore yields the same master inequality and
Uptake. **Directional enforcement is mathematically sufficient for Progress.**

## Derived repair securities

Because `u_x` has positive mass one and negative mass one,

\[
-1\le u_x^\top V\le1.
\]

The rescaled repair-difference security

\[
G_x=\frac{1+u_x^\top V}{2}\in[0,1]
\]

turns the row into the scalar threshold

\[
P(G_x)\ge\frac{1+\gamma_x}{2}-\frac{\tau_n}{2}.
\]

Equivalently, the authority can trade the underlying value securities directly in
direction `u_x`. The latter keeps all regret feedback inside one action-value vector
and avoids assuming separately priced derived securities satisfy exact same-round
linearity.

One row can therefore inherit either:

- PR50's model-supported isolated one-coordinate affordability result, after
  rescaling and under its containment/margin/no-subsidy hypotheses; or
- the proved Common-Mixture theorem, if one covered assessed-world mixture makes the
  row's expected payoff satisfy its threshold.

The second route is stronger because it composes across directions.

## Finite simultaneous Answer-Mode realization

Let `R` be a finite family of operative repair rows. Suppose one assessed-world
distribution `mu` has coverage `theta>0` and expected service-value vector `bar v`
satisfying

\[
u_x^\top\bar v\ge\gamma_x
\qquad\text{for every }x\in R.
\tag{8}
\]

Each directional projection trade has nonnegative expected value under the same
`mu`; hence their aggregate does too. The Common-Mixture theorem applies to the
aggregate authority without separating accounts or coordinates:

\[
E_{\le N}(\omega)\ge-3(1-\theta)/\theta.
\]

This is a meaningful, nonzero-liability, finite multi-repair realization of the
authority-safety half of basic Progress. Worlds may individually contradict rows;
only one covered barycenter must satisfy all of them. Projection tolerance can vanish
arbitrarily and several repairs may be active simultaneously.

The full realization still separately assumes the typed compiler, Surface Fairness,
and the exact finite confidence-rated modification-regret package identified by PR69.
The liability theorem does not discharge those obligations.

## Does repair structure make compatibility automatic?

No. It makes the required constraints transparent and directional, but it does not
control the settlement convex hull.

### Common target

For one-hot settlement profiles on modes `{x_1,x_2,y}`, the mixture mean
`(1/5,1/5,3/5)` gives both `v(y)-v(x_i)>=1/5` with coverage `1/5`. Several sources
sharing an answer can therefore be jointly affordable.

### Disjoint acceptable sets

For one-hot profiles on `{x_1,y_1,x_2,y_2}`, mean
`(1/8,3/8,1/8,3/8)` gives both pairwise margins `1/4`. Disjoint pairs are not a
problem by themselves.

### Acyclic answer graph

Acyclicity makes positive comparison rows feasible in an unconstrained value cube,
but it does not imply settlement compatibility. If the only assessed profiles are
`(0,0)` and `(1,1)`, every mixture has `v(y)-v(x)=0`; the acyclic row
`v(y)-v(x)>=1/2` has no compatible mixture.

### Cyclic answer graph

A positive pairwise cycle is already semantically infeasible: summing its rows gives
`0>0`. The compiler's nonemptiness screen must divert it before enforcement. More
general stochastic cycles can be feasible only when their directions do not sum to a
strict positive contradiction; feasibility still does not imply covered settlement
compatibility.

### Action plus inquiry and overlapping kernels

They compose exactly when `(8)` has a covered solution in the assessed settlement
hull. Labels and overlap do not matter to the theorem. Correlations in settlement
payoffs do: separately compatible marginals may have no single joint distribution.

Thus the special zero-sum/conic structure reduces the geometry to a finite linear
feasibility certificate, but does not solve it automatically.

## Full-polytope versus directional enforcement

| question | full polytope | directional rows |
| --- | --- | --- |
| sufficient for Progress gain bound | yes | yes |
| requires global distance calculation | yes | no |
| enforcement coordinates | all service values | only operative repair directions |
| common-mixture liability condition | barycenter in `K` | every active row holds at one barycenter |
| separately affordable rows compose | no | no |
| exact conformance result already in workspace | yes | follows by scalar/halfspace specialization |

Directional enforcement is the preferred minimal realization. It avoids enforcing
normative coordinates the Progress proof never reads. It does not remove the joint
condition: multiple directional authorities can still be funded by one another unless
one common mixture or another bounded-recycling certificate controls their aggregate.

## Time multiplexing

Coupling Surface Fairness to enforcement exposure is safe under a fixed common
mixture: every activated row has nonnegative value in the same potential, so arbitrary
fair rotation preserves the theorem.

Without a common mixture, multiplexing merely converts spatial recycling into temporal
recharge. PR50's pump already alternates individually covered psi bands; it is an exact
example of per-era affordability plus recurrent switching producing unbounded loss.
A bounded-deficit scheduler does not make the set-gap sum finite. Fair rotation through
disjoint requirements generally repeats the bill forever.

A multiplexed theorem therefore needs one of:

1. one covered mixture satisfying every row that can recur;
2. a proved bounded-recycling certificate with `kappa<theta`;
3. genuinely fenced ordinary-trader capital in the market semantics; or
4. finite/summable switching cost plus a theorem controlling authority turnover.

Only item 1 is proved here.

## Account separation

- Separate repair comparators are an online-learning device and say nothing about
  market wealth.
- Separate authority ledgers make attribution clearer but their losses still add.
- Separate Budgeter components have individual floors, yet ordinary traders can move
  gains through shared securities or adaptive strategies; PR50's patsy and pump
  fixtures distinguish redistribution from self-financing recharge.
- Only a semantic inability to transfer wealth, or an aggregate potential such as the
  common mixture, closes cross-subsidy.

No result in this pass relies on fictional per-reason accounts.

## Surviving theorem hierarchy

### Tier A: proved common-mixture theorem

- **Hypotheses:** finite support-local assessed profiles; coverage `theta`; one
  barycenter admitted by all active/historical regions; ordinary firm floor and
  MarketMaker aggregate cap.
- **Bound:** `(C+B_F)(1-theta)/theta`, equal to `3(1-theta)/theta` in current LI.
- **Tolerance:** independent.
- **Dimension:** no explicit factor; implicit through achievable `theta`.
- **Motion:** arbitrary if the same retrospective barycenter remains admitted.
- **Repairs:** finite simultaneous family allowed.
- **Status:** proved by composition of existing workspace theorems and finite algebra.

### Tier B: proved algebraic closure, open geometric realization

- **Hypotheses:** potential deficit `Lambda_N>=-S-kappa L_N`, `kappa<theta`.
- **Bound:** `[S+(1-theta)U]/(theta-kappa)`.
- **Status:** algebra proved; deriving `kappa` from a general schedule is open.

### Tier C: Progress-specialized common-mixture realization

- **Hypotheses:** finite Answer-Mode rows and one covered assessed mixture satisfying
  all row margins.
- **Bound/status:** inherits Tier A; proved authority-safety route.

### Tier D: PR50 isolated directional result

- **Hypotheses:** one rescaled direction, stationary interior margin, containment and
  actual no-subsidy.
- **Status:** model-supported conjecture, not promoted here.


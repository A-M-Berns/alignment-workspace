# Controlled drift

## 1. The exact switching ledger

Let `e_n` be the authority's day-payoff vector, `E_n=sum_{k<=n}e_k`, and let
`mu_n` be a `theta`-covered potential that underwrites the current exercise:

\[
\mu_n\cdot e_n\ge0.
\]

Changing the potential reprices the historical ledger. Define switching debt

\[
d_n=\bigl[-(\mu_n-\mu_{n-1})\cdot E_{n-1}\bigr]_+.
\tag{SD}
\]

Then the identity

\[
\mu_n\cdot E_n
=\mu_{n-1}\cdot E_{n-1}
+\mu_n\cdot e_n
+(\mu_n-\mu_{n-1})\cdot E_{n-1}
\]

implies

\[
\mu_N\cdot E_N\ge-\sum_{n\le N}d_n.
\tag{PS}
\]

This is the precise sense in which revision can refinance past authority losses. The
quantity is inventory-sensitive: a metric on regions or potentials matters only
through its action on the historical portfolio.

## 2. Bounded switching-debt theorem

Assume every `mu_n` has minimum mass `theta`, every coordinate of `E_n` is at most
`U`, and `D_N=sum d_n<=D` uniformly. Applying the Underwriting Lemma to `(PS)` gives

\[
\boxed{L_N\le\frac{D+(1-\theta)U}{\theta}},
\qquad
L_N=\max_\omega(-E_N(\omega))_+.
\tag{BSD}
\]

This is a genuine controlled-drift theorem. It allows no common potential and makes
the cost of revision explicit.

More generally, if a schedule certificate proves

\[
D_N\le S+\kappa L_N,\qquad \kappa<\theta,
\]

then

\[
\boxed{L_N\le\frac{S+(1-\theta)U}{\theta-\kappa}}.
\tag{RC}
\]

Thus `kappa` is the fraction, in the unnormalized potential units, of worst liability
that potential switching can refinance. The normalized recycling rate is
`r=kappa/theta`; safety requires `r<1`.

## 3. A geometric sufficient condition

Let `t_n=TV(mu_n,mu_{n-1})`, where `TV=||.||_1/2`, and
`T_N=sum t_n`. Since probability differences have total mass zero,

\[
| (\mu_n-\mu_{n-1})\cdot E_{n-1} |
\le t_n(\max E_{n-1}-\min E_{n-1})
\le t_n(U+L_N).
\]

Consequently `D_N<=T_N(U+L_N)`. If `T_N<=T<theta` uniformly, `(RC)` gives

\[
\boxed{
L_N\le U\frac{1-\theta+T}{\theta-T}.}
\tag{TV}
\]

This proves one checkable controlled-drift fragment. Mere summability with total
variation `T>=theta` does not close this self-referential bound. Nor do bounded
per-step Radon--Nikodym ratios or finite per-step KL divergence prevent infinite
cumulative switching. KL/Bregman conditions help only through a bound on the exact
switching work or a summable metric controlling it.

## 4. Region geometry and selection

A region schedule is safe under `(TV)` if it admits `theta`-covered compatible
selectors `mu_n` with lifetime total variation below `theta`. This is stronger than
small Hausdorff motion and different from it:

- moving regions with a fixed compatible barycenter have `T=0`, regardless of their
  boundary motion;
- nested closed regions meeting the compact trimmed hull at every date have a common
  point by compactness, hence `T=0`;
- pairwise overlap need not give a low-variation global selector. In one dimension,
  `{0},[0,1],{1}` has zero gap at each adjacent pair but every selector moves by one.

The correct geometric problem is therefore a **covered compatible selection of
bounded switching work**, not raw region variation.

## 5. Relation to PR50 set gap

For one binary security, a mixture is determined by its mean `c` and

\[
TV(\mu_c,\mu_d)=|c-d|.
\]

The minimum forced switch between two admissible mean sets is exactly their set gap.
This explains why disjoint transitions recharge opposition and why a fixed common
point makes repeated overlapping motion free. But a sum of adjacent set gaps is not
the entire theory: the `{0},[0,1],{1}` example has zero adjacent gaps and positive
global selector movement, and switching debt additionally depends on historical
inventory. PR50's set-gap story is a one-coordinate lower-level shadow of potential
switching, not a general replacement for `(SD)`.

## 6. PR50 pump

The low and high eras separately admit covered product potentials, but their psi
means lie in disjoint bands. Every recurrent switch must change the underwriting
potential. The attack arranges historical inventory so the switching term is
negative, turns that deficit into renewed opposition capacity, and repeats. Hence its
switching debt is not uniformly bounded and no `kappa<theta` certificate can hold.

This identifies the failure more precisely than “two coordinates”: changing
standards refinance an inherited ledger faster than the coverage coefficient can
close the loss.

## 7. Anti-reset

Evaluator revision changes the next increment, not the ledger:

\[
E_{n+1}=E_n+e_{n+1}.
\]

A fresh account is harmless bookkeeping only if consolidated liability still includes
`E_n`. Erasing it invalidates both `(PS)` and the preservation theorem. This
anti-reset principle is an interpretation of cumulative net worth, not a new
Continuity axiom.


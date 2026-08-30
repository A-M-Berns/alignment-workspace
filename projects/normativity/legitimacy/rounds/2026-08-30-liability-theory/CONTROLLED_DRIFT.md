# Controlled drift

## 1. Dates and the exact switching ledger

Work on one fixed finite episode/profile quotient `Omega`. Dates are
`n=0,1,...`. Let `e_n in R^Omega` be the authority's date-`n` payoff vector and

\[
E_n=\sum_{k=0}^{n}e_k.
\tag{1}
\]

At date `n`, let `mu_n` be a probability on `Omega` with
`mu_n(omega)>=theta>0` and suppose it underwrites that date's exercise:

\[
\mu_n\cdot e_n\ge0.
\tag{2}
\]

There is no `mu_{-1}`. Switching begins at date one. For `n>=1`, define the raw
switching debt

\[
d_n=\bigl[-(\mu_n-\mu_{n-1})\cdot E_{n-1}\bigr]_+,
\qquad
D_N=\sum_{n=1}^{N}d_n,
\tag{3}
\]

with `D_0=0`. The identity

\[
\mu_n\cdot E_n
=\mu_{n-1}\cdot E_{n-1}
+\mu_n\cdot e_n
+(\mu_n-\mu_{n-1})\cdot E_{n-1}
\tag{4}
\]

and the base `mu_0 dot E_0=mu_0 dot e_0>=0` imply by induction

\[
\boxed{\mu_N\cdot E_N\ge-D_N.}
\tag{5}
\]

This identity is exact. Switching debt is the negative repricing of inherited
inventory; it is not defined “against” either terminal or running liability. Those
quantities enter only when deriving tractable upper bounds on `(3)`. Normalizing
`d_n` would obscure the ledger identity and buys no stronger theorem.

## 2. Terminal and running liability

Assume the market composition supplies the same pointwise upper envelope at every
date:

\[
E_n(\omega)\le U
\qquad(n\ge0,\ \omega\in\Omega).
\tag{6}
\]

Define

\[
L_n=\max_\omega(-E_n(\omega))_+,
\qquad
\bar L_N=\max_{0\le k\le N}L_k.
\tag{7}
\]

At a fixed horizon, `(5)`, coverage, `(6)`, and the Underwriting Lemma give

\[
L_N\le\frac{D_N+(1-\theta)U}{\theta}.
\tag{8}
\]

The terminal statement is exact. A lifetime guarantee is obtained by applying it at
every horizon and taking the maximum.

## 3. Controlled-Drift theorem hierarchy

> **Controlled-Drift Theorem.** Under `(1)`, `(2)`, coverage, and the uniform upper
> envelope `(6)`:
>
> 1. if `D_n<=D` for every `n<=N`, then
>    \[
>    \bar L_N\le\frac{D+(1-\theta)U}{\theta};
>    \tag{BSD}
>    \]
> 2. more generally, if for every `n<=N`
>    \[
>    D_n\le S+\kappa\bar L_n
>    \qquad\text{with }\kappa<\theta,
>    \tag{9}
>    \]
>    then
>    \[
>    \boxed{\bar L_N\le
>    \frac{S+(1-\theta)U}{\theta-\kappa}.}
>    \tag{RC}
>    \]

Proof of part 2: apply `(8)` at each `n`, substitute `(9)`, and choose
`j<=N` with `L_j=bar L_N`. Then

\[
\bar L_N=L_j
\le\frac{S+\kappa\bar L_j+(1-\theta)U}{\theta}
\le\frac{S+\kappa\bar L_N+(1-\theta)U}{\theta},
\]

and rearrange. Part 1 is `kappa=0`, `S=D`.

A common fixed potential has no switching terms, so `D_n=0` and `(BSD)` recovers
Common-Mixture Affordability. The normalized recycling fraction
`r=kappa/theta` may aid interpretation, but raw `d_n` and `D_n` remain the primary
objects.

## 4. Corrected total-variation corollary

Let

\[
t_n=\operatorname{TV}(\mu_n,\mu_{n-1})
=\tfrac12\|\mu_n-\mu_{n-1}\|_1,
\qquad
T_N=\sum_{n=1}^{N}t_n.
\]

Because a difference of probabilities has total mass zero,

\[
| (\mu_n-\mu_{n-1})\cdot E_{n-1} |
\le t_n(\max E_{n-1}-\min E_{n-1}).
\tag{10}
\]

The old draft incorrectly bounded the last range by `U+L_N`. Later authority trades
can repair an earlier loss, so terminal liability need not dominate earlier loss.
The valid bound is

\[
\max E_{n-1}-\min E_{n-1}
\le U+\bar L_N,
\]

and, horizon by horizon, the sharper form uses `bar L_n`. Hence

\[
D_n\le T_n(U+\bar L_n).
\tag{11}
\]

If one selector sequence satisfies `T_n<=T<theta` at every horizon, then `(11)` is
`(9)` with `S=TU` and `kappa=T`. Therefore

\[
\boxed{
\bar L_N\le U\frac{1-\theta+T}{\theta-T}
\quad\text{for every }N.}
\tag{TV}
\]

The numerical bound is unchanged; the quantified liability is now correct. It
diverges as `T` approaches `theta`, and the strict threshold is a limitation of this
self-financing closure, not evidence that every schedule with `T>=theta` is unsafe.
Many tiny switches and one large switch receive the same conservative bound when
their total TV agrees.

## 5. Selector quantifiers and timing

There are three different claims:

1. **Ex post algebraic audit.** After a run, existence of covered `mu_n` satisfying
   `(2)` and a debt bound proves that run's liability bound. This is mathematically
   valid but not an implementable safety policy.
2. **Adapted design certificate.** For every allowed run, an authority uses a fixed
   causal rule that, after `K_n` and historical ledger `E_{n-1}` are known but before
   the date-`n` projection trade `e_n` is realized, chooses
   `mu_n in M_n`. Compatibility of its barycenter with `K_n` then proves `(2)` for
   every resulting projection trade. A uniform debt or TV bound for this rule is an
   operational certificate.
3. **Region-only certificate.** A selector determined solely by the region schedule
   is stronger. It is convenient but not required by the algebra; allowing dependence
   on `E_{n-1}` can reduce switching debt without hindsight.

For design claims, mere existence of a different good selector for each completed run
is insufficient. The quantifiers required are

\[
\exists\text{ one adapted selector rule }\sigma\quad
\forall\text{ allowed runs generated using }\sigma:\quad
\sup_N D_N<\infty
\]

or the corresponding uniform `(9)`. The rule may use strict-prefix inventory, but
not `e_n`, the current response, or future regions.

## 6. Geometry, selection, and inventory

For each date define the feasible underwriting set

\[
M_n=\{\mu\in\Delta_\theta(\Omega):S\mu\in K_n\}.
\tag{12}
\]

The causal chain is

\[
\boxed{
\text{region motion}
\to\text{forced selector motion}
\to\text{repricing inherited inventory}
\to\text{switching debt}.}
\]

The arrows are not equivalences:

- regions may move arbitrarily while sharing one barycenter, so selector motion and
  debt are zero;
- `{0},[0,1],{1}` has zero adjacent set gaps but every global selector moves by one;
- selectors can move far while `E_{n-1}=0`, producing zero debt;
- an arbitrarily small selector move can produce large debt against sufficiently
  large inherited inventory;
- distinct mixtures with the same barycenter can have large TV while repricing every
  linear authority payoff by zero. TV is therefore only a conservative proxy.

In high dimension `theta<=1/|Omega|`, so `T<theta` can be very restrictive. A schedule
may admit both good and arbitrarily bad selectors; the existential algebra uses the
good sequence, while an authority guarantee requires constructing it causally.

## 7. Exact open problem

For moving finite regions and a fixed finite payoff-profile fragment, characterize
conditions under which there exists one adapted rule

\[
\mu_n=\sigma_n(K_{\le n},E_{n-1})\in M_n
\]

such that, for every allowed authority/opposition run generated with that rule,

\[
\sup_N\sum_{n=1}^{N}
[-(\mu_n-\mu_{n-1})\cdot E_{n-1}]_+<\infty,
\]

or at least

\[
D_N\le S+\kappa\bar L_N
\quad\text{uniformly with }\kappa<\theta.
\tag{13}
\]

A region-only selector is a useful stronger subproblem. General time-varying profile
sets and settlement maps are deferred. This is the precise remaining diachronic
liability problem; the round does not solve arbitrary moving-region affordability.

## 8. PR50 set gap and pump

For one binary security, a mixture is determined by its mean `c` and
`TV(mu_c,mu_d)=|c-d|`; the minimum forced switch between two mean sets is their set
gap. Set gap therefore controls the first two arrows above in that fragment. It does
not see historical inventory or the global selector problem.

PR50's low/high eras separately admit covered potentials but force recurrent movement
between disjoint psi bands. The attack aligns inherited inventory with the negative
repricing direction and converts the resulting debt into renewed opposition capacity.
Its unbounded run cannot satisfy any uniform `(13)`.

## 9. Anti-reset

Revision changes the next increment, not the ledger: `E_n=E_{n-1}+e_n`. A fresh
account is harmless only when consolidated liability retains `E_{n-1}`. Erasing it
invalidates `(4)` and the preservation theorem. This is an interpretation of
cumulative net worth, not a new Continuity axiom.


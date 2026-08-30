# Liability theory

## 1. Exact inherited result

Fix a horizon `N` and quotient the live assessed worlds by equality on every payoff
used by authority inventory through `N`. Write the resulting finite profile set as
`Omega_N`, with profiles `S(omega)`. The authority's cumulative payoff is

\[
E_N(\omega)=\sum_{n\le N}\langle\zeta_n,S_n(\omega)-P_n\rangle,
\qquad
\zeta_n=\lambda_n(\Pi_{K_n}P_n-P_n).
\]

The merged Common-Mixture theorem assumes:

1. `E_N(omega)<=U` on every live profile, obtained from the MarketMaker cap `C`
   and ordinary TradingFirm floor `-B_F`, with `U=C+B_F`;
2. a probability `mu_N` on the profile quotient with `mu_N(omega)>=theta>0`;
3. the barycenter `bar S_mu` belongs to every historical region `K_k` whose
   projection inventory contributes to `E_N`.

Projection linearity then gives `sum mu_N E_N>=0`, hence

\[
E_N(\omega)\ge-U\frac{1-\theta}{\theta}.
\tag{CM}
\]

In the current LI composition `U=1+2=3`. The distribution may depend on `N`, but a
single `theta` must work at every horizon. Compatibility is retrospective, not merely
per-date. Coverage is required over payoff profiles, not syntactically distinct
worlds. The projection premise is market-theoretic; the weighted-sum conclusion is
finite convex algebra.

## 2. Covered compatibility and covered underwriting

For finite profiles define the trimmed settlement hull

\[
C_\theta(\Omega)=\left\{\sum_\omega\mu_\omega S(\omega):
\mu_\omega\ge\theta,\ \sum_\omega\mu_\omega=1\right\}.
\]

`K cap C_theta(Omega) != empty` is **covered compatibility**. For accumulated
projection inventory the correct certificate is

\[
C_\theta(\Omega_N)\cap\bigcap_{k\le N}K_k\ne\varnothing,
\tag{CC-N}
\]

with the obvious restriction maps when historical fragments differ. A witness of
`(CC-N)` **underwrites** the accumulated exercise because its expectation functional
is nonnegative on every contributing projection trade.

The distinction is useful:

- covered compatibility is geometry;
- covered underwriting is the resulting potential inequality for the actual
  cumulative portfolio;
- bounded liability is the outcome property.

Common covered compatibility is a strong, checkable certificate of bounded liability,
not its definition and not a necessary condition.

## 3. Liability regimes

The useful taxonomy is certificate-based rather than falsely exhaustive.

1. **World-compatible authority.** Every assessed profile is admitted. Projection
   value is pointwise nonnegative and liability is zero.
2. **Exposure-bounded authority.** Authority trades only finitely or has summable
   gross inventory. Liability may be bounded without any compatible potential.
3. **Common-underwritten authority.** One covered potential supports all accumulated
   interventions. Liability is bounded by `(CM)` and may be nonzero.
4. **Drift-underwritten authority.** Supporting potentials change, but their switching
   debt is bounded. `CONTROLLED_DRIFT.md` gives an exact sufficient theorem.
5. **Unsupported shifting authority.** No common or bounded-debt potential is known.
   This does not logically imply loss—opposition may never arrive—but PR50 shows that
   repeated refinancing can make liability unbounded.

The earlier A--D taxonomy survives after adding exposure-bounded schedules and
changing “uncontrolled” from a conclusion of insolvency to absence of a safety
certificate.

## 4. Three sources of failure

- **Synchronic incompatibility:** current jointly operative rows have no covered
  compatible assessment.
- **Diachronic incompatibility:** each era is covered, but accumulated interventions
  have no common or bounded-debt supporting potential.
- **Settlement mismatch:** the settlement hull is the wrong semantic object for the
  normative comparison.

The third is a diagnosis of why the first may occur, not a disjoint convex category.
An inactive authority can exhibit any compatibility failure without incurring loss.

## 5. What liability means

Liability measures sustainable leverage against the possibilities on which authority
is assessed. It does not establish truth, moral correctness, grounded authorization,
fair service, or Progress. A wrong demand can be cheaply underwritten; a correct
demand can be expensive under a mismatched descriptive settlement.

The paper-level statement supported here is:

> Normative authority may reject individual assessed possibilities, but sustained
> intervention needs an underwriting relation between its joint demands and the
> possibilities against which its liability is assessed. One sufficiently covered
> common potential bounds liability. Revision without a common potential is safe
> only to the extent that switching potentials incurs bounded debt.


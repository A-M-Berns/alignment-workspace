# Joint margin, common mixtures, and recycling

## 1. What the one-coordinate margin is doing

PR50's direct mechanism is flow-based. For one undecided binary security and a fixed
interior interval `K=[lo,hi]`:

1. deductive containment keeps both billing/throttling worlds live;
2. a short acquired at price at most `hi` loses at least `1-hi` at the true world;
3. the Budgeter floor converts a finite war chest `B` into a finite total short
   inventory, at scale `B/(1-hi)`;
4. the authority loses at most `hi` per absorbed share at the false world;
5. MarketMaker error adds a summable allowance;
6. no cross-coordinate subsidy ensures authority losses elsewhere do not refill the
   same component at its throttling world.

This yields PR50's model-supported geometry `B*hi/(1-hi)+allowance` against short
flow, with the symmetric ratio against long flow. Near a vertex, the throttling loss
per opposing share vanishes and the conversion costs inverse margin. Settlement can
remove the throttling world and vindicate the opponent; moving disjoint regions can
pay world-uniform cash and recharge it.

The raw intensity `lambda=rho/delta^2` never appears in this realized-flow bound.

## 2. Binary margin versus mixture coverage

For assessed settlements `{0,1}`, a mixture with mean `c` is uniquely

\[
\mu_c=(1-c,c),\qquad \theta(c)=\min(c,1-c).
\]

For a point peg `K={c}`, PR50's two-sided plausibility margin is exactly
`theta(c)`. Therefore `K={1/2}` has coverage `1/2`, while `K={epsilon}` has coverage
`epsilon` and any worst-world bound obtained from coverage scales as `1/epsilon`.
The analogy in the dispatch is real for point pegs.

For an interval it is not an equality. In PR50's strict-interior binary regime,

\[
m(K)=\min(lo,1-hi),
\qquad
\theta^*(K)=\max_{c\in K}\min(c,1-c)
=\frac12-\operatorname{dist}(1/2,K).
\]

Thus `theta^*(K)>=m(K)`, often strictly. For `[2/5,3/5]`, `m=2/5` but
`theta^*=1/2`. The direct PR50 margin controls every location in the peg and gives a
flow-specific far/near ratio; mixture coverage selects one compatible barycenter and
controls aggregate authority liability. Neither numerical quantity replaces the
other outside the point case.

## 3. Common-Mixture Affordability

The following theorem is new in this pass, but its ingredients are already proved in
the workspace.

> **Common-Mixture Affordability Theorem.** Fix a horizon `N`. Let `F` be the
> ordinary realized TradingFirm, `E` an added projection authority, and `A=F+E` the
> aggregate priced by the MarketMaker. Suppose:
>
> 1. `A_{<=N}(omega)<=C` at every relevant live assessed world;
> 2. `F_{<=N}(omega)>=-B_F` there;
> 3. a distribution `mu_N` has full support on the finite relevant authority-payoff
>    profiles, with `mu_N(omega)>=theta>0`;
> 4. its barycenter valuation is admitted by every projection region used through
>    `N`.
>
> Then, for every relevant live world,
>
> \[
> E_{\le N}(\omega)
> \ge
> -\frac{1-\theta}{\theta}(C+B_F).
> \tag{CM}
> \]

If the hypotheses hold uniformly at every horizon, the authority has uniformly
bounded assessed liability. In the current generalized LI construction, `C=1` and
`B_F=2`, so

\[
E_{\le N}(\omega)\ge-3\frac{1-\theta}{\theta}.
\tag{CM-LI}
\]

### Proof

Write `U=C+B_F`. From `A=F+E`, the MarketMaker upper cap and firm floor give

\[
E_{\le N}(\omega)=A_{\le N}(\omega)-F_{\le N}(\omega)\le U
\tag{4}
\]

at every live support world. Projection has nonnegative value at the barycenter on
every date, so by linearity

\[
0\le E_{\le N}(\bar S_{\mu_N})
=\sum_\nu\mu_N(\nu)E_{\le N}(\nu).
\tag{5}
\]

For a fixed `omega`, bound every other term in `(5)` above by `U`:

\[
0\le \mu_N(\omega)E_{\le N}(\omega)
 +(1-\mu_N(\omega))U.
\]

Division by `mu_N(omega)>=theta` proves `(CM)`. No fixed-point flow identity, raw
intensity, tolerance, dimension factor, or separation of ordinary trader accounts is
used. Dimension enters only through how small an achievable coverage `theta` becomes.

The constant is sharp under these abstract hypotheses: with one world of mass
`theta` at value `-U(1-theta)/theta` and all remaining mass at value `U`, the mixture
value is zero.

### Exact composition with current Lean results

- `(5)` is `ProjectionBudget.cumValue_nonneg_of_forall_mem` at the fractional
  barycenter plus linearity of `Strategy.value`/`cumValue`.
- `(4)` uses `EnforcementPreservation.realizedAggregate_netWorth`,
  `marketMaker_netWorth_lt_one`,
  `AssessmentFirm.tradingFirmTrader_netWorth_floor`, and
  `tradingFirmTrader_quote_eq_realizedFirm`.
- `(CM-LI)` supplies the `hliab` argument to
  `EnforcementPreservation.no_efficient_trader_exploits`.

The only unformalized step is the finite weighted-sum packaging. The mathematical
argument does not depend on PR50's model-supported C0.

### What “full support” means

For a fixed finite episode fragment, quotient live worlds by equality of all authority
payoffs through `N`. It is enough to cover these finitely many profiles: authority net
worth is identical within a class. Representatives must be live so the TradingFirm
floor applies. A fixed lower bound `theta` implies at most `1/theta` relevant profiles;
for `d` independent binary coordinates the naive uniform value can be `2^{-d}`.

The strongest moving-region form is retrospective: at every horizon `N`, one covered
mixture barycenter must lie in every `K_k`, `k<=N`. A single fixed mixture compatible
with every region is an easy sufficient condition. Stationary fixed-episode regions
are the primary application.

## 4. The PR50 pump is the critical negative test

PR50's exact witness has all four binary worlds live and enforces

\[
K_n=[2/5,3/5]\times
\begin{cases}
[1/10,1/5],&\text{low era},\\
[4/5,9/10],&\text{high era}.
\end{cases}
\]

Each era separately has a full-support compatible product mixture. Taking phi mean
`1/2` and psi mean `3/20` or `17/20` gives minimum world mass `3/40` in either era.
But one distribution has one fixed psi expectation, and

\[
[1/10,1/5]\cap[4/5,9/10]=\varnothing.
\]

Therefore:

1. each coordinate/era separately is well covered;
2. each joint region separately has a covered compatible mixture;
3. no single mixture is compatible through the attack;
4. the failure recurs at every band switch;
5. the common-mixture theorem does not predict bounded liability.

This explains the pump by one clean failure: **temporal common compatibility**, not
mere dimension two. The fixed phi peg and each individual psi era are harmless; the
disjoint repeated psi requirements destroy the global potential and pay the attacker
world-uniform cash.

## 5. Geometric comparison map

Let `C=conv S(Omega)` and, for prescribed `theta`, let

\[
C_\theta=\left\{\sum_\omega\mu(\omega)S(\omega):
\mu(\omega)\ge\theta,\ \sum\mu=1\right\}.
\]

For finite `Omega`:

```text
K intersects C_theta
        => one theta-covered compatible mixture
        => full-support compatible mixture
        => K intersects C

full-support compatible mixture
        <=> K intersects relint(C)
            (for the listed finite settlement generators)

homothetic core + compatible anchor
        => full-support compatible mixture

common mixture  -/-> homothetic core
homothetic core -/-> common mixture without a compatible anchor
ambient Slater interior -/-> settlement compatibility
settlement compatibility -/-> ambient Slater interior
```

Exact separations:

- `K={0}` with binary settlements intersects `C` but has no full-support mixture.
- `K_n={1/n}` has full support per date but no uniform coverage over the schedule.
- `K={1/2}` has a maximally covered mixture but no positive homothetic core relative
  to both binary worlds.
- In two dimensions, let live settlements be `(0,0),(1,0)`, anchor
  `c=(1/2,1)`, and let `K` contain `c` and the alpha-scaled copies of the live
  segment toward `c`. This has an `alpha`-core but is disjoint from the settlement
  convex hull.
- A full-dimensional ball or box can be disjoint from `C`; ambient Slater interior
  says nothing about compatibility.
- A singleton barycenter in `relint(C)` is compatible but has empty ambient interior.

The condition relevant to liability is therefore a **covered relative compatibility
margin**, not ambient interior and not a homothetic core.

## 6. A bounded-recycling closure lemma

Common compatibility is `kappa=0` in a more general algebra. Let

\[
L_N=\max_\omega(-E_{\le N}(\omega))_+,
\qquad
\Lambda_N=\sum_\omega\mu(\omega)E_{\le N}(\omega),
\]

and retain the pointwise upper bound `E_{<=N}(omega)<=U`. Suppose a schedule-level
certificate, quantified over every allowed market run, proves

\[
\Lambda_N\ge-S-\kappa L_N
\tag{6}
\]

for constants `S<infinity` and `kappa<theta`, where `mu(omega)>=theta`.
At a worst world,

\[
\Lambda_N\le-\theta L_N+(1-\theta)U.
\]

Combining with `(6)` yields the exact closure

\[
\boxed{
L_N\le\frac{S+(1-\theta)U}{\theta-\kappa}.}
\tag{RC}
\]

If `r=kappa/theta`, this is
`[S+(1-theta)U]/[theta(1-r)]`. This resolves the two candidate denominators:
the unnormalized threshold is `kappa<theta`; the normalized threshold is `r<1`.

Common compatibility gives `S=kappa=0`. In the PR50 pump, unbounded `L_N` with fixed
`U` implies that no uniform certificate `(6)` with `kappa<theta` can hold for any
chosen covered potential. This locates the threshold abstractly, but it does not yet
derive a computable `kappa` from arbitrary moving polytope geometry. That derivation
remains open.

## 7. Moving regions

- **One fixed covered mixture in every `K_n`:** theorem proved; arbitrary motion is
  allowed because the authority never loses in the common potential.
- **Horizon-wise mixtures whose barycenters lie in every past `K_k`:** theorem proved;
  this is the exact retrospective generalization.
- **Per-date mixtures with uniform coverage:** insufficient; PR50's pump is the
  counterexample.
- **Summable mixture variation or set-gap motion:** plausible only with an additional
  bound on potential-switching cost or authority turnover. PR50 supplies model
  evidence for its one-dimensional set-gap case, not a general theorem.
- **Fresh successor accounts:** do not remove historical authority loss and do not
  repair `(BL)`.


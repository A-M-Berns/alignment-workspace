# Sufficient factorizations

Each route below ends at the same `PracticalCert`.  The first uses scalar
counterfactual values.  The second uses only adequate response sets and bounded
anchored loss.  Neither is the definition of practical semantics.

## 1. Generic proxy composition

Suppose an external theory supplies a nonnegative proxy `g`, constants
`C,L,epsilon_0,epsilon_resp >= 0`, and

\[
 |g(b_s)-g(u_s)|\le C d_s,\qquad g(u_s)\le\epsilon_0,
 \qquad \Lambda_{es}(\Pi_s)\le Lg(b_s)+\epsilon^{resp}.
\]

Then

\[
 \Lambda_{es}(\Pi_s)
 \le (LC)d_s+(L\epsilon_0+\epsilon^{resp}).
\]

Thus `M_es=LC` and
`epsilon_es=L epsilon_0+epsilon_resp`.  `proxy_route` is Lean-proved.  This is an
algebraic normal form, not a substantive semantics: every direct affine certificate
can be put in it artificially by taking `g(b)=M d+epsilon`, `L=1`, `C=M`,
`epsilon_0=epsilon`, and `epsilon_resp=0`.

## 2. Value-correspondence route

For a finite policy menu, the landed realization supplies:

1. authenticated values `v*_{es}` and a region witness whose directed ambiguity is
   `zeta_es`;
2. displayed values calibrated to the authenticated values within
   `d_s+zeta_es`;
3. a distribution `Pi_s` with displayed suboptimality at most `eta_s`; and
4. anchored response adequacy

\[
 \Lambda_{es}(\Pi_s)\le L_{es}\operatorname{Regret}_{v^*}(\Pi_s)
   +\epsilon^{resp}_{es}.
\]

The landed randomized transfer and response composition give

\[
 \operatorname{Regret}_{v^*}(\Pi_s)le
 2d_s+2\zeta_{es}+\eta_s,
\]

and hence exactly

\[
 \boxed{M_{es}=2L_{es},\quad
 \epsilon_{es}=L_{es}(2\zeta_{es}+\eta_s)
   +\epsilon^{resp}_{es}.}
\]

**External bill (ambient assumption).**  The theory must authenticate the
counterfactual values or directed correspondence; justify the policy interventions;
control evaluator manipulation, interference, and domain transport; certify the
decision rule's displayed suboptimality; and authenticate regret-to-anchored-loss
adequacy.  Logical Induction supplies none of these facts.

**Strict weakening.**  Two-sided calibration at every policy is sufficient but not
needed for the regret algebra.  It suffices that the displayed score does not
underestimate one authenticated best response by more than `r` and does not
overestimate responses in the realized distribution's support by more than `r`.
`one_sided_randomized_argmax_transfer` proves the resulting `2r+eta` bound.  The exact
fixture underestimates a nonoptimal policy by `1/2` while its one-sided radius is
`1/10`.  Likewise, membership `v* in V` is not used once directed ambiguity is
supplied.

This route is natural for utility-like domains with meaningful comparable policy
values.  Rights-like or procedural requirements may make its response-adequacy
constant absorb the whole loss range, even when a direct certificate is sharp.

## 3. Adequate-set route: no scalar value vector

Let `Q_s` be a finite response menu, `A_es subseteq Q_s` the responses certified
adequate for exposure `e`, and `lambda_es(q)` its anchored loss.  Suppose

\[
 0\le\lambda_{es}(q)\le D_{es}\quad(q\in Q_s),\qquad
 \lambda_{es}(q)\le\epsilon^{ad}_{es}\quad(q\in A_{es}),
\]

and the external response controller proves the defect-to-failure-mass coupling

\[
 \Pi_s(Q_s\setminus A_{es})
 \le \kappa_{es}d_s+\theta_{es}.
\]

Splitting the expectation over `A_es` and its complement gives

\[
 \Lambda_{es}(\Pi_s)
 \le \epsilon^{ad}_{es}+D_{es}(\kappa_{es}d_s+\theta_{es}).
\]

Therefore

\[
 \boxed{M_{es}=D_{es}\kappa_{es},\quad
 \epsilon_{es}=\epsilon^{ad}_{es}+D_{es}\theta_{es}.}
\]

`adequate_set_route` is Lean-proved for finite menus and has an exact rational
inhabitation witness.  The route applies directly to:

- a receipt obligation, where `A_es` consists of responses carrying a valid receipt
  of kind `X` by horizon `H`;
- a prohibition, where `A_es` excludes every response containing a forbidden action;
- a constraint bundle, where adequacy is proof-carrying membership in a declared
  feasible response relation.

No ranking among adequate responses is required.

**External bill (ambient assumption).**  The theory must authenticate `A_es` against
the immutable exposure, certify the bound on anchored loss, and prove the coupling
between the operative market defect and mass outside `A_es` for the realized response
controller.  It must also prove joint coupling against the same `Pi_s` when several
edges share `s`.

## 4. Relation between the routes

Both routes instantiate proxy composition, but they need not yield ordered constants.
The exact crossing fixture gives value-route constants `(M,epsilon)=(2,1)` and
adequate-set constants `(10,0)`: the adequate-set bound is smaller for `d<1/8`, the
value bound is smaller for `d>1/8`.  This is not a theorem that either semantics is
more accurate; it shows there is no uniform constant-wise dominance.

The adequate-set route is one non-scalar sufficient realization, not a claim that all
procedural or rights-like obligations reduce naturally to a finite set.  Infinite and
history-dependent response predicates require their own measurability and causal
semantics while retaining the same public endpoint.

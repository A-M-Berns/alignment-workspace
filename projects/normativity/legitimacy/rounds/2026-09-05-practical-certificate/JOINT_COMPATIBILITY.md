# Joint practical-response compatibility

## 1. Weakest useful condition

Let `E_s={e:T(e,s)>0}`.  One service occurrence has one response-distribution receipt
`Pi_s`; there is not a separately chosen `Pi_es` for every edge.

**`JointPracticalAdequacy` (provisional definition/interface).**

```text
JointPracticalAdequacy(s, E_s, Pi_s) :⇔
  for every e in E_s,
    Lambda_es(Pi_s) <= M_es * d_s + epsilon_es.
```

Equivalently, the transport support condition is

```text
T(e,s) > 0  ⇒  Admissible(e,s,responseReceipt(s)),
```

where `Admissible` checks `PracticalCert` against the receipt identifying the single
actual `Pi_s`.  This edge-level formulation is the weakest one the Progress summation
can use.  A bundle-level certificate is a compact witness for all such checks.  Merely
proving `for every e, exists Pi_e` is insufficient.

Before a response is chosen, feasibility of a bundle means existence of one `Pi` in
the adapter's permitted response class satisfying all edge bounds at the same quote.
The adapter must then realize that witness (or another jointly certifying response).
At zero defect, and when the adapter must certify every quote including a region point,
`bundle_certifiable_iff_zero_defect_adequate` Lean-proves:

\[
 \exists\Pi(\cdot)\ \forall e,b,\
 \Lambda_e(\Pi(b))\le M_e d(b)+\epsilon_e
 \quad\Longleftrightarrow\quad
 \exists\Pi\ \forall e,\ \Lambda_e(\Pi)\le\epsilon_e,
\]

assuming `M_e,d(b)>=0` and some `b_0` has `d(b_0)=0`.  The reverse direction uses a
constant adapter.  This characterizes a uniform adapter contract, not merely one
observed service occurrence.

## 2. Exact separation from price-space feasibility

Take a feasible price region with two independent coordinates fixed at one:

\[
 K_s=\{(1,1)\}\subseteq[0,1]^2.
\]

Let the response menu be `{a,b,c}`.  Exposure `e1` has losses `(0,1,1)` and exposure
`e2` has losses `(1,0,1)`.  Thus `A_1={a}` and `A_2={b}`.  Each edge separately has a
zero-loss response, while no common distribution has zero loss on both.  Indeed, for
every distribution `Pi`,

\[
 \Lambda_1(\Pi)+\Lambda_2(\Pi)\ge1,
\]

so at least one loss is `>=1/2`.  The half mixture on `a,b` attains `1/2` on both.
`disjoint_adequate_sets_force_loss` is the Lean lower bound; Python checks the feasible
region, individual certificates, a Farkas dual witness for every common tolerance
`<1/2`, and attainment at `1/2`.

Therefore joint price-space feasibility neither entails nor is entailed by practical
compatibility.  A second fixture has an empty price box but two identical practical
demands with a common zero-loss response.

## 3. Legitimate outcomes of incompatibility

### Distinct service contexts

Create distinct service identities `s1,s2`, each with its own strict-prefix context,
defect, intensity, response receipt, and transport column.  Record `(e1,s1)` and
`(e2,s2)` only if each edge certifies against `Pi_s1` and `Pi_s2`, respectively.  The
plan may not present these as two edges in one column, because column amplification and
response semantics are occurrence-indexed.

### Licensed adjudication or aggregation

An upstream rule may authorize one aggregate answer specification or priority result.
The service receipt records the rule, its licence, the input exposure identities, and
the resulting response specification.  An old edge `(e,s)` remains in transport only
if an authenticated semantic-transport certificate bounds the chosen response's loss
against that old immutable anchor.  A rule that disposes of or replaces an obligation
must produce the corresponding licensed history transition; absent such a transition
and an edge certificate, that exposure remains residual.  Aggregation authority does
not itself prove practical adequacy.

### Common adequate response

Record the single response receipt once and attach every supported edge certificate to
that receipt.  Determinism is unnecessary: the exact fixture's half mixture achieves a
common tolerance no deterministic response achieves.  Every edge keeps its own
`M_es,epsilon_es`; the column condition sums `T(e,s)M_es`.

### Residual mass

Omit uncertified edges from `supp(T)`.  Their evaluation mass contributes to

\[
 r_N=1-\sum_{e,s}T(e,s)
\]

and is charged at `D r_N`.  The exact accounting fixture matches only `e1` to response
`a` and leaves `e2` residual; both realized loss and claimed bound are `1/2`.  Falsely
matching both claims a zero bound while realizing loss `1/2`.

## 4. Useful sufficient and refutation certificates

For adequate sets, the direct sufficient condition is a common distribution with
`Pi(Q\A_e)<=theta_e` for every matched exposure.  A necessary intersection test says
that every subset `S` with `sum_{e in S}theta_e<1` must have nonempty common adequate
set.  `union_bound_two` Lean-proves the two-set mass inequality.  This test is not
sufficient: three disjoint singleton sets with every `theta_e=1/2` pass all strict
subset intersection demands but require total adequate mass at least `3/2`.

For finite menus, nonnegative exposure weights `w_e` give an exact Farkas-style
infeasibility witness whenever

\[
 \max_q\sum_{e:q\in A_e}w_e
 <\sum_e w_e(1-\theta_e).
\]

The checker evaluates this inequality with exact rationals.  It is a sufficient
refutation certificate, not claimed complete here.

# Necessity and rejected strengthenings

## 1. Clauses retained by the public endpoint

### Same realized response

This is load-bearing.  In the two-exposure fixture, `delta_a` certifies `e1` with zero
loss and `delta_b` certifies `e2` with zero loss.  Charging both edges to occurrence
`s` while citing their separate witnesses claims zero, but the actual `delta_a` response
incurs loss one on `e2`.  At transport mass `1/2` per edge, realized matched loss is
`1/2` and the claimed bound is zero.

### Immutable exposure anchor and evaluation protocol

This is load-bearing for meaning, although not derivable from arithmetic.  The same
numeric response `delta_a` has loss zero under the `e1` anchor and loss one under the
`e2` anchor.  An unindexed certificate can therefore be made true by evaluating the
wrong specification.  The external theory must authenticate the anchor and response
map; the direct inequality only consumes their result.

### Edge-specific constants

This is load-bearing.  Factorizations can produce different `M_es` and
`epsilon_es` for the same service occurrence.  The Progress column uses
`sum_e T(e,s)M_es` and the error uses `sum_{e,s}T(e,s)epsilon_es`; replacing them by an
uncertified shared constant understates one edge unless a separate domination proof is
provided.

### Defect coupling or additive slack

Some control is load-bearing for a nonvacuous conclusion.  In the adequate-set route,
if mass outside `A_e` is not bounded by `kappa*d+theta`, zero defect is compatible with
unit anchored loss.  If off-set loss has no finite bound, arbitrarily small failure
mass can carry arbitrarily large expected loss.  If responses called adequate are not
bounded by `epsilon_ad`, unit mass on `A_e` can itself have arbitrary loss.  Exact tests
instantiate all three failures.

Nonnegativity of `M` and `epsilon` is not needed to sum a certificate at one fixed
occurrence.  It is retained by the wider contract so worsening nonnegative defect
cannot improve the bound, `Gamma_N` is an amplification bound, and zero-defect
compatibility reduces to the additive tolerance.

## 2. Strengthenings not required

### Scalar counterfactual values

Not required.  `adequate_set_route` derives the public constants from a bounded loss
predicate and off-adequate mass.  The forbidden-action fixture gives a sharp
`(M,epsilon)=(1,0)` adequate-set certificate while every regret-dominance value route
with the forbidden action declared uniquely value-optimal requires
`epsilon_resp>=D=1`, regardless of `L`.

### Value soundness as membership

Not required by the algebra.  Directed ambiguity relative to the authenticated target
is sufficient.  The exact interval fixture has `V=[2/5,3/5]`, `v*=7/10` outside `V`,
and directed radius `zeta=3/10`; nevertheless
`|b-v*|<=dist(b,V)+zeta` holds and is tight.  This does not authenticate `v*`; it shows
that membership is one sufficient source of the bound, not a used premise.

### Two-sided uniform calibration

Not required for approximate argmax transfer.  Only an upper error bound at one true
best response and a lower error bound on responses in the realized support are used.
`one_sided_argmax_transfer` and its randomized form are Lean-proved.  The exact fixture
has two-sided radius `1/2` but one-sided radius `1/10`.

### Deterministic response

Not required.  With disjoint zero-loss responses for two exposures, every deterministic
response has loss one on at least one edge, while the half mixture has loss `1/2` on
both.  The public object is the realized distribution.

### Zero-loss common response

Not required when additive errors are permitted.  Joint compatibility asks for the
edge-specific affine tolerances, not intersection of zero-loss sets.  The half-mixture
fixture is jointly compatible for `epsilon_1=epsilon_2=1/2` and incompatible for any
common tolerance below `1/2`.

### Region feasibility, convex response geometry, or a universal response ontology

None is required by `PracticalCert`.  The exact fixtures separate price-box feasibility
from practical compatibility in both directions.  Convexity is useful for the market
enforcer; response semantics may be procedural, rights-like, discrete, or
history-dependent.

### A certificate uniform in every possible quote

Not required by the final matched-loss sum, which consumes the actual service receipt.
A pre-response plugin should normally prove a conditional/uniform theorem to prevent
post-selection.  That is audit strength, not a further term in the endpoint.

### Edge localization among all possible theorem designs

An aggregate certificate bounding the complete transported loss would be weaker than
requiring every supported edge to certify separately.  The existing theorem uses
edge-local certificates because they make admissibility auditable, allow column
amplification, and expose residual mass.  This round's minimality claim is relative to
that public design; it does not rule out replacing the design with one opaque global
semantic premise.

## 3. Limits of the counterexamples

Finite fixtures establish exact separations only.  They do not show that value
semantics is unsuitable for every rights-like domain, that the adequate-set route is
minimal among realizations, or that the Farkas witness implemented here is a complete
infeasibility calculus.

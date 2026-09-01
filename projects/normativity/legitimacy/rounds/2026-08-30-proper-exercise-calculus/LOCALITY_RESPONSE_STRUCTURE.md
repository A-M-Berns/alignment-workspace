# Locality must preserve response structure

## The new counterexample to `(BL)`

PR71's follow-up protected realized residual behavior with

\[
p_R(\alpha(q,r)\star e)=p_R(\alpha(q',r)\star e). \tag{BL}
\]

This is sound as an optional *realized-behavior invariance* certificate, but too strong as
the definition of residual-agent locality.  Let the unchanged residual rule be
\(r:Y\to D\).  Query \(q_0\) yields receipt 0 and hence action \(r(0)=a_0\); query
\(q_1\) yields receipt 1 and action \(r(1)=a_1\).  The inquiry subsystem alone changed,
yet a projection observing the downstream action makes `(BL)` fail.

The invariant should normally be the contingent response structure, not its one realized
trace.  This mirrors the earlier exterior result: hold an opponent or predictor strategy
fixed, not its realized response.

## Minimal certificate

Plain Cartesian-frame data \(A\times E\to\Omega\) does not expose “feed every possible
receipt to the continuation.”  The modeler must supply:

* a receipt interface \(Y\);
* a downstream continuation type \(D\);
* authenticated residual semantics \(\kappa:R\to(Y\to D)\), or an extensional
  equivalence class of such rules;
* a realization certificate that every \(\alpha(q,r)\) invokes the same
  \(\kappa(r)\) after its receipt, for all admitted \(q\).

Equivalently, if the model supplies a counterfactual feeding operation, two residuals
are extensionally equal when their non-inquiry continuations agree for every receipt and
admissible exterior continuation.  Without the receipt intervention coordinate, CF
cannot prove this fact by itself.  No full decision-process formalism is needed.

## Locality hierarchy

1. **Exterior strategy fixed:** `epsilon(z)` is independent of `q`.
2. **Residual response structure fixed:** authenticated `kappa(r)` is independent of
   `q`.
3. **Realized residual behavior fixed:** `(BL)` holds for the chosen observation.
4. **Inquiry-local semantics:** the varied coordinate is contract-certified as inquiry,
   with the required target/applicability conditions.

The first does not imply the second: `(CFP)` admits whole-agent replacement.  The second
does not imply the third: an unchanged rule can react differently to different receipts.
The third does not imply the second: two latent rules may agree at the actual receipt and
differ off-path.  None of the first three alone implies the fourth: `q` may be cosmetic,
target-manipulating, or simply mislabeled.  With a fixed receipt and compatible
observables, response-structure equality does imply equal realized downstream action;
the unconditional implication is false.

Predictor dependence is compatible with the hierarchy: the fixed exterior object is its
strategy table even though its realized output varies with `q`.  Self-modification may
change the response-rule type, in which case equality is ill-typed and PE must certify a
translation between the old and new rule interfaces.

## Where the certificate belongs

Keep `(CFP)` as the thin exterior-fixed patch certificate.  Attach a typed response-
structure certificate when route adequacy or a revision argument relies on locality.
When a revision claims to replace *only* inquiry, `PE^locality` should transport the
residual response policy across the transition.  Requiring strong `(BL)` in every patch
would reject legitimate information-dependent behavior; requiring no locality witness
would reinstate whole-agent replacement.

Thus CF supplies the counterfactual decomposition.  The receipt semantics and invariant
are modeler-supplied, and PE authenticates their preservation when normatively material.

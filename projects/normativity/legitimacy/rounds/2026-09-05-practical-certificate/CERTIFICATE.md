# Minimal practical-semantics certificate

## 1. Public endpoint

Fix an exposure `e` with immutable anchored response space `(Y_e, ell_e)`, and a
service occurrence `s`.  Let `Pi_s` be the one response distribution actually
realized at `s`.  The external practical semantics supplies the induced anchored
loss functional

\[
  \Lambda_{es}(\Pi):=
  \mathbb E_{q\sim\Pi,\,y\sim\rho_{es}(q)}\ell_e(y).
\]

The expectation is one realization.  The theorem-facing object may instead take
`Lambda_es` as a certified bounded functional on response distributions; neither a
finite response menu nor a scalar utility representation is public structure.

**`PracticalCert` (provisional definition/interface).**

```text
PracticalCert(e, s, Pi_s; M_es, epsilon_es) :⇔
  Lambda_es(Pi_s) <= M_es * d_s + epsilon_es.
```

Here `d_s` is the realization round's public operative defect,
`dist_infinity(b_s,K_s)`.  The constants are exactly the abstract contract's
`M_es` and `epsilon_es`; they are not additional error terms.  The wider Progress
contract takes `d_s,M_es,epsilon_es >= 0`, `ell_e in [0,D]`, and nonnegative
transport mass.  Only the displayed inequality is used in the matched-loss
summation.

The certificate is indexed by the immutable exposure, service occurrence, and
realized response receipt.  Its metadata fixes before response evaluation:

1. the exposure anchor and `ell_e` (or its authenticated identifier);
2. the declared evaluation worlds/randomness and the causal response map into `Y_e`;
3. the service occurrence and response-distribution receipt;
4. `d_s`, `M_es`, and `epsilon_es`;
5. the authentication/provenance evidence required by the history interface.

Those fields prevent a numerically true inequality from being reassigned to another
exposure, response, or evaluation protocol.  Their authenticity is an external
semantic premise; the inequality does not prove it.

If the external claim ranges over a declared family of live evaluation worlds, it
must supply the inequality uniformly over that family or define `Lambda_es` as the
committed aggregate/worst-case functional.  The abstract theorem does not choose the
family or aggregation.

## 2. Exact role in Progress

For nonnegative transport weights `T(e,s)` supported only on certified edges,

\[
 \sum_{e,s}T(e,s)\Lambda_{es}(\Pi_s)
 \le
 \sum_{e,s}T(e,s)M_{es}d_s+
 \sum_{e,s}T(e,s)\epsilon_{es}.
\]

The realization round's column-amplification condition then controls the first sum;
its `bar epsilon_N` is the second sum.  Unmatched mass is charged through `D r_N`.
No value vector, counterfactual-identification method, optimizer, adequate set, or
convex response model appears in this use.

A single aggregate inequality for the whole transport plan would be logically weaker
than edgewise certificates, but would discard the current contract's local admissible-
edge audit and compositional column accounting.  `PracticalCert` is minimal within that
edge-local public interface, not among all possible redesigns of Progress.

## 3. External bill

An external practical-semantics theory must certify:

- that `Lambda_es` measures the response against the immutable `Spec_e`, rather than
  a later substitute;
- that the map from the response at `s` to `Y_e` has the declared causal and
  evaluation meaning;
- that its boundedness/integrability is sufficient for the public loss and residual
  bound; and
- the affine inequality for the actual `Pi_s`, or a pre-response theorem that implies
  it for every permitted realization.

The generic Normative Induction layer checks and composes this evidence.  It does not
derive any of these semantic facts from market conformance.

## 4. Pointwise versus adapter-level claims

The final Progress inequality consumes pointwise certificates attached to recorded
edges.  A deployable plugin normally proves the stronger conditional statement

```text
for every permitted strict-prefix state b and every declared live evaluation world,
  PracticalCert(e, s, Adapter_s(b); M_es, epsilon_es).
```

This uniform statement blocks post-selection of constants or evidence.  It is a
realization/audit obligation, not extra algebra in the public Progress theorem.

## Provenance

The public endpoint and constants are read from
`projects/normativity/legitimacy/rounds/2026-09-04-normative-inductor-realization/`
`NORMATIVE_INDUCTOR_REALIZATION.md` §§3, 6, 13 and
`PRESENTATION_AND_VALUE_SEMANTICS.md` §§5–8.  The reduction to the direct inequality
is paper-derived from the displayed matched-loss summation.  Lean proves only the
factorization algebra listed in `THEOREMS.md`.

# Faithful authentication

## Soundness does not imply adequacy

Authentication soundness says a checker asserts only true equations relative
to its supplied denotation. A constant or coarse denotation can satisfy that
condition while forgetting every distinction relevant to inherited
answerability. Join preservation and bottom preservation do not prevent this.

For slice \(\alpha\) in era \(n\), supply:

- admissible carrier representations \(D_{n,\alpha}\subseteq L_n\);
- an anchored answerability preorder \(\preceq_\alpha\) on those
  representations;
- equivalence \(x\equiv_\alpha y\) iff both \(x\preceq_\alpha y\) and
  \(y\preceq_\alpha x\);
- an authenticated denotation \(\iota_{n,\alpha}\) into the stable slice
  domain.

The current evaluator does not choose these relations unilaterally. They are
anchored protocol/model data or outputs of a named domain checker whose
soundness and adequacy are seed assumptions.

## Weakest useful conditions

For exact translation, equality reflection on admissible representations is
enough:

\[
\iota(x)=\iota(y)\Longrightarrow x\equiv_\alpha y.
\tag{ER}
\]

For the stronger weakening/strengthening classification, order reflection is
required:

\[
\iota(x)\le\iota(y)\Longrightarrow x\preceq_\alpha y.
\tag{OR}
\]

Order reflection implies equality reflection. The reusable adequacy condition
is therefore that the induced map

\[
D_{n,\alpha}/{\equiv_\alpha}\longrightarrow L_\alpha
\]

is an order embedding. Full injectivity on \(L_n\) is too strong: typography,
implementation details, and other slice-irrelevant distinctions may collapse.
Restriction to \(D_{n,\alpha}\) avoids freezing representations that cannot
carry this slice.

This definition is independently testable once the domain supplies its
relevance preorder; it is not “whatever makes conservation true.”

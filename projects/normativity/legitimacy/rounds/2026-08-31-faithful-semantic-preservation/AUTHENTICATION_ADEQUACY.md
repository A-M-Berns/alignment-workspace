# Authentication correctness and adequacy

Use two judgments.

\[
AuthSound(\xi)
\]

means validated certificates do not assert false equations in the declared
semantic model.

\[
AuthAdequate_\alpha(D,\preceq_\alpha,\iota)
\]

means that model reflects the answerability preorder on admissible
slice-carrier representations. A sound constant observation fails adequacy. A
coarse quotient is adequate exactly when every collapsed distinction is
\(\alpha\)-irrelevant.

## Lossy-map attacks

Let \(\iota(a)=A\), \(\iota(b)=0\). Then join preservation gives

\[
\iota(a\vee b)=A=\iota(a).
\]

The same commuting equation can hide strengthening \(a\mapsto a\vee b\) or
weakening \(a\vee b\mapsto a\). If \(b\) is relevant, equality and order
reflection fail. If \(b\) is explicitly irrelevant modulo
\(\equiv_\alpha\), the collapse is harmless for this slice.

Semantic correctness is therefore model-relative; adequacy says the model has
not omitted a distinction the theorem promises to protect. No Semantic
Laundering needs both. Answerability adequacy remains weaker than the
comparison structure required by Progress.

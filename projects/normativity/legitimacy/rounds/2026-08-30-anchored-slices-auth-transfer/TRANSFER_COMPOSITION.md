# Composition of authenticated Transfer

## Exact law

Suppose \(x\) authentically transfers to a finite family \(Y\), and each
\(y\in Y\) authentically transfers to \(Z_y\). Then

\[
x\rightsquigarrow\bigcup_{y\in Y}Z_y
\]

is authenticated when:

1. all steps concern the same anchored slice;
2. the first step's target interpretation is exactly the second step's source
   interpretation, or an authenticated bridge connects them;
3. context and target identifiers are stable or authentically transported;
4. every bridge preserves finite joins and bottom;
5. both local certificates validate.

The proof substitutes each authenticated equality for
\(\llbracket y\rrbracket\) and uses associativity, commutativity, and
idempotence of finite join.

## Why local-looking certificates need not compose

Let an intermediate label \(y\) denote \(a\) in context \(K_1\) but \(b\) in
\(K_2\). The first checker can validate \(x\mapsto y\) relative to \(K_1\), and
the second can validate \(y\mapsto z\) relative to \(K_2\). Without an
authenticated \(K_1\)-to-\(K_2\) bridge, their shared spelling is no semantic
interface and composition is invalid.

## Time-varying local semantic domains

For era-local semilattices \(L_n\), give each slice a stable anchored domain
\(L_\alpha\) and authenticated maps

\[
\iota_{n,\alpha}:L_n\longrightarrow L_\alpha
\]

that preserve finite joins and bottom. Transfer is checked after mapping into
\(L_\alpha\). An ontology translation commutes when

\[
\iota_{n,\alpha}(\llbracket x\rrbracket_n)
=
\iota_{n+1,\alpha}(\llbracket x'\rrbracket_{n+1}).
\]

An arbitrary era-to-era join homomorphism is insufficient: it could map
nonzero inherited content to zero. The stable anchored codomain is what turns a
representation change into preservation rather than evaluator-controlled
forgetting.

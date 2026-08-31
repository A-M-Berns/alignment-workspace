# Semantic authentication

## Accounting is not authentication

Transfer accounting checks an equation in supplied semantic values:

\[
I=s\vee d\vee\bigvee_{q'\in S}\lambda'(q').
\tag{TA}
\]

It proves that no supplied value was lost or invented. It does not prove that a
successor representation actually means the value assigned to it. A censor can
label “ignore criticism \(c\)” with the old value for \(c\); equation (TA)
passes while answerability is laundered.

Semantic authentication is the independent evidence that source and target
representations are related to the historically anchored meaning as claimed.

This is authentication correctness, not by itself authentication adequacy. A
join-preserving denotation can be correct and still collapse a distinction
relevant to the slice. The strong No Semantic Laundering consumer therefore
also requires order reflection on admissible representations modulo an
anchored slice-relative equivalence. The
2026-08-31-faithful-semantic-preservation follow-up makes that interface exact.

## Generic interface

For domain \(\tau\), context \(K\), matter \(m\), and slice \(\alpha\), use a
proof-relevant judgment

\[
AuthTrans^\tau_{K,m,\alpha}(x,Y;\xi).
\]

Its generic soundness projection is

\[
Valid^\tau_K(\xi)\Longrightarrow
\llbracket x\rrbracket_{K,m,\alpha}
=\bigvee_{y\in Y}\llbracket y\rrbracket_{K,m,\alpha}.
\tag{AUTH}
\]

The answerability theorem consumes (AUTH), not the internals of \(\xi\).
Depending on the domain, a certificate can be:

- anchored protocol data;
- a derivation checked in a fixed metalanguage;
- a proof emitted by a domain-specific checker;
- explicitly named external model data or semantic-oracle evidence.

The current evaluator's unsupported declaration is not a certificate. Context
and target parameters are part of the judgment when equivalence is relative.

## Required algebra

Accounting needs a finite join-semilattice with bottom: associative,
commutative, idempotent join and \(0\). The induced order is enough. The theorem
does not use meet, distributivity, complements, or finite atomic decomposition.

Non-atomic content is allowed. “Answer \(a\) in light of \(b\)” may be one
semantic element rather than the join of independent atoms. Idempotence makes
overlapping successor loads harmless for conservation, though the certificate
must still authenticate their allocations.

## Where authentication stops

The theory cannot derive semantic correctness from syntax alone. Its stopping
point is an explicitly fixed metalanguage/model relation or a named checker
whose soundness is a seed assumption. If authentication rules are themselves
revised, the new rules are object-level data and need an authenticated bridge
in that fixed metalanguage.

This is not an infinite certificate tower. It is the ordinary boundary between
a theorem parameterized by a semantics and a proof that a particular semantics
is correct. Seed quality includes the adequacy, amendability, and self-application
rules of that boundary.

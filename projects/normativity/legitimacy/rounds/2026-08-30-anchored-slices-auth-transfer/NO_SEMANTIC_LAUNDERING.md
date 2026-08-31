# Slice-wise conservation and No Semantic Laundering

## Slice-wise Answerability Conservation

Fix matter \(m\), a slice \(\alpha\) born at \(n_0\), and its authenticated
anchor \(A(m,\alpha)\). Assume:

1. the trace satisfies settled Normative Continuity;
2. initial slice allocation at \(n_0\) is authenticated and complete;
3. every affected resolution batch has valid finite Transfer accounting;
4. every successor load and semantic translation used in that accounting is
   authenticated to the same slice;
5. every terminal receipt is authenticated Satisfaction or authorized
   Disposition;
6. any era change has a join-and-bottom-preserving commuting bridge into the
   slice's anchored semantic domain.

Then, for every \(n\ge n_0\),

\[
A(m,\alpha)=Sat_{\le n}(m,\alpha)\vee
Disp_{\le n}(m,\alpha)\vee
\bigvee_{q\in C_n(m,\alpha)}\lambda_n(m,\alpha,q).
\]

### Proof

At birth, assumption 2 gives the equation. For an inductive step, unaffected
live issues keep their loads by exact outstanding evolution. For each resolved
issue, assumptions 3 and 4 replace its authenticated incoming load by the join
of authenticated satisfaction, disposition, and fresh successor loads.
Associativity, commutativity, and idempotence combine simultaneous splits and
merges. Freshness and matter ancestry put those nonterminal loads on the new
live carrier frontier; settled closure prevents a closed matter from silently
reviving. Assumption 5 handles terminal terms, and assumption 6 makes
era-local substitutions equations in the same anchored domain. The invariant
follows.

Late accretion starts a new induction at its own birth and does not alter this
proof for existing slices.

## No Semantic Laundering

If a slice has no authenticated Satisfaction or authorized Disposition by
prefix \(n\), the conservation equation reduces to

\[
A(m,\alpha)=
\bigvee_{q\in C_n(m,\alpha)}\lambda_n(m,\alpha,q).
\]

Hence a representation, ontology, or evaluator change cannot reduce inherited
content merely by relabeling it. Any weakened part must occur in an authorized
Disposition term. Any strengthened part cannot be charged to the old slice and
must have a fresh authenticated origin.

## What is substantive

Continuity supplies outstanding evolution, fresh successor ancestry, and
absorbing closure. It cannot authenticate a successor's meaning and admits a
structurally live bogus successor. Authentication supplies the substantive
semantic equality; Transfer accounting supplies local conservation. Their
inductive composition is the diachronic result.

All slice and authentication machinery sits above the settled lifecycle. No
Continuity definition or theorem requires surgery.

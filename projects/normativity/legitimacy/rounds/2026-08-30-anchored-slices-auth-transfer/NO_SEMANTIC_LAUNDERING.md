# Slice-wise conservation and No Semantic Laundering

## Slice-wise Answerability Conservation

Fix matter \(m\), a slice \(\alpha\) born at \(n_0\), and its authenticated
anchor \(A(m,\alpha)\). Assume:

1. the trace satisfies settled Normative Continuity;
2. initial slice allocation at \(n_0\) is authenticated and complete;
3. every prefix transition has a finite semantic-mutation batch containing
   every resolved, born, or persistent carrier whose slice load changes, and
   that batch has valid generalized Transfer accounting;
4. every carrier outside that batch persists with exactly the same
   authenticated slice load (the identity frame condition), while every load
   and semantic translation inside it is authenticated to the same slice;
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

At birth, assumption 2 gives the equation. For an inductive step, assumption 4,
not outstanding evolution, preserves the loads of carriers outside the
semantic-mutation batch. Assumptions 3 and 4 replace the join of every affected
old load—including a load edited on a structurally persistent issue—by the join
of authenticated satisfaction, disposition, and affected post-state loads.
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

This equation alone prevents loss in the supplied anchored domain. For the
stronger claim about local answerability-relevant distinctions, additionally
assume that each era interpretation is order-reflecting on its admissible
slice-carrier representations modulo an anchored slice-relative equivalence,
and that successive equivalence quotients are compatible. Then a
representation, ontology, or evaluator change cannot reduce inherited relevant
content merely by relabeling it. Any weakened part must occur in an authorized
Disposition term. Any strengthened part cannot be charged to the old slice and
must have a fresh authenticated and grounded origin.

## What is substantive

Continuity supplies outstanding evolution, fresh successor ancestry, and
absorbing closure. It cannot authenticate a successor's meaning and admits a
structurally live bogus successor. Authentication supplies the substantive
semantic equality; Transfer accounting supplies local conservation. Their
inductive composition is the diachronic result.

All slice and authentication machinery sits above the settled lifecycle. No
Continuity definition or theorem requires surgery.

## Correction at the open PR73 head

The initial version quantified only over resolution batches and said that exact
outstanding evolution preserved unaffected loads. That structural fact says
only which issue occurrences persist; it does not constrain their semantic
loads. A persistent issue could therefore change from load \(a\) to \(0\)
without resolution. The generalized mutation batch and identity frame above
are necessary semantic hypotheses. Sound denotational equations are also too
weak for the strong local-distinction corollary without the order-reflection
condition just stated. The follow-up
2026-08-31-faithful-semantic-preservation round supplies the exact finite
countermodels and repaired proofs.

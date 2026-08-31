# Anchored slices

## Why the matter anchor is not enough

Let one matter open at time 3 with content \(a\), then acquire an independently
grounded obligation \(b\) at time 20. A single value \(A_n(m)\) can record
\(a\) and later \(a\vee b\), but it cannot say when or by what admission
witness \(b\) became owed. Two traces with the same current value can therefore
have different inherited answerability. Treating the later value as a
translation of the earlier one also launders accretion into representation
change.

An append-only growing anchor can be repaired with dated deltas and admission
witnesses. That repaired object is anchored-slice indexing up to isomorphism.

## Minimal object

For each matter \(m\) and prefix \(n\), let \(\Sigma_n(m)\) be a monotone finite
set of slices. Each \(\alpha\in\Sigma_n(m)\) has:

- a birth prefix \(\beta(\alpha)\);
- an immutable anchored denotation \(A(m,\alpha)\in L_\alpha\);
- an authenticated admission witness explaining why it became answerable.

For \(n\geq\beta(\alpha)\), issue \(q\) has a matter-and-slice-indexed current
load \(\lambda_n(m,\alpha,q)\). Define

\[
C_n(m,\alpha)=
\{q\in Live_n(m):\lambda_n(m,\alpha,q)\ne 0\}.
\]

The slice invariant is

\[
A(m,\alpha)=Sat_{\leq n}(m,\alpha)\vee
Disp_{\leq n}(m,\alpha)\vee
\bigvee_{q\in C_n(m,\alpha)}\lambda_n(m,\alpha,q).
\tag{SAC}
\]

It is imposed only from the slice's birth onward. Adding a later slice creates a
new invariant and does not rewrite any earlier invariant.

## Slices are indices, not a second lifecycle

A slice has no outstanding set, issue routes, parents, successor relation, or
closure rule. Existing issue resolution carries a slice through the indexed
loads. Splitting allocates one slice across a successor set; merging joins
matter-indexed loads on one fresh successor. A merged issue can carry slices
from several matters without merging their anchors.

No tested split, merge, late accretion, or ontology translation requires slice
parentage. If an alleged slice evolution changes denotation, it is instead an
authenticated translation, a fresh accretion, or a disposition-plus-admission
revision.

## Translation, accretion, revision

| Operation | Slice treatment | Required evidence |
| --- | --- | --- |
| representation-only translation | preserve slice identity | authenticated denotational equivalence |
| genuinely new obligation | fresh slice | origin time and admission witness |
| weakening | preserve retained slice content | disposition witness for every removed part |
| strengthening | preserve old slice content | fresh slice for the increment |
| incomparable revision | retained old content plus both operations | disposition and fresh admission witnesses |

This classification prevents “translation” from either weakening inherited
content or inventing a fictional history for newly incurred content.

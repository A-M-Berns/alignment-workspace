# Transfer semantics

## Resolution-batch judgment

`Transfer` is matter-indexed and resolution-batch-local. For a matter (m), let (P)
be its resolved carriers in batch (n), and (S) the fresh children with parents in
(P). Define incoming content

\[
I_m=\bigvee_{p\in P}\lambda_n(m,p).
\]

A proof object

\[
Transfer_n(m;P,S;s,d,\lambda';\xi)
\]

contains two distinct obligations.

**Incoming soundness.** Each child's claimed load is inherited from its actual parent
set:

\[
\lambda_{n+1}(m,q')\le
\bigvee_{p\in Par_n(q')\cap P}\lambda_n(m,p).
\tag{TS}
\]

The satisfied component (s) and disposed component (d) are below (I_m), and every
part of (d) has an authorization witness.

**Outgoing completeness.** The whole successor set and terminal receipts account for
all affected content:

\[
I_m=s\vee d\vee\bigvee_{q'\in S}\lambda_{n+1}(m,q').
\tag{TC}
\]

The obligations belong in one proof object because a consumer needs both, but retaining
the two projections identifies different failures. Two children redundantly carrying the
same half pass `(TS)` and fail `(TC)`. A child inventing a new claim fails `(TS)`.

The judgment must see the resolution batch, not only one parent or one child. Split
completeness quantifies over (S); merge soundness uses the child's complete parent set.
The same child may carry distinct loads for several matters, checked independently.

## The local SDT rule

For every affected unresolved component, the allowed account is

\[
Satisfy\ \vee\ Dispose\ \vee\ Transfer.
\tag{SDT}
\]

This is a componentwise rule, so one batch may satisfy one part and transfer another.
Deferral, blockage, and temporary impossibility are not fourth exits: their content
remains transferred to a live carrier. Overlapping successors are permitted because join
is idempotent; redundancy never repairs a completeness gap.

An outstanding carrier not resolved in the batch retains its load. Any in-place semantic
edit must have an identity/translation certificate satisfying the same conservation
equation. Otherwise a structurally live issue can launder its content without using
succession at all.

## Identity and composition

Identity leaves the load allocation unchanged. Sequential composition substitutes each
intermediate carrier's certified successor family, joins terminal receipts, and flattens
the resulting finite family:

\[
b\rightsquigarrow B_1\rightsquigarrow
\bigcup_{b'\in B_1}B_2(b').
\]

Associativity is union associativity; duplicate merge targets are coalesced by
idempotence. Composition also requires compatible authenticated semantic maps at the
intermediate ontology. Two complete-looking link tables do not compose if the second
changes the intermediate denotation. The executable `Translation` fixture checks this.

## `Continue` remains

`Continue_n(P;q',g)` and `Transfer_n(m;P,S;...)` have different consumers and
signatures. The first accepts one fresh issue's initial state and may allow an explicit
reset. The second accounts collectively for one matter's inherited content across all
affected parents and successors. Renaming the settled oracle would falsely suggest it
already proves transfer completeness.

Use **Transfer** for the semantic layer and retain **Continue** in the settled API. A
domain may use an accepted `Continue` record as evidence inside `Transfer`, but it is not
sufficient evidence by itself.

# Burden transport

## Smallest surviving generic core

Simple discharge-or-one-successor conservation is too restrictive.  A burden may split,
several burdens may merge, and an ontology translation may change every identifier.  For
the affected live burdens, use a proof-relevant relation presented as

\[
\Phi_\xi(b)\in
\mathsf{NonemptyFinite}(B(S'))\;\sqcup\;\mathsf{Disposed}.
\tag{BT}
\]

Every successor in the finite family needs a `Transport` proof; a disposition needs a
typed soundness proof.  Totality is required only on `Affected`, but `Affected` itself
needs the domain-specific completeness proof described in the calculus.  The same target
may occur in several images (merging), and one image may contain several targets
(splitting).  A one-to-one translation is the ordinary special case.

Partial discharge is represented by carrying the unresolved residual as a successor.
Allowing a bare “some part discharged” alternative would permit a certificate to erase
the remaining part.

## Semantic frontier

For an initial burden \(b\), let \(F_0(b)=\{b\}\).  Across a sound transition, preserve
unaffected members, replace each carried member by its nonempty successor family, and
remove a member only on a complete certified disposition.  Duplicate successors are
coalesced, so merging is harmless.

### Answerability Conservation (finite-horizon)

Assume for every transition in a finite sequence:

1. the PE scope is complete for all changed members of the current frontier;
2. every affected member has a sound complete disposition or nonempty sound transport;
3. every transported burden has a live structural carrier in the post-state;
4. Continuity's exact outstanding-set evolution, resolution discipline, and fresh
   successor conditions hold for those carriers.

Then every burden live at the initial state has at the final state either:

* a complete tree of certified dispositions, or
* a nonempty frontier of live, semantically transported descendants.

**Proof.** Induct on transitions.  For each frontier member, an unaffected carrier
persists by exact evolution and Continuity; an affected member is removed only by its
disposition receipt or replaced by a nonempty live transported family.  Union the
families and coalesce merges.  A split is fully discharged only when every resulting
branch is eventually disposed.  The induction preserves the stated disjunction. ∎

This is more than matter ancestry: `Transport` states that a successor substantively
represents the inherited target, applicability, exceptions, failures, and response
quality.  It is less than Progress: it does not promise exercise, repair, or eventual
discharge.  The substantive assumptions are transport/disposition validity and affected
completeness; Continuity contributes the carrier bookkeeping.

## Coverage continuation

For coverage, a useful presentation is

\[
\Phi_\xi:
\Gamma_\sigma^{live}\rightrightarrows
\mathsf{NonemptyFinite}(\Gamma_{\sigma'}^{live})
\sqcup\mathsf{Disposed}.
\]

A transport proof records target translation, relevance/applicability translation,
outstanding exceptions and open implementation failures, and no illicit weakening of
route quality.  It permits implementation replacement without a new normative burden,
but rejects silent scope shrinkage.  Ontology translation is legitimate exactly when the
semantic proof and a live successor carrier both exist.

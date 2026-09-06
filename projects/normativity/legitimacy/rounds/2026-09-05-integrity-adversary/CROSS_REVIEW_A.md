# Cross-review of the constructive Integrity definition

Target: `2026-09-05-integrity-constructive/DEFINITIONS.md` and `THEOREMS.md` as read on
2026-09-05. The reviewed core is:

```text
Integrity(Lambda,Closes,a,b) iff
  forall i, a <= i < b -> LocalConservation(Lambda,Closes,i).
```

`LocalConservation` contains `identity_frame`, `incoming_sound`, `carry_complete`,
`closure_certificate`, `sat_receipts`, and `stl_receipts` exactly as quoted in the
constructive round. The attacks below distinguish its valid lattice invariant from the
larger Answerability claim.

## A-X1 — local pass with no adequate answer

Let one issue `q` carry atom `alpha`, resolve by `answer`, and put `alpha` into `sat`.
All six clauses pass. No clause asks for an answer body, responder authority, anchored
answer specification, or adequacy certificate. `src/cross_review_a.py` computes:

```text
LocalConservation = true; AdequateAnswer = false.
```

This is an `exact-witness`. It is also the existing A0 attack specialized to Agent A's
definition. Therefore Agent A Integrity does not imply the existing substantive
Answerability desideratum unless `kind=answer` already means an authenticated adequate
answer. Making that meaning ambient would move the missing Answerability premise into
the trace interpretation, not derive it from Integrity.

## A-X2 — faithful carry does not imply answerable disposal

Let `q` cite itself as its disposal ground and transfer its entire atom to fresh child
`q1`. `incoming_sound` and `carry_complete` both hold; receipts are unchanged. The
finite mirror returns:

```text
LocalConservation = true; self_grounded = true.
```

This is an `exact-witness`. `LocalConservation` reads neither grounds nor `Disciplined`,
and it has no `Li`, standing, opener, or resolver field. Thus the definition proves
content conservation for a self-grounded or unauthorized transition. That is a useful
conservation theorem, but it is not yet Integrity in the proposed provenance-plus-
Answerability sense.

Blocking condition: conjoin a record-integrity predicate, including `Disciplined` or a
successor notion of answerable transition, rather than putting those fields into the
lattice equation.

## A-X3 — `Closes` can certify itself

Let `q` resolve as `settle(s)`, set `Settled_n(s)`, and choose
`Closes(n,s,q)=True`. The closure clause and `stl_receipts` pass even when the resolver
manufactured `Settled`, `s` is false, and the closure rule is unauthorized. The mirror
returns:

```text
LocalConservation = true; externally_supplied = false; settlement_true = false.
```

This is an `exact-witness` about the formal interface, not a claim against the intended
ambient trust boundary. The definition correctly separates `Settled` from `Closes`, but
it proves neither settlement truth/independence nor the provenance of `Closes`. Those
must remain named ambient settlement and record-integrity assumptions. Calling the item
"authenticated" in prose cannot discharge either premise.

## A-X4 — evolving `Closes` retroactively toggles Integrity

On the same stored settlement transition, one evaluator supplies
`Closes(n,s,q)=True`; a later evaluator recomputes the historical predicate as false.
The same local step changes from pass to fail. This is an `exact-witness` in
`closes_recomputed`.

Prefix indexing is insufficient if `Closes` is a replaceable function parameter. The
history must store an immutable closure-certificate identity and basis. Later cognition
may append a `Reconsiders` event and fresh load; it must not alter whether the historical
event carried a certificate. The application may then separately judge that certificate
defeated.

## A-X5 — join accumulation collapses multiplicity

Take two distinct obligation occurrences `q1,q2`, each carrying the same atom `alpha`,
and answer both. The exact receipt count is `2`; `sat` is
`{alpha} join {alpha} = {alpha}`, with cardinality `1`. All local clauses pass.

This is an `exact-witness`. The theorem conserves a join of semantic content, not
additive debt multiplicity. It is exact in its stated semilattice, but it cannot by
itself recover the carrier round's occurrence weights or distinguish two separately
owed copies of the same anchored content. A realization must encode occurrence identity
inside `L` or use an additive/accounting structure when multiplicity matters.

The same issue sharpens merge laundering: a merged child's load may cover two parents
with equal lattice content because both inequalities ask only for `alpha <= alpha`.

## A-X6 — zero-ledger vacuity and the endpoint relation

`Integrity` does not include the initial account equation or authentication that
`Lambda` represents an admitted slice. The everywhere-bottom ledger satisfies the five
algebraic clauses for every non-settlement transition, including erased substantive
debt. The constructive theorem ledger correctly lists authenticated anchored loads and
the initial equation as additional hypotheses; the proposed endpoint relation in
`DEFINITIONS.md` does not.

Therefore

```text
H_a <=_leg H_b iff exists a segment carrying Integrity
```

is under-specified if the witness may choose `Lambda`: it admits the bottom witness.
The endpoint interface must quantify over the declared admitted slices and bind their
initial accounts, or package the authenticated ledger into the segment certificate.

This is a `paper-derived` consequence of the displayed definitions. No new Lean lemma
is needed: every bottom inequality and receipt equation is reflexive.

## A-X7 — what composes, and what does not

Concession: `integrity_compose` is correct for the same `Lambda`, anchored domain, and
`Closes` function. Its proof is interval case analysis, and no attack here defeats it.

The proposed endpoint relation has not yet inherited that theorem. Two existential
segment witnesses may use different ledgers, slice universes, or historical `Closes`
interpretations at their shared endpoint. Agent A explicitly says exact agreement is
required; the displayed endpoint relation does not type that agreement. Either:

- the endpoint state packages those objects and equality/transport at the boundary, or
- composition takes an explicit compatibility certificate.

Without one, HI-3 is a theorem about fixed parameters, not transitivity of
`<=_leg`. This is an `open` interface obligation, not a counterexample to HI-3.

## A-X8 — Non-Capture remains outside

No formal local clause accidentally imports Non-Capture: none quantifies over
counterfactual interventions, coalitions, or control of entry, standing, licences,
rules, or settlement. This is a concession. Conversely, "authenticated anchored
loads" and a "prior licence" must not be strengthened during realization to mean that
the issuer could not be captured. Authentication establishes provenance; Non-Capture
establishes resistance to a declared control class.

## Surviving core

The following survives cross-examination.

- `incoming_sound` plus `carry_complete` prevents a disposed load from decreasing as a
  join in one fixed, authenticated anchored lattice.
- `identity_frame` prevents silent mutation on unresolved carriers in that lattice.
- the two receipt equations and closure premise yield the stated account invariant.
- `Settled` and `Closes` are correctly separate inputs.
- fixed-witness segment restriction, reflexivity, and composition are valid.

The result should be stated as **content-account conservation conditional on record
Integrity, answer adequacy, closure provenance, authenticated slice semantics, and an
initial account**, not as a derivation of those conditions from the six local clauses.

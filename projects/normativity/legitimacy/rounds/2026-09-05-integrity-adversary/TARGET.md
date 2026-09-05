# Target conditions

These are the exact weak generic-Integrity conditions attacked. They are a proposed
interface, not a claim that the wiki or the landed theory endorses their conjunction.
The executable replay in `src/integrity_model.py` implements I1, I2, and I4–I7 and the
trace parts of I3 and I9. I8 and the closure judgment above the trace have separate
finite fixtures.

Let a history be a sequence of batches. At prefix `n`, `O_n` is the outstanding set,
`Born_n` and `Res_n` are the current batch, `par(q)` is immutable ancestry,
`Pre_n(q)` is the active prerequisite set, and `Settled_n` is the external settlement
view. Each issue has an immutable anchor, opener, and exact load.

## I1 — append-only event discipline

An issue is born once; only an outstanding issue resolves; a resolution removes it at
the next prefix; and records already stored are not rewritten. A prerequisite occurrence
is introduced once. This is structural Integrity.

## I2 — anchored births

Every birth records an immutable anchor and opener. A disposal successor is evaluated
against a supplied licence relation `Li`; `standsFor(Li,n,b,k)` means that some issue
live at `n` licenses participant `b` at anchor `k`. `Li` itself is an evaluator-supplied,
unversioned parameter. This is the weakest executable reading of "authenticated birth"
present in the current `DefeatTrace`; it does not authenticate the issuer of a licence.

## I3 — grounded replay

> `Replay(q) := ∃ r, anc(r,q) ∧ par(r)=∅`.

Parent links point from an issue resolved in the child's birth batch. Thus they point
strictly into the recorded past. `Replay` does not require `r` to be at position zero or
to satisfy an independent `Auth` predicate.

## I4 — strict pre-state citation

> `Grounded_n(issue q) := ∃ j<n, q∈Born_j`;
> `Grounded_n(settled s) := s∈Settled_n`.

Every disposal ground is grounded at its resolution prefix. No co-born successor or
other same-batch issue can ground that disposal.

## I5 — constitutive immutability

Parents and anchors do not change after birth. A successor named by a resolution is
fresh and names the resolved issue as parent. A new prerequisite route root is live or
co-born. These clauses type the record; they contain no semantic identity judgment.

## I6 — local acyclicity

The disposed issue itself is absent from its grounds. Strict pre-state citation and
fresh ancestry exclude direct self-grounding and ancestry cycles. They do not exclude a
later ground that undercuts an earlier ground through a successor.

## I7 — disciplined resolution

Every resolution has exactly one of these forms:

> `answer`; or
> `dispose(G,q')`, where `q'` is a fresh child, every `g∈G` is grounded,
> the resolved issue is not in `G`, a participant other than the resolver stands on
> `q'`, and `G` contains a settlement fact or an issue opened by another participant;
> or `settle(s)`, where `s∈Settled_n`.

The principal-relative strengthening additionally requires a designated `P` to stand
on `q'`. `answer` has no receipt, semantic adequacy, responder-authority, or
no-successor clause. `settle(s)` has no `Closes(H_n,s,α)` premise.

## I8 — faithful semantic carry

For an anchored slice `A`, a representation change `iota` is accepted when it induces
an order embedding on the declared slice-relative quotient:

> `iota(x) ≤ iota(y)  ⇒  [x]_A ≤ [y]_A`.

The quotient is supplied with the certificate. I8 does not require the quotient itself
to be anchored to the slice's birth vocabulary or require split/merge maps to preserve
joint answer specifications.

## I9 — external monotone settlement

`Settled_n ⊆ Settled_{n+1}` and settlement additions are treated as supplied through
the trusted external boundary. The item is authenticated as an item; the internal
history decides neither its truth nor its arrival. I9 does not type the item as closing
an obligation.

## Candidate conclusion under attack

> **Generic-Integrity-to-Debt-Conservation:** for every obligation load incurred in an
> I1–I9 history, the terminal account is an adequate answer, a settlement item together
> with a valid prefix-relative `Closes` certificate, or a semantically faithful live
> carrier preserving the original answer specification and standing.

The countermodels refute derivability from I1–I9. The conclusion contains predicates
that I1–I9 either leave uninterpreted or do not store.

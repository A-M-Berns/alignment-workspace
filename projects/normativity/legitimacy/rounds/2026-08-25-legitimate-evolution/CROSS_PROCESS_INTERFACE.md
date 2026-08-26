# What one process receives, and what it may infer

Status: **specification; unregistered.** Names provisional.
`LEGITIMATE_EVOLUTION.md` carries the theory; `CONSUMER_TEST.md` and
`TRADERIZATION_CONSUMER.md` are the two consumers.

---

## 1. The shape

```text
Recognizes_A(G)                     A accepts a base
A accepts Pi = (Permit, ProvOK)     and an authorization semantics
A accepts Xi                        and a threat class
A accepts alpha                     and an audit context
o in Auth(L(alpha, t))              the certificate checks
------------------------------------------------
Recognizes_A(o)
```

**Verifier soundness is a theorem** and is now stated where it belongs: `Verify`
is a checker, `Valid` is the semantic relation, and `verifier_sound` is the claim
that the first implies the second along the replay it drives.

**Iteration is not an extra assumption.** The replay is a fold, so a recognizer
that accepts the step accepts any finite run of steps. There is no separate
composition principle to state.

**The bridge is an axiom, and it now carries four parameters rather than two.**

> **(R) — the recognition axiom.** `A` regards an occurrence in
> `Auth(L(alpha, t))` — the legitimate state of a process whose base, permit
> relation, provenance relation and audit context `A` accepts — as one it
> recognizes. `[AXM]`

What the mathematics contributes is the narrowing: (R) commits `A` to H1-H6 being
the right conditions and to `Permit`, `ProvOK`, `Xi` and `alpha`, and to nothing
about what the future authority says.

## 2. What A does not have to do

**Endorse the content.** No clause of the replay reads what an occurrence says.
`apply` is content-blind by the type, and relabelling every value specification
in a record leaves the legitimate state fixed.

**Know B's internal representation.** H1-H6 are conditions on
`(Occ, Edit, G, Valid, Permit, ProvOK)`. A constitution and its gazette satisfy
them with no ledger; a Reflective Integrity record satisfies them with one.

**Trust what B is doing.** This is the change from the previous interface. The
raw process's own view of what is in force is not consulted at all: `L` is
rebuilt from the base, and a process that has revoked something it had no
authority to revoke is simply wrong about its own state.

**Accept an act because it survived a counterfactual.** Legitimacy is a local
judgment about an edit given the state it was made in, so an act that would not
have happened but for an argument is not thereby suspect.

## 3. The certificate, and what it costs now

```text
Ground = ( occ, edit, children )
```

A finite grounding tree: leaves in `G`, internal nodes accepted edits, children
the grounds each edit invoked, historical index strictly decreasing. That is the
whole certificate. **The stability judgments are gone**, because there is no
challenge operator to evaluate.

What a recipient must be able to do instead is evaluate `Valid` at each node —
which is `grounds ⊆ Auth(L)`, `Permit`, and `ProvOK` at the audit context. The
first two are local to the tree. `ProvOK` is where the cost now sits, and it is
smaller than before: a judgment about one edit's declared input and exercise
rather than a replay of the whole record under a voided episode.

So the honest reading of a certificate is:

1. `A` evaluates `ProvOK` itself, which needs the declared inputs and `alpha` but
   not the raw history;
2. `A` names an audit context and `B` answers for the edits it doubts;
3. `A` accepts an attestation, which is a trust assumption and should be recorded
   as one.

Route 1 is now available and was not before, which is the main practical gain of
the compression.

## 4. What A must be told, and it is more than before

Everything is relative to four inputs, and a certificate that omits any of them
certifies nothing:

```text
G        the base                    — A recognizes it or the question is empty
Pi       Permit and ProvOK           — what counts as an authorized exercise
Xi       the threat class            — what influences A cares about
alpha    the audit context           — what is currently believed about the past
```

`alpha` is the new one and it is not a formality. Two recognizers with the same
base and the same semantics can legitimately disagree about what is in force,
because they believe different things about whether an old edit's conditions were
actually met. That is a feature — it is how a recognizer revises on new evidence
— and it means recognition is indexed, not absolute.

## 5. Answerability, and what became of it

Not in the headline object, and this pass did not put it back. The previous
pass's countermodel stands: a delegation nobody answers for has a clean spine and
a derivable authority.

Under the compressed theory the point sharpens. Custody — who is answerable — is
not part of the legitimate state at all, because the state is a set of
occurrences and has no holder field. Reflective Integrity's `Transfer` is
therefore a **no-op on `L`**, and a recognizer that cares whether `B` is an
answerable process is asking a question this object does not answer.

That is the right division and it is stated rather than assumed: entitlement is
what `L` tracks; answerability is a separate interface; and `TRADERIZATION_CONSUMER.md`
§5 has the third.

## 6. The three interfaces

```text
legitimate    entitled                  o in L(alpha, t), under Pi and Xi
accountable   answerable                the account layer — not here
serviceable   sustainably enforceable   bounded-lifetime liability — not here
```

Independent, and the process carries no liability field. A legitimate norm can be
unenforceable, and the enforcement API says so itself.

# What one process receives, and what it may infer

Status: **specification; unregistered.** Names provisional.
`LEGITIMATE_EVOLUTION.md` carries the theory this document is the consumer face
of, and `TRADERIZATION_CONSUMER.md` the second consumer's half.

---

## 1. The shape

```text
Recognizes_A(G)                     A accepts a base
A accepts a verifier V
A accepts a threat model Xi
V(c) = true                         the certificate checks, and covers Xi
------------------------------------------------
Recognizes_A(target(c))
```

**Verifier soundness is a theorem.** `verify(f, c) => G |- target(c)`, because the
verifier recomputes derivability rather than reading the certificate's own
verdicts. `[THM]`

**Iteration is a theorem.** `|-_q` is the least fixed point of the certified-step
operator, so derivations compose: `A` needs the bridge principle for one step and
gets arbitrarily long evolutions from it. Without this a recognizer would need a
separate commitment per step, and a process could evolve out of recognition by
taking small ones. `[THM]`

**The bridge is an axiom.**

> **(R) — the recognition axiom.** `A` regards inheritance of authority through a
> certified succession from a base it accepts, against a threat model it accepts,
> as preserving its recognition. `[AXM]`

`RecognitionTransport` is (R) plus verifier soundness plus composition, and the
mathematics' job is to say as narrowly as possible what (R) commits to: L0-L4 and
`Coverage` being the right conditions, and nothing about what the future
authority says.

**The threat model is now part of what A accepts**, and this is the pass's
addition to the recognition axiom. A certificate is relative to a set of
influences; a recognizer that accepts a certificate has thereby accepted the
threat model it names, and one that cares about an influence the certificate does
not cover has not been given a reason.

## 2. What A does not have to do

**Endorse the content.** No clause of `|-` reads what an authority says: the frame
has no content field, relabelling every value specification in a record leaves the
derivable set fixed, and `C11`, `C14` and `C33` are records where recognition
transports across a content change.

**Know B's internal representation.** L0-L8 are conditions on
`(A, T, affected, parents, tgt, lic, rank, when, live, Chal, |=)`. A register of
warrants satisfies them with no ledger; a Reflective Integrity record satisfies
them with one.

**Recognize B's acts.** `|-` transports *possession* of authority. Whether a
particular exercise was licensed is `prospective_license`, which is act-relative,
reads the pre-state at the act's own time, and reads content. Recognition that
`B` is entitled to decide is not agreement that any decision of `B`'s was
permitted.

**Accept that stability is enough.** It is not, and this is the pass's central
repair. An authority that survives a challenge may be entitled to nothing, and a
recognizer inheriting authority from such an object is doing exactly what
laundering is for. `COUNTERMODELS.md` §1.

## 3. The certificate, and where it stops being cheap

```text
Cert = ( base, target, steps, challenges, stability, coverage_claim, accounts )
```

**`steps`** is the derivation: finite in the size of the target's ancestry,
checkable by anyone holding it, and canonical under L2'. Without L2' it is a
*route*, and the recipient learns that this route is clean and not that every
route is — which is the right thing to learn, since a challenged issuer may sit
in a route-blind provenance while the authority is perfectly legitimate.

**`stability`** is a list of judgments about a counterfactual, and whether they
compress is a fact about the realization. In the warrant register a judgment is a
reachability query over a dependency graph and the recipient can be handed the
graph. In the Reflective Integrity realization it is a replay of the whole record
under a voided episode, the operator is neither monotone nor composable, and no
compression is available.

So for our realization a certificate is one of:

1. `A` holds `B`'s record and evaluates the challenges itself;
2. `A` names a challenge and `B` answers it — a challenge-response exchange
   rather than a document;
3. `A` accepts an attestation, which is a trust assumption and should be recorded
   as one.

Route 2 is the one the architecture has a shape for: an anti-bootstrap demand is a
demand on an account, and challenge and review roots are named in Reflective
Integrity §32 as a conservative extension. `PRIORITIES.md` item 67.

**`coverage_claim`** names the influences the certificate is offered against.
`certify` returns nothing when coverage fails: a certificate against an uncovered
threat is not a weaker certificate.

**`accounts`** is optional and carries the outstanding accounts beneath the base.
A recipient that wants it must be given the branching, not the chain.

## 4. What A must be told about the base and the threat model

Everything here is relative to `G` and to `Xi`, and both are inputs.

- `A` recognizes a base it should not: nothing here helps. Legitimacy is definable
  only relative to a base recognition relation and this round makes that explicit
  rather than removing it.
- `A` accepts a threat model narrower than its actual worry: the interface
  certifies and the recognition is worth what the threat model is worth. A
  record's own episodes generate a threat model it covers by construction, which
  is the ceiling on self-certification and not a solution to provenance
  completeness.

## 5. What A learns from the account layer

```text
continuous(base account)     no end anywhere below it is unanswered
outstanding_below(a)         the witnesses, if not
```

A process that cares whether `B` is *answerable*, rather than only whether `B`'s
authority is *entitled*, reads this. The two come apart:
`delegated_custody(answered=False)` has a derivable authority, a clean spine, and
an account outstanding forever. Authority recognition transports there and
deference should not, and the distinction belongs at this boundary rather than
inside `|-`.

## 6. The three interfaces

```text
legitimate    entitled                    G |- y, under coverage
accountable   answerable                  the account layer, L7-L8 and T5
serviceable   sustainably enforceable     bounded-lifetime liability
```

Independent, and a consumer picks. `LegitimateEvolution` does not mention
liability, and the frame carries no field for it —
`test_the_frame_carries_no_liability_field` pins that. The reason is downstream
rather than conceptual: an authority that inherits unbounded outstanding
liability is still entitled and is not serviceable, and the enforcement API's own
exhaustion behaviour says so in as many words. `TRADERIZATION_CONSUMER.md` §5.

# What one process receives, and what it may infer

Status: **specification; unregistered.** Names provisional. `LEGITIMATE_EVOLUTION.md`
carries the theory this document is the consumer face of.

---

## 1. The shape

```text
Recognizes_A(G)                     A accepts a base
A accepts a verifier V
V(c) = true                         the certificate checks
------------------------------------------------
Recognizes_A(target(c))
```

Three things about that inference, in order of how much they cost.

**The verifier's soundness is a theorem.** `verify(f, c) => G |- target(c)`,
because the verifier recomputes derivability rather than reading the
certificate's own verdicts. `[THM]`, `test_frame.py`.

**Iteration is a theorem.** `|-_q` is the least fixed point of the certified-step
operator, so derivations compose: `A` needs the bridge principle for one step
and gets arbitrarily long evolutions from it. `[THM]`. This is the whole of what
the mathematics contributes to transport, and it is not nothing — without it a
recognizer would need a separate commitment per step and a process could evolve
out of recognition by taking small ones.

**The bridge is an axiom.** That `A` *treats* a certified succession as
recognition-preserving is not derivable and this round does not derive it:

> **(R) — the recognition axiom.** `A` regards inheritance of authority through
> a certified succession from a base it accepts as preserving its recognition.
> `[AXM]`

Stating (R) is the honest form. `RecognitionTransport` is not a theorem; it is
(R) plus verifier soundness plus composition, and the mathematics' job is to say
as narrowly as possible what (R) is a commitment to. It is a commitment to L0-L4
being the right conditions and to nothing else — in particular, not to any claim
about what the future authority says.

## 2. What A does not have to do

**A does not have to endorse the content.** No clause of `|-` reads what an
authority says: the frame has no content field, and relabelling every value
specification in a record leaves the derivable set fixed while changing what is
in force. So `Recognizes_A(y)` is available where
`content(y) != content(g)` for every `g` in `A`'s base, and `C11`, `C14` and
`C33` are the records where that actually happens. `[THM]` + witnesses.

**A does not have to know B's internal representation.** L0-L4 are conditions on
`(A, T, src, tgt, lic, rank, Chal, |=)`. A register of warrants satisfies them
with no ledger anywhere; the Reflective Integrity realization satisfies them
with one. `A` reads the frame, not the implementation.

**A does not have to recognize B's acts.** `|-` transports *possession* of
authority. Whether a particular exercise was licensed is
`prospective_license`, which is act-relative, reads the pre-state at the act's
own time, and reads content — a protocol's `covers` and `condition`. Recognition
that `B` is entitled to decide is not agreement that any given decision of `B`'s
was permitted, and keeping the two apart is what lets recognition be
content-blind while permission is not.

## 3. The certificate, and where it stops being cheap

```text
Cert = ( base, target, steps, challenges, stability, accounts )
```

**`steps`** is the derivation: finite in the size of the target's provenance,
canonical under L2', and checkable by anyone holding it.

**`stability`** is a list of judgments `q |= u`. The interface makes no promise
that these compress, and the two realizations disagree about whether they do. In
the warrant register a stability judgment is a reachability query over a
dependency graph and a recipient can be handed the graph. In the Reflective
Integrity realization it is a replay of the whole record under a voided episode,
the operator is neither monotone nor composable, and **no compression is
available**: a positive survival witness for one event is the excised prefix
that admits it.

So for our realization the honest reading of a certificate is one of:

1. `A` holds `B`'s record and evaluates the challenges itself;
2. `A` names a challenge and `B` answers it — a challenge-response exchange
   rather than a document;
3. `A` accepts an attestation, which is a trust assumption and not a legitimacy
   fact, and should be recorded as one.

Route 2 is the one the architecture already has a shape for: an anti-bootstrap
demand is a demand on an account, and challenge and review roots are named in
Reflective Integrity §32 as a conservative extension. Nothing here builds it.

**`accounts`** is optional and carries the outstanding accounts beneath the base
— what T6 makes visible. A recipient that wants it must be given the branching,
not the chain: a derivation to one successor of a two-way supersession says
nothing about the other's account, and `split_with_due_branch` is the record
where the chain is clean and the base is discontinuous.

## 4. What A must be told about the base

Everything in this document is relative to `G`, and L0 says `G` survives every
challenge in view. Two failure modes, both real:

- `A` recognizes a base it should not. Nothing here helps; legitimacy is
  definable only relative to a base recognition relation, and this round makes
  that explicit rather than removing it.
- `A` recognizes a base and `B`'s challenge set does not include the influence
  `A` cares about. `Q` is the record's own episodes, and the criterion is
  exactly as good as the provenance links the record carries. That hypothesis is
  the Carroll round's `C25` and is not closed.

## 5. What A learns from the account layer

A separate reading, and the only one that can fail with the authority side
clean:

```text
continuous(base account)     no end anywhere below it is unanswered
outstanding_below(a)         the witnesses, if not
```

A recognizing process that cares whether `B` is an *answerable* process, rather
than only whether `B`'s authority is entitled, reads this. The two come apart:
`delegated_custody(answered=False)` has a derivable authority, a clean spine, and
an account outstanding forever. This round's position is that authority
recognition should transport there and that deference should not, because they
are answers to different questions — and that the distinction belongs at this
boundary rather than inside `|-`.

## 6. Liability

`LegitimateEvolution` does not mention liability, and the interface carries it as
a field a consumer may read rather than as a clause. The reason is the downstream
one rather than a conceptual symmetry: an authority that inherits unbounded
outstanding liability is still entitled, and it is not *serviceable* — the
vertical slice's `T3b` says an account that cannot fund its charge emits no force
and produces no price. So an insolvent `B` has recognized authority and inert
authority, which is a fact `A`'s trust layer needs and `A`'s recognition does
not.

# Prosecuting the hypotheses

Status: **prosecution record; unregistered.** Every entry names the frame that
decides it and the test that runs it.

Six of the eight sections below settle a question the round's first pass got
wrong or left open, and three of them were decided by a register of offices
rather than by a record, because Reflective Integrity's admission preconditions
make the alternatives indistinguishable inside our own architecture.

---

## 1. The licence had only to be stable, and that refuted the headline theorem

**`warrant.stable_but_illegitimate_register`.**

```text
act:plant     challenged; grants w:tainted
act:launder   clean findings, under the charter; supersedes w:tainted by w:m
act:use       under w:m; grants w:y
```

`w:m` **survives** the challenge — the act that granted it relies on nothing void
— and is **not** derivable, because it inherits from `w:tainted`. The first
pass's rule required a licence only to satisfy `q |= lic(t)`, so:

```text
rejected rule    w:y is derivable,      and bootstrapped_under is non-empty
repaired rule    w:y is refused,        and thm_no_bootstrap is clean
```

This is a refutation and not a proof gap. On the frame above, every axiom of the
spine holds and **T2's conclusion is false**: `w:tainted` sits in `w:y`'s
provenance and was issued by a challenged exercise. The first pass's proof step
"each such `z` is itself derivable" was unavailable for a licence, because
derivability recursed only through parents while provenance ran through licences
too.

**The repair** is that the licence is a *ground*: `grounds(t) = parents(t) ∪
{lic(t)}` and derivability requires all of it. Stability of the licence then
follows from T2a rather than being assumed, so the repaired rule has one clause
fewer, not one more.

`frame.derivable_stable_licence` keeps the rejected rule so the two run side by
side, and `TestTheLicenceMustBeDerived` runs them.

**Stable-but-illegitimate objects are wanted, not excluded.** `w:m` is exactly
such an object and the interface's job is to refuse what it licenses. A
recognizing process must not inherit authority merely because the authority
survived a counterfactual, and this register is where that sentence has a truth
value.

## 2. Acting on a standing is not inheriting from it

**`warrant.cleanup_register`.** A regulator revokes a fraudulent warrant and
grants a proper one:

```text
act:cleanup     revokes w:tainted, inherits from nothing, grants w:proper
act:relaunder   inherits from w:tainted,                  grants w:carried
```

`w:proper` is derivable and `w:carried` is refused. Under the first pass's rule —
where the objects acted on were the legitimacy parents — the cleanup produced an
illegitimate successor, which is the wrong answer: a legitimate authority ending
an illegitimate standing is doing the thing one wants it to do.

So the type splits. `affected(t)` is what the exercise acts on and constrains
nothing; `parents(t)` is what its issue inherits from and must be derivable.

**The record calculus can express both**, and `cases.record_cleanup` is the
witness: a revocation acts on the tainted standing and issues nothing, and a
separate creation issues under a seeded authority and inherits from nothing. In
Reflective Integrity a `Supersede` that issues does inherit from what it
supersedes — `pred(y) = X` is the lineage — so a cleanup is two events, and that
is a fact about the record calculus rather than a limitation of it.

**All of `parents`, not one of them.** `warrant.merge_register` is unchanged from
the first pass and still decides it: an act inheriting from a manufactured
warrant and an earned one, relying only on clean findings, is refused under
all-of and admitted under one-of. The Reflective Integrity realization cannot see
this — `G6` refuses a supersession with an absent target — which is why the
register exists.

## 3. Unique issuance is optional, and the theorem had to move to make it so

**`warrant.two_issuers_register`.** Two chanceries and no central roll: `w:dual`
is entered by each, once on a challenged finding and once cleanly.

```text
L2'                     fails
thm_finite_lineage      clean
w:dual, w:downstream    derivable, by the clean route
provenance(w:downstream)  contains the challenged issuer
the derivation           does not
```

The first pass claimed L2' bought only canonicity while `minted_by` raised on a
second issuer and `provenance` and the no-bootstrap theorem both ran through it.
That claim was not false so much as untested, and the register tests it.

Three repairs. `minted_by` returns the first issuer rather than raising, so an
existential theorem cannot lean on uniqueness. `provenance` closes over **every**
issuer, which is the right object for T1 — a claim about the whole graph being
well founded. And **T2 is stated over a derivation**, not over the provenance,
because on this register the union contains a challenged issuer while the
authority is perfectly legitimate.

So the separation is real:

```text
without L2'   every authority has at least one finite lineage to G   (T1)
with L2'      the provenance is determined by the target              (T1')
```

and L2' is out of the checked spine.

## 4. Exercise identity relocates the hypothesis rather than removing it

**`cases.partial_effect`.** One `Create`, two payloads, and only the second reads
the strict pre-state — it names the number of reasons on the ledger. Excising an
episode that contributed a reason changes the effect and leaves the first payload
alone.

```text
identity = "event"     L3  fails at @s5.1     L3' clean
identity = "effect"    L3' fails at @s5.0     L3  clean
```

`C28` alone would have suggested effect identity is free: it fails L3 under event
identity and satisfies the whole spine under effect identity. `partial_effect` is
the record that shows the general case, and both failures are the same defect
seen from two sides.

**Both are discharged by pre-state-blindness**, checked rather than declared by
rerunning each schema against a truncated pre-state. So the first pass's
hypothesis was not an artefact of a coarse map; it is the record-level condition
that makes the challenge operator's action on effects determinate.

The identity is therefore chosen on external semantics. *If the same act is
replayed but produces a different authority-changing effect, did the same
legitimacy-relevant exercise survive?* No — so effect identity is the default,
and the round records that this buys a repaired `C28` and no hypothesis.

## 5. Coverage: a structurally perfect frame that certifies a captured warrant

**`warrant.undercovered_register`.** A capture grants a warrant, the warrant
grants a permit, and the register challenges nothing.

```text
spine violations      {}
challenges            ()
derivable_everywhere  every warrant, including the captured one
```

Every axiom holds, vacuously, and the calculus certifies the thing anyone would
have wanted it to refuse. The first pass carried this as a prose caveat; it is
now a hypothesis with a type.

```text
ThreatModel = (Xi, depends)
Coverage    :  forall xi. exists q. depends(xi) subset Chal(q)
```

`certified_against` returns the empty set when coverage fails, and `certify`
returns no certificate at all — a certificate against an uncovered threat is not
a weaker certificate. The same threat model against `laundered_register`, which
does challenge the influence, certifies the charter and refuses the permit.

**What this does not do.** `depends` is supplied from outside and nothing here
computes it. A record's own declared episodes generate a threat model its
challenge set covers by construction, which is the honest ceiling on
self-certification and is not a solution to provenance completeness. The Carroll
round's `C25` — two episodes with no reference reaching each other — is
unaddressed and is now visibly a failure of `depends` against `Chal` rather than
a vague caveat.

## 6. Answerability, and the countermodel that kept it out of the spine

**`cases.delegated_custody(answered=False)`**, unchanged from the first pass, and
now also **`warrant.unanswered_delegation_register`** so the same shape exists in
a frame with no record.

```text
spine violations             {}
derivable everywhere         the delegated authority is in it
continuity at the base       False
outstanding below the base   the disposed episode, forever
```

Every authority-side clause holds; only the holder moved and only the account is
outstanding. Adding answerability continuity to the succession relation would
refuse a case in which nothing about the authority is wrong.

What the account layer earns instead is two constructors the authority graph
cannot express — delegation issues nothing, disposal has no successor — and T5,
the only clause of the interface that can fail with the authority side clean.

**The traderization consumer does not change this**, and `TRADERIZATION_CONSUMER.md`
§4 is why: what it needs is bounded liability, which is a third thing again.

## 7. Where a suspension is not an edge

`SetStatus` writes neither `pred` nor a fresh identifier, so a suspension and a
reactivation make no authority edge. It is an `affected` with empty `parents` and
empty `tgt`, and it moves the lifecycle view without moving derivability — which
is the right answer, since suspending an authority does not unmake its
entitlement.

The Carroll round's consequence stands: excising *more* can restore a suspended
authority and with it a later event's admissibility, which is why the challenge
operator is not monotone. The frame does not repair that and does not need to,
because `derivable_everywhere` intersects per-challenge verdicts and never
excises a union.

## 8. The strongest counterexample that survives

Provenance incompleteness, now stated as a coverage failure rather than as prose.
An external process can satisfy L0-L8 with a `depends` its `Chal` does not reach,
and the interface will certify it. `Coverage` makes the hypothesis explicit and
does not discharge it; nothing in this round says how a process comes by an
adequate challenge set, and the answer is not available from a record
counterfactual.

Second, and smaller: the account layer remains Reflective Integrity's
answerability structure with the names changed. `warrant.py` realizes it, but the
realization was written to match rather than found independently, so it is the
one part of the interface whose abstraction is not tested by a system that had
its own reasons for the same shape.

## 9. What no entry above claims

That the spine is minimal. L2' is out; nothing shows the remaining six cannot be
merged further, and L5-L8 are four axioms doing bookkeeping that a better
factorization might do with two.

That the interface has no counterexample. It has fifty-six checks the round
wrote, against axioms the round wrote, in two realizations the round wrote. The
evidence that the exercise was adversarial is §§1-4, where a review's diagnosis
refuted a shipped theorem, a register refuted a shipped design decision, a
register refuted a shipped claim about what an axiom buys, and a new record
refuted the round's own first reading of what the identity repair would achieve.

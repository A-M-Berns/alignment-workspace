# Legitimate evolution and cross-process recognition

Status: **specification, reference models and a prosecution record;
unregistered.** All names are provisional under `AGENTS.md` §6. Nothing here is
Lean-checked and no claim is registered.

## Verdict

LEGITIMATE-EVOLUTION-TWO-CONSUMER-READY — the licence-grounding defect is repaired and the no-bootstrap theorem is valid over derivations rather than provenances; lineage existence is free of unique issuance; challenge coverage is a typed hypothesis rather than a caveat; exercise identity relocates the pre-state condition rather than removing it; the interface exports a legitimately live frontier with two projections; and both the deference and enforcement consumers can read it without any Reflective Integrity vocabulary, each with one named missing hypothesis of its own.

Read that with the four reservations below, all of which are in `THEOREM_MAP.md`
and `COUNTERMODELS.md`.

**The previous verdict was wrong and is withdrawn.** The first pass's headline
theorem was false, not merely under-proved: `warrant.stable_but_illegitimate_register`
satisfies every axiom, derives an authority, and puts a challenged issuer in its
provenance. The rejected rule is kept in the module so the two run side by side.

**Recognition transport is still an axiom** plus verifier soundness plus
composition — and it now also commits the recognizer to a threat model.

**Coverage is explicit and undischarged.** `depends` is supplied from outside and
nothing computes it. A record's own episodes generate a threat model it covers by
construction, which is the ceiling on self-certification.

**Neither consumer theorem is provable yet.** Deference needs an index on the
principal's grade; enforcement needs bounded-lifetime liability. Both are named
and both are on the consumers' side of the boundary.

## The two layers

```text
                succession frame  +  L0-L4  +  coverage
                          |
                          |   T1-T5, recognition transport
                          v
   legitimate evolution, a legitimately live frontier, two projections
  ------------------------- realization boundary -------------------------
   Reflective Integrity, standing replay, reason provenance,
   answerability succession, challenged replay
                          |
                          |   realization theorem
                          v
                 satisfies L0-L8 (L3' under one named condition)
```

`src/warrant.py` is a register of offices and appointments. It imports `frame.py`
and nothing else of this repository's, and it **settled three questions our own
architecture cannot see**, because Reflective Integrity's admission preconditions
make the alternatives indistinguishable inside a record: whether a licence must be
legitimately grounded, whether an exercise's legitimacy parents are the objects it
acts on, and whether lineage existence needs unique issuance.

## The spine

```text
L0   base stability        every base authority survives every challenge
L1   precedence            an exercise follows what it acts on and inherits from,
                           and precedes what it issues
L2   no ex nihilo          every authority is in the base or was issued
L2'  unique issuance       optional; out of the checked spine
L3   issuance stability    if the act survives, what it left in force survives
L3'  origin necessity      an authority survives only if some issuer does
L4   challenge bite        a challenge voids the exercises it challenges
C    coverage              the challenges reach the influences in the threat model
L5   lifecycle entry       nothing comes into force without an act
L6   lifecycle exit        nothing falls out of force on its own
L7   account carriage      ends what it acts on, opens one for what it leaves
L8   account trichotomy    open, outstanding or answered; none removed
```

## What the repair changed

```text
G |-_q y   :=   y in G,  or
                exists t.  parents(t) union {lic(t)}  subset Derivable_q
                       and y in tgt(t)
                       and q |= t
```

Three separations, each forced by a countermodel.

**The licence is a ground.** Being stable is surviving a challenge; being
derivable is being entitled. A recognizer must not inherit authority merely
because the authority survived the counterfactual, and requiring the licence to be
derivable makes stability of it a *consequence* rather than a second clause.

**`affected` is not `parents`.** A regulator revoking a fraudulent warrant and
granting a proper one acts on the fraudulent one and inherits from its charter.
The old rule made the replacement illegitimate; the record calculus expresses the
cleanup as two events and the replacement is derivable.

**The theorem is about a derivation.** With two issuers for one authority, the
route-blind provenance contains a challenged issuer while the authority is
perfectly legitimate by the clean route. So `provenance` is the object for lineage
existence and a *derivation* is the object for no-bootstrap.

## The lifecycle, and the second consumer

`F^leg_s = live[s] ∩ Derivable`, with the lifecycle view supplied by the
realization. **T4** gives *persistent until legitimately changed*; **T4'** gives
the second exit — a new challenge shrinks what is derivable, so the enforcement
target moves and a consumer that cached it would be wrong.

`AuthorityView` and `NormView` are projections under a consumer-supplied
classifier. `cases.force_bearing` is the record where the norm projection is a
real set: one injunction legitimately superseded, one manufactured beside it, and
the frontier holds the successor while the manufactured one is live and outside
it.

## The three interfaces

```text
legitimate    entitled                  G |- y, under coverage
accountable   answerable                the account layer, and T5
serviceable   sustainably enforceable   bounded-lifetime liability
```

Independent, and the frame carries no liability field. A legitimate norm can be
unenforceable, and the enforcement API says so itself: on exhaustion "force is
withheld, nothing is spent, the endorsement keeps its normative standing."

## Contents

- `LEGITIMATE_EVOLUTION.md` — the frame, the spine, the theorems, the realization,
  and the exercise-identity prosecution.
- `CROSS_PROCESS_INTERFACE.md` — what one process receives and may infer.
- `CONSUMER_TEST.md` — the deference and corrigibility substitution, and the
  negative test with the architecture deleted.
- `TRADERIZATION_CONSUMER.md` — the enforcement substitution, and the one theorem
  that is missing.
- `COUNTERMODELS.md` — every axiom prosecuted; the withdrawn claims are §§1-5.
- `THEOREM_MAP.md` — every claim graded, withdrawals first.
- `src/` — `frame.py` (the interface, the theorems, and the rejected rule),
  `ri_frame.py` (the realization, under either exercise identity), `warrant.py`
  (seven registers with no ledger), `cases.py` (the records the Carroll round did
  not have).
- `tests/` — 59 cases. `python3 tests/run.py`.

## What this does not establish

`THEOREM_MAP.md` carries the list; four matter most.

No Lean and no registered claim. The realization theorem is a paper argument from
Reflective Integrity's own statements, and those are themselves unregistered.

Coverage is a hypothesis nobody discharges. An external process satisfying every
axiom with a challenge set that names almost nothing is certified, and the Carroll
round's unlinked-episode witness is now visibly a coverage failure rather than a
caveat.

Pre-state-blindness survives the prosecution. Effect identity repairs `C28` and
`cases.partial_effect` shows it does not repair the general case — the condition
is needed under either identity, and it is now required by two consumers rather
than one.

The account layer's abstraction is the weakest part. `warrant.py` realizes it, but
the realization was written to match rather than found independently.

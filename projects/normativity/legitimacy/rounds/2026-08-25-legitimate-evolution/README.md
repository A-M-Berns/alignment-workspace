# Legitimate evolution and cross-process recognition

Status: **specification, reference models and a prosecution record;
unregistered.** All names are provisional under `AGENTS.md` §6. Nothing here is
Lean-checked and no claim is registered.

## Verdict

LEGITIMACY-THEOREM-COMPRESSED — the raw lifecycle is replaced by a legitimate replay indexed by an audit context; an unauthorized revocation is a no-op; authorization of the exact exercise is separated from grounding of the authority; legitimate influence no longer has to survive its own removal; declared-dependency factorization is precise and falsifiable in two ways; and finite grounding, no-laundering and hidden-state noninterference are proved from local hypotheses each of which fails a countermodel when dropped.

Four reservations, all in `THEOREM_MAP.md` and `COUNTERMODELS.md`.

**The substantive content is in the parameters.** `Permit` and `ProvOK` carry
what legitimacy actually says; what is proved here is structural. That is the
honest division and it is stated rather than disguised.

**Coverage is still undischarged.** `depends` is supplied from outside, a
record's own episodes cover by construction, and this is the hole that has
survived every reformulation the round has tried.

**Recognition transport is still an axiom**, and now carries four parameters
rather than two: base, authorization semantics, threat class, audit context.

**Neither consumer theorem is provable yet.** Deference needs an index on the
grade; enforcement needs bounded-lifetime liability.

## What replaced what

```text
                     before                         now
state         raw_live ∩ Derivable          L(alpha, s), replayed from G
judgment      does the edge survive q       did prior authority permit this edit
identity      standings and derivations     occurrences, tagged by issuing edit
time          one index                     historical time and audit time
axioms        L0-L4 + coverage + L5-L8      H1-H6
```

The previous succession calculus was the scaffold. It found the right questions —
licences must be grounded, jurisdiction is missing, coverage is a hypothesis —
and the object underneath is smaller.

## The theorem

```text
L(alpha, 0)    = G
L(alpha, s+1)  = apply(L(alpha, s), e_s)   if Valid_alpha(L(alpha, s), e_s)
                 L(alpha, s)               otherwise
```

```text
H1 mediated mutation      state moves only by applying an edit
H2 fresh occurrence       an edit issues occurrences nobody has issued
H3 prestate grounding     a valid edit's grounds are authorities of the pre-state
H4 permit soundness       a valid edit is one its grounds permit, for this edit
H5 declared factorization same declared view, same verdict and same effect
H6 provenance adequacy    valid implies ProvOK, and ProvOK reaches Xi
```

```text
G1 finite grounding       a finite tree to G, historical index descending
G2 no self-ratification   no edit is grounded in what it issues
G3 no laundering          a rejected occurrence never becomes legitimate
G4 noninterference        hidden state cannot move the legitimate state
G5 persistence            until a valid edit disposes it
G6 revisability           content is unconstrained
```

## The three attacks that forced it

**An unauthorized revocation used to work.** `office.rogue_revocation`: a rogue
authority is correctly refused, and the norm it revokes leaves the frontier
anyway, because the raw lifecycle was a conjunct. The persistence theorem
reported no violation while it happened. An attacker who could not add to the
enforcement target could still subtract from it.

**A grounded warrant used to do anything.** `office.unauthorized_scope`: a fiscal
warrant legislating on safety, with impeccable grounds and provenance, admitted.
The calculus checked that the licence was derivable and never what it was for.

**Being persuaded used to count against you.** `office.persuasion`: remove Bob's
argument and Alice's revision does not happen, and challenge survival scored that
as dependence. A legitimacy theory that cannot let an agent be argued into a
revision is not describing the learning the programme exists to describe.

## Occurrences, not contents

An occurrence is *this* grant, tagged by the index of the edit that issued it.
That one choice makes freshness free — so unique issuance is not an axiom and the
question the previous pass argued about does not arise — makes no-laundering
true, and lets a later clean act adopt the very content a rejected act proposed.

## The surprise in audit contexts

Tightening `alpha` can put **more** in force, because the edit it invalidates was
a repeal. The previous branch met this as the challenge operator being neither
monotone nor composable and could only record it; here it is a one-line
consequence, which is the clearest sign the object was wrong before.

## Contents

- `LEGITIMATE_EVOLUTION.md` — the canonical theorem: the object, H1-H6, G1-G6,
  the realization, and what the compression cost.
- `CROSS_PROCESS_INTERFACE.md` — what a recognizer receives and must be told.
- `CONSUMER_TEST.md` — deference and corrigibility.
- `TRADERIZATION_CONSUMER.md` — enforcement, and the one theorem still missing.
- `COUNTERMODELS.md` — every hypothesis prosecuted; withdrawals are §§1-5.
- `THEOREM_MAP.md` — every claim graded, withdrawals first.
- `src/` — `replay.py` (the theorem), `ri_frame.py` (the record realization),
  `office.py` (a constitution and its gazette, importing nothing else of ours),
  `cases.py` (the records the Carroll round did not have).
- `tests/` — 46 cases. `python3 tests/run.py`.

## What this does not establish

No Lean and no registered claim; the realization is a paper argument from
Reflective Integrity's own unregistered statements.

The theorems are not deep. G3 and G5 are short, and the ontology did their work.
The defence is that they were false or missing in the previous object, and that
each fails when its hypothesis is dropped — checked, not asserted.

Coverage is a hypothesis nobody discharges, and it is now the only place where a
process satisfying every axiom can still be certified against a threat it never
looked at.

Reflective Integrity has no jurisdiction on an authority, so **H4** is vacuous on
a record whose authority is a bare `PAuth`. The abstraction exposed that; it is a
gap in the architecture rather than in the interface, and nothing here fixes it.

# Answerable Revision

Status: **specification, reference models and a prosecution record;
unregistered.** All names are provisional under `AGENTS.md` §6. Nothing here is
Lean-checked and no claim is registered.

## Verdict

ANSWERABLE-REVISION-SURVIVES — standards may change and reasons incurred under them remain answerable, including when the standard revised is the one that promoted the reason, and including when the reason is about a warrant. The reflective case needs no meta-hierarchy: a warrant's target is an ordinary identifier that may name a warrant, and the module contains no level or rank notion at all. The honest qualification is that most of the theorem is inherited — promotion puts a reason in the frozen package's opens, incurred never shrinks, and A1 lets a claim leave the outstanding set only through an accepted resolution, while a warrant revision is not a resolution and appears in neither fold — so the closure argument is three lines. The round's own content is one premise, promotion permanence: what was promoted at t is a function of the state at t. A process that re-derives its own past under present standards violates it, and the frozen package would not notice, because its premises govern how claims leave rather than whether they arrive; the closure theorem, A1 and Grounded Replay are all clean on that history while the reason simply never exists. The second piece of content is separating historical validity from current endorsement, which lets a process say that something really was a reason it incurred and that it now rejects its force, while forbidding the claim that because standards changed there never was an answerability relation. The boundary is that Answerable Revision begins at promotion and cannot reach behind it: a warrant that narrows itself before a criticism can be promoted is legitimate under every premise here, which is the same boundary the improvement round found one level down and is some evidence it is the real boundary of this family.

## The question

The round below this one asked what happens when a *repair* is withdrawn after it
has been demonstrated. This one asks what happens when the **standards deciding
what counts as a reason for revision** are themselves revised.

```text
P_t       the substantive policy or procedure
Lambda_t  the evaluator or audit standard
W_t       the comparison warrant: what evidence may count as a reason
```

All three may legitimately change. The invariant is not a fixed target:

> **Standards may change; reasons incurred under them remain answerable.**

## What is claimed

At the strict pre-state of `t`, with `W` standing, `E` admissible and
`Promote(W,E) = rho`: for every later `s`, `rho` is incurred, and is outstanding
or was resolved — however `P`, `Lambda` and `W` change in between.

The proof is three lines of inheritance from frozen Legitimate Evolution. The
round's own content is elsewhere:

**Promotion permanence.** What was promoted at `t` is a function of the state at
`t`. A process that re-derives its past under present standards violates this,
and the frozen package would not notice — its premises govern how claims *leave*
the outstanding set, and this attack prevents them from arriving.

**Historical validity is not current endorsement.** These are separate
predicates and they diverge. A process may say *this really was a reason we
incurred, and we now reject its force*. It may not say *our standards changed, so
there never was a reason*.

## What the prosecution found

The reflective case works. A warrant admitting comparisons about warrant
protocols promotes a reason criticising itself; the warrant is then replaced and
the reason survives. No meta-warrant is required, which was the failure mode
worth watching for.

The improvement round is recovered as one warrant — its demonstration threshold
is a promotion rule, its withdrawal challenge an ordinary instance — and so is
its boundary. The specialization is **one-directional**: this round begins at
promotion and inherits nothing about what happens while a repair is live.

## Contents

- `ANSWERABLE_REVISION.md` — theorem, promotion interface, AR1-AR10, boundaries,
  the improvement-round specialization, freeze recommendation.
- `src/warrant.py` — warrants, promotion, the theorem over frozen LE.
- `src/cases.py` — AR1-AR10 and the specialization.
- `tests/` — 29 cases. `python3 tests/run.py`.

## What this does not establish

No Lean and no registered claim.

That criticism reaches promotion at all. A warrant may narrow itself first, and
that is legitimate here — the named frontier is reflective openness.

That a defeat is any good. A bare refusal answers a reason structurally.

Responsive Revision, the quantitative follow-up. Not claimed and not built.

Anything about RI realization: promotion is not mapped to a `ReasonOcc`, and no
event kind was added or proposed.

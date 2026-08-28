# Provenance

## Frozen inputs, read and not modified

```text
rounds/2026-08-25-legitimate-evolution/src/replay.py   imported unchanged
rounds/2026-08-25-legitimate-evolution/src/answer.py   imported unchanged
```

A test asserts by AST parse that only `Duties`, `Ob`, `Frame`, `Edit`, `Occ`,
`BASE`, `incurred` and `outstanding` are read from them.

The two rounds above are **not imported**. Their results are cited and their
boundary is where this round begins; no code is called.

## A correction to a merged round

This branch also carries a qualification to
`rounds/2026-08-28-answerable-revision`. That round's document listed *a Due
obligation* among four things that must not collapse, while its reference
realization wired every promoted reason straight into frozen `opens`, which is
incurrence. The document now says that the fixtures adopt
`promotion -> answerability incurrence` as a canonical constitution, and states
the two claims the generic theory actually supports. No code behaviour changed
and its 29 tests are unaffected.

The same correction is applied pre-emptively here: `service.duties` says in its
own docstring that `registered(c) -> ConsiderationDue(c)` is a canonical
constitution rather than the generic theory.

## No external sources

This round fetched nothing.

## New names introduced

All provisional under `AGENTS.md` §6.

*registered challenge*, *procedural standing*, *challenge episode*,
*adjudication terms*, *episode pinning*, *prospective revision*, *explicit
transfer*, *registration permanence* (C1), *episode pinning* (E1), *temporal
integrity* (D1), *inferential integrity* (D2), *reflective non-ad-hocness* (named,
not solved), *adjudicative opportunity*, *service*, *starvation debt*,
*consideration claim*.

## What was computed rather than asserted

Every row of `CHALLENGE_SERVICE.md` §G is produced by `src/cases.py` and
re-derived by the tests. The two claims most at risk of being asserted are both
checked: that the frozen package cannot see a registration rewrite, and that the
indefinite-starvation docket satisfies every qualitative premise while `S1`
fires. The indistinguishability observation is checked by running every predicate
in the module against both worlds and comparing outputs.

# Provenance

## Frozen inputs, read and not modified

```text
rounds/2026-08-25-legitimate-evolution/src/replay.py   imported unchanged
rounds/2026-08-25-legitimate-evolution/src/answer.py   imported unchanged
```

`tests/test_revision.py::TestFrozenLEIsUntouched` asserts by AST parse that only
`Duties`, `Ob`, `Frame`, `Edit`, `Occ`, `BASE`, `incurred` and `outstanding` are
read from them.

The merged improvement round is on the path but is **not imported**: this round
names no regret quantity, and a test asserts that too. It is recovered as a
special case in `cases.pr60_as_a_warrant`, which reconstructs its promotion rule
rather than calling its code.

## No external sources

This round fetched nothing. It is semantic and theorem-design work over the
frozen package, and every claim is either inherited from it, proved in three
lines, or exhibited by a fixture in `src/cases.py`.

## New names introduced

All provisional under `AGENTS.md` §6.

*comparison warrant* (`W`), *warrant standing*, *admissibility*, *promotion*,
*revision reason*, *promotion permanence* (P1), *historical validity*, *current
endorsement*, *retroactive erasure*, *self-authorising promotion*, *pre-promotion
self-sealing*, *answerable revision*, *reflective openness* (named as a frontier,
not defined).

## What was computed rather than asserted

Every row of `ANSWERABLE_REVISION.md` §F is produced by `src/cases.py` and
re-derived by the tests. The claim that the closure theorem alone does **not**
catch retroactive invalidation is asserted by a test that checks the theorem,
frozen `A1` and Grounded Replay are all clean on that history while the reason is
absent from the incurred set.

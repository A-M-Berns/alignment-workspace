# Defeat Principle Landing, Horty Check, and Standing Repair

**Round of 2026-09-03.** Closes two of the previous round's outstanding maintainer
actions, performs the prior-art check `PRIORITIES.md` item 77 asks for, and repairs a
defect in that round's Lean that its report did not flag.

The **Defeat Principle is settled** as of this round: `DECISIONS.md`, 2026-09-03,
maintainer ruling. Nothing here is a registered claim.

## Read in this order

| file | what is in it |
| --- | --- |
| [`REPORT.md`](REPORT.md) | verdict, five declared deviations, what is not established, outstanding maintainer actions |
| [`HORTY.md`](HORTY.md) | the prior-art check: five findings, and an explicit account of which texts were and were **not** read |
| [`STANDING_REPAIR.md`](STANDING_REPAIR.md) | the vacuous `contested` clause, the repair, and laundering reproved from the standing side |
| [`WITNESS.md`](WITNESS.md) | the first Lean inhabitant of `Disciplined`, and one that fails by exactly one clause |

## Three results in one line each

- **Horty cannot express `MayDispose`** — not because a priority ordering fails to
  license the loser, but because his theory says what to *conclude*, not what is
  *owed*, so there is no account for a licence to operate on.
- **Exclusion is challengeable in-system**, so an exclusionary reason is a `dispose`
  without a successor and not a `settle`. The round's two summands survive the check.
- **The standing half of D3 was vacuous**, and every laundering result in the previous
  round in fact rested on one clause while appearing to rest on two.

## What the check rests on

**Horty's own text**, supplied mid-round: *Reasons as Defaults*, Draft #2, 2006 — the
paper the 2012 book develops, carrying the full apparatus. All five findings are
checked against it; none was withdrawn when it arrived and two got sharper. The **2012
book** is still unread, so a claim about what the *book* says is not licensed here.
`HORTY.md` §0 records both states of the check rather than tidying the first away.

## Verify

    python3 tests/run.py                # 7 tests; the previous round's 24 also still pass
    cd ../../../../../lean && lake build Workspace.Normativity.Contrib.NormativeContinuity

The Lean lives in `lean/Workspace/Normativity/Contrib/NormativeContinuity.lean`
§§5.2, 5.4, 5.7–5.9.

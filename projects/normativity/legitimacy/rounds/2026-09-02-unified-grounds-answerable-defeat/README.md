# Unified Grounds and Answerable Defeat

**Round of 2026-09-02.** Answers `PRIORITIES.md` item 77 — what licenses authorized
disposition. Everything is conditional on the **Defeat Principle**, this round's
hypothesis: *no participant extinguishes a debt; a participant may pay it or move it
onto the grounds for saying it is not owed; only settlement extinguishes.*

**Nothing here is a registered claim.** The Lean results are sorry-free and
axiom-audited; the rest is paper-derived and test-supported.

## Read in this order

| file | what is in it |
| --- | --- |
| [`REPORT.md`](REPORT.md) | the verdict, the two findings, six declared deviations, what is not established, outstanding maintainer actions |
| [`GROUNDS.md`](GROUNDS.md) | the diagnosis (no type held a disposal's grounds), the unification, and the two requirements that did **not** re-derive |
| [`DEFEAT.md`](DEFEAT.md) | answerable disposal D1–D3, no-self-grounding, laundering, and the coalition attack |
| [`LOADS_AND_MASS.md`](LOADS_AND_MASS.md) | one rule across the carrier and service layers |
| [`THEOREMS.md`](THEOREMS.md) | T1–T5 with what is proved, where, and how strongly |
| [`COUNTERMODELS.md`](COUNTERMODELS.md) | twelve hostile fixtures and the clause that refused each |

## The result in one line

One ground type `Q ⊕ S` replaces two traces; `StandingTrace`, `Licensing` and the
inductive `Grounded` are deleted as primitives and re-derived from ancestry; disposal
gets a licence predicate with a soundness theorem; and **separation stops one
participant but not two**.

## Verify

    python3 tests/run.py                             # 24 tests, exact rationals
    cd ../../../../../lean && lake build Workspace.Normativity.Contrib.NormativeContinuity

The Lean lives in `lean/Workspace/Normativity/Contrib/NormativeContinuity.lean` §5;
§2 and §4.2 of that file were deleted by this round.

# Decision theory

This line specifies and tests what a computable agent combining logical induction (LI)
with bounded inductive rationality (BRIA) must satisfy for the combination to count as
an advance in logical-induction-based decision theory, and later rounds will judge
candidate constructions against that specification.

## Start here

- `rounds/2026-09-29-li-bria-synthesis-spec/PROBLEM_STATEMENT.md` — the objective, the
  eight candidate requirements examined, the minimum credible synthesis, the stronger
  targets, and the acceptance checklist.
- `rounds/2026-09-29-li-bria-synthesis-spec/TEST_SUITE.md` — the diagnostic benchmarks,
  each with its environment, timeline, predictor access, comparator, guarantee, negative
  control and the requirement it diagnoses.
- `rounds/2026-09-29-li-bria-synthesis-spec/AUDIT.md` — prior approaches and what each
  guarantees, the compatibility of the requirements with one another, and the
  specification choices still open.

The sources of record for the two components are Garrabrant et al., *Logical
Induction* (arXiv:1609.03543), and Oesterheld, Demski and Conitzer, *A Theory of Bounded
Inductive Rationality* (TARK 2023); both are cited in `wiki/Sources.md`.

## Relation to the deference line

Continuation BRIA — bounded inductive rationality lifted to temporally extended
continuations under a constitutional execution wrapper — lives in the deference line,
at `projects/deference/rounds/2026-09-08-continuation-bria/` with the canonical
statement on `wiki/Continuation-BRIA.md` and its Lean algebra in
`lean/Workspace/Deference/Contrib/ContinuationBRIA.lean`.  It stays there: it is
corrigibility's learning layer, consumes the deference line's gate, and is cited by
pinned path from the wiki, the round index, the decision ledger and the priority items.
This line consumes its block contract and weighted criterion as the temporally
extended form of BRIA and does not restate them.  The coupling of BRIA's claims with
the market is `PRIORITIES.md` item 102; this line's specification says what that
coupling must deliver.

- Completed rounds: `rounds/`
- No claims registry yet: the line has registered nothing.

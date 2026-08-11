# Contributing

**Quality here is enforced by machine-checkable gates, not by trust.** You do not
need to be known to anyone to contribute. Your pull request either passes four
gates or it does not, and the gates are the same ones the author's own work
passes.

## Run everything locally first

```sh
python3 tests/run.py                              # gate 1: every project's tests
cd lean && lake exe cache get && lake build       # gate 2: Lean, sorry-free
python3 tests/audit_axioms.py                     # gate 2: axiom audit
python3 tests/check_frozen.py                     # gate 3: frozen integrity
cd frozen/consolidation_aug9 && python3 tests/run.py   # gate 4: foundations
```

CI runs exactly these. If they pass locally on a clean checkout, they pass in CI.

## What a contribution must contain

**A theorem** ships as four things:

1. a **statement** — in a `THEOREMS.md` or a docstring — that a reader can
   evaluate without reading the implementation;
2. an **implementation**, in exact rationals (`fractions.Fraction`; floats only
   in clearly-marked exploration code, and no result may depend on one);
3. a **test** that recomputes the claim exactly; and
4. a **necessity witness for each hypothesis** where feasible — a displayed
   instance showing that dropping the hypothesis breaks the result.

Where a necessity witness is not feasible, say so in the statement. An
unexamined hypothesis is a gap, and naming it is not a failure.

**Lean** ships building and auditing clean: no `sorry`, `#print axioms` at the
end of the file, and every result auditing to
`[propext, Classical.choice, Quot.sound]` and nothing else. **External theory
enters as named hypotheses of the statement that uses it — never as an `axiom`
declaration.** An `axiom` standing in for a citation is the specific failure the
gate exists to catch.

**A witness** ships as the exact instance and the check that verifies it. "There
is a counterexample" is not a witness; the counterexample is.

## Where to find work

`OPEN_PROBLEMS.md`. It is the source of truth and it tags difficulty: **[entry]**
items need no new mathematics, **[substantial]** items are scoped results,
**[open]** items may be impossible. GitHub issues mirror that file, not the
reverse — if the two disagree, the file is right.

## The two hard rules

**1. Nothing in `frozen/` changes.** Frozen inputs are read-only, checksummed,
and cited by path. CI recomputes their digests and fails on drift, and refuses
any pull request touching `frozen/` unless the same pull request updates
`frozen/MANIFEST.md`. A frozen input that needed changing was not frozen: the
honest move is a new dated entry beside the old one.

**2. Contributors do not coin permanent names.** Naming is the author's.
If your work needs a name for something new, use an obviously provisional one,
mark it, and list it in the pull request's "new names introduced" field. This is
not bureaucracy — a name that ships is very hard to change later, and the
program's vocabulary has already been through one painful retirement.

## Citation integrity

No unverified identifiers. Cite content inline, or cite a claim identifier
against a checksummed frozen tree. **Never a remembered label.** If you cannot
verify a citation against the source it names, state the content directly and say
that the label did not check out — that has caught real errors here, including
labels attributed to sources that do not contain them.

## Review

The author reviews everything (`CODEOWNERS`). The gates decide correctness; review
decides fit, naming, and whether a result belongs in the program. A green PR is
not automatically merged, and a red one is not argued with.

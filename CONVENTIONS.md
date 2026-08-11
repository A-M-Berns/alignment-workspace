# Conventions

House standards. These are not suggestions; a round that departs from one says
so in its report and explains why.

## 1. Exact arithmetic

All theorem-bearing Python uses exact rationals — `fractions.Fraction`. Floats
appear only in code clearly marked as visualization or exploration, and no
result depends on them. A number that appears in a claim is exact, and the test
that recomputes it compares exactly.

## 2. What a theorem ships as

Every theorem ships as four things:

1. a **statement**, in a `THEOREMS.md` or in a docstring, that a reader can
   evaluate without reading the implementation;
2. an **implementation**;
3. a **test**; and
4. a **necessity witness for each hypothesis** where one is feasible — a
   displayed instance showing that dropping the hypothesis breaks the result.

Where a necessity witness is not feasible, the statement says so rather than
leaving the hypothesis unexamined.

## 3. Runners

One command per project, and one repo-level runner that runs them all:

```sh
python3 tests/run.py        # repo level: every project, plus the Lean gate
```

A project's runner is self-contained: it does not reach outside its own
directory except to read `frozen/`.

## 4. Frozen inputs are immutable

Anything under `frozen/` is read-only, checksummed in
`frozen/FROZEN_INPUT_CHECKSUMS.json`, and referenced — never edited, never
unpacked into `projects/`. A frozen input that needed changing was not frozen;
the honest move is a new dated entry beside the old one.

## 5. Citation integrity

No unverified identifiers. Cite content inline, or cite a claim identifier
against a checksummed frozen tree. **Never a remembered label.** If a citation
cannot be verified against the source it names, state the content directly and
record the failure — this has caught real errors more than once, including a
label that did not exist in the source it was attributed to.

## 6. Naming is the author's

Agent rounds **flag naming decisions for the author and do not coin permanent
names**. A round that needs a name for something new uses an obviously
provisional one, marks it, and lists it in the round's report under decisions
awaiting the author.

## 7. Dispatch provenance

Every agent round's prompt and report live under
`prompts/YYYY-MM-DD-round-name/` — `PROMPT.md`, `REPORT.md`, and any decision
items — committed with the work they describe. A round whose prompt is not in
the tree did not happen, as far as the repository is concerned.

## 8. Lean discipline

- **Sorry-free gate.** No `sorry` reaches a committed file; the runner fails on
  one.
- **Every file ends with `#print axioms` lines** for the results it establishes.
- **Results audit to `[propext, Classical.choice, Quot.sound]`.** Anything else
  is a finding, not a detail.
- **External theory enters only as named hypotheses.** Facts from the Logical
  Induction paper, from the corpus, or from any other body of work are taken as
  explicit hypotheses of the statement that uses them — **never re-asserted as
  axioms**. An `axiom` declaration standing in for a citation is the specific
  failure this rule exists to prevent.
- One Lake project, `lean/`, library `Workstudio`, per-line namespaces.
  Formalized-Agent-Foundations is pinned by commit; Mathlib and Foundation
  arrive through it, so the stack stays consistent.

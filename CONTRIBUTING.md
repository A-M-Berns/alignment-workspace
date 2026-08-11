# Contributing

## For readers

If you have just arrived, five things.

**1. Verify before you trust.** Four gates run in CI and all four run locally,
with the commands in the next section. Every claim in this repository is either
machine-checked by them or **explicitly labelled otherwise** — the frozen
consolidation, for instance, separates machine-checked results from hand-derived
ones from transcribed ones from a reading audit, and says which is which per
claim.

**2. Read provenance before you cite.** Every artifact declares an origin class:
`human`, `llm-reviewed`, or `llm-unreviewed`. The last one means exactly what it
says — LLM-generated and not yet author-reviewed. It is allowed here, because
this is a working repository and a label that lies is worse than an honest one,
but it is never hidden. See `AGENTS.md`.

**3. Documentation comes in two registers by design.** The verification register
is precise and dense, for auditing and for agents. The human register explains
what was shown and why it matters, in plain language. **If you are a person,
start with the human-register document** — it is not a summary of the other one,
it is a different account of the same work.

**4. The two hard rules** are frozen-immutability and no-permanent-naming.
Nothing under `frozen/` changes, ever; and names are the author's to set.

**5. Disagreement is welcome, and it has a format.** Not an opinion: a
counterexample, a failing test, or a precise objection filed as an issue against
a named ledger item. That is not gatekeeping — it is the same standard the
repository's own results are held to, and a good counterexample is worth more
here than agreement.

---

**Quality here is enforced by machine-checkable gates, not by trust.** You do not
need to be known to anyone to contribute. Your pull request either passes four
gates or it does not, and the gates are the same ones the author's own work
passes.

## Run everything locally first

```sh
python3 tests/run.py                              # gate 1: every project's tests
python3 -m checkers.run --self-test               # the house harness's own tests
python3 -m checkers.run                           # every registered claim
python3 tests/path_gate.py                        # which layer your files are in
python3 tests/conservativity.py                   # no new axioms; spec shape held
cd lean && lake exe cache get && lake build       # gate 2: Lean, sorry-free
python3 tests/audit_axioms.py                     # gate 2: axiom audit
python3 tests/check_frozen.py                     # gate 3: frozen integrity
cd frozen/consolidation_aug9 && python3 tests/run.py   # gate 4: foundations
```

CI runs exactly these. If they pass locally on a clean checkout, they pass in CI.

## What you can contribute

Every file in this repository belongs to exactly one layer, and which one decides
what you may do to it.

**The proof layer is open to you.** Lean proofs of statements of record and new
lemmas in contribution namespaces; witnesses and domain parameters; documentation
of contributed results.

**The specification layer is not.** Definitions and statements of record, the
checker harness, CI, toolchain pins, the axiom allowance, budgets, and the
governance documents. A `path-gate` CI job fails any non-maintainer pull request
that touches one. There is no trusted-contributor tier that bypasses it — if your
work genuinely needs a specification change, open an issue proposing it.

Identity is never a factor in a proof-layer verdict. Anonymous and pseudonymous
contributions are fine.

### Nothing enters the record unasked

**Every registered claim answers a filed `OPEN_PROBLEMS.md` item.** Propose new
items as issues; filing is a maintainer act. An unsolicited-but-correct
contribution is not merged into the record — but the maintainer may file a
matching item and then accept it, so good work is not wasted, only sequenced.

### Submission format, by claim class

| you are claiming | you submit | what adjudicates it |
|---|---|---|
| **a Lean theorem** | the proof, in a contribution namespace, plus a term inhabiting its full hypothesis package | the Lean kernel, the axiom audit, and the nonvacuity check |
| **an existential, counterexample, sharpness or necessity witness** | **data** — the instance — plus the house checker id and the property parameters | `checkers/witness.py`, which you did not write and cannot change |
| **a finite universal claim** | **domain parameters** only | `checkers/enumeration.py`, which generates the domain itself |
| **anything over an infinite domain, or sampled** | the work, registered as `test-supported` or `conjectured` | nothing — it is **not citable as proven**, and its natural fate is a Lean port |

**You never ship the verifier for a claim of record.** A test file of your own
may support exploration, but the thing that certifies a registered claim is
always a house checker. If a contributor supplied the enumeration, the
contributor would be certifying the claim — the enumeration *is* the proof.

A theorem also does not enter the record without an **inhabitation witness**: a
concrete instance satisfying all its hypotheses. A theorem whose hypotheses
nothing satisfies is not false, it is empty, and that difference is invisible to
the kernel.


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

*(Stated above for readers; here is what they mean for a pull request.)*

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

## Sign your commits

Every commit carries a Developer Certificate of Origin sign-off:

```sh
git commit -s          # adds the Signed-off-by line
git commit --amend -s  # fixes one you forgot
```

The sign-off asserts the DCO in [`DCO`](DCO) — that you have the right to submit
the work under this repository's licence. CI checks every commit in a pull
request.

**Pseudonymous sign-offs are accepted.** The maintainers know that is a thinner
assertion from a pseudonym than from a known person, and accept it deliberately:
Apache-2.0 §5 is the primary rights mechanism and the DCO is the recorded
assertion on top of it. Identity is not a factor in a proof-layer verdict, and
this does not make it one — the gate checks that an assertion was made, not who
made it.

## Citation integrity

No unverified identifiers. Cite content inline, or cite a claim identifier
against a checksummed frozen tree. **Never a remembered label.** If you cannot
verify a citation against the source it names, state the content directly and say
that the label did not check out — that has caught real errors here, including
labels attributed to sources that do not contain them.

## Review

The author reviews everything (`CODEOWNERS`). The gates decide correctness; review
decides fit, naming, provenance labelling, whether both documentation registers
are present, and whether a result belongs in the program. A green PR is
not automatically merged, and a red one is not argued with.

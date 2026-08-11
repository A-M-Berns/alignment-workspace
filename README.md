# alignment-workstudio

The working monorepo for the Berns–Demski research program: models, proofs, and
dispatch provenance for two research lines, formalized against
[Formalized-Agent-Foundations](https://github.com/A-M-Berns/Formalized-Agent-Foundations)
as a pinned dependency.

This file points; it does not contain. Research content lives under `projects/`
and `frozen/`.

## The two lines

**Leverage** — the normativity and answerability program: what a record must
show for a learner's normative state to be accountable, and what a world-channel
must satisfy before its writings acquire operative force. Its authoritative
record is frozen; new rounds land in the workspace.
→ `projects/leverage/`

**Delegation** — the deference and corrigibility program: when a bounded agent
should defer, what deference costs, and what an agent's own deliberation must
look like for deference to be safe rather than merely obedient. Its recorded
starting point takes the Logical Induction theorems as named hypotheses; the
leverage line and the pinned dependency sit on the other side of that gap, which
is why both lines share this repository.
→ `projects/delegation/`

## Layout

```
projects/     one directory per research line; rounds land here
lean/         one Lake project, library Workstudio, per-line namespaces
frozen/       immutable checksummed inputs, referenced and never edited
prompts/      every round's prompt and report, committed with the work
tests/        the repo-level runner
```

`CONVENTIONS.md` is the house standard — exact arithmetic, what a theorem ships
as, frozen inputs, citation integrity, and the Lean discipline. `DECISIONS.md`
is the dated decision ledger, with what is still awaiting the author at the top.

## Running the tests

```sh
python3 tests/run.py                    # every project, frozen digests, Lean gates
WORKSTUDIO_LEAN=1 python3 tests/run.py  # the above, plus `lake build`
```

The repo-level runner verifies the frozen-input digests, enforces the Lean
sorry-free and `#print axioms` gates, and runs each project's own runner. Lean
compilation is opt-in because it wants a toolchain and a warm cache.

## Building the Lean

```sh
cd lean
lake exe cache get     # Mathlib oleans
lake build
```

One Lake project. Formalized-Agent-Foundations is pinned by commit in
`lakefile.toml`; Mathlib and Foundation arrive through it, so the solver stack
stays consistent rather than being pinned three times and drifting. The
toolchain matches the dependency's exactly. `Workstudio/Smoke.lean` certifies
the chain compiles by reaching a real declaration in each of the three and
proving something trivial against it.

# alignment-workspace

A working research repository on agent foundations, run mostly by AI agents under
a maintainer's direction. Two research lines — what makes an artificial agent's
normative state accountable, and what makes deference to a principal stable rather
than merely imposed — together with their models, their Lean proofs, and the
record of every round that produced them, including the rounds that failed.

The organising problem is that **an agent can generate far more research than a
person can check.** What that costs is not wrong theorems — the Lean kernel
catches those — but wrong *readings* of correct theorems, and a state of play too
expensive to recover. So the repository is built to keep four things visibly
apart:

> what we are trying to show · what we have actually constructed · what blocks the
> gap · what a human has actually adopted

**Anyone can contribute, and quality is enforced by machine-checkable gates rather
than by trust.** Exact rationals, a theorem shipping as statement + code + test +
necessity witness, sorry-free Lean with axiom audits, one-command verifiers. A
pull request whose seven required checks pass merges itself. See
`CONTRIBUTING.md`.

## How work actually flows

A round is dispatched with a written prompt and returns a report, both committed
with the work. What it produces is challenged — by the kernel, by the house
checkers, and where the claim is load-bearing by an independent adversarial review
run in a fresh context. What survives is consolidated into the line's status
documents. A small number of things then receive maintainer judgment and are
recorded as dated decisions.

The interesting case is when that pipeline catches something, and it has twice.
The deference line's Stage III built a comparator, verified its Lean, and drew a
positive conclusion; an independent review found the comparator contained no
future agent at all. **The theorems were correct and the interpretation was
wrong.** The mathematics was kept under a corrected name, the positive reading was
withdrawn, and the follow-up round was not dispatched. Stage IV then failed in the
mirror-image way and, between them, located the obstruction as structural rather
than a sequence of mistakes.

That is the behaviour the repository exists to make cheap: a verified artifact and
an unendorsed interpretation are different things, and saying so should cost
nothing.

## Where to start

- **`RESEARCH_STATE.md`** — what each line is trying to show, what is built, and
  what blocks the gap. The shortest path to the current state.
- **`PRIORITIES.md`** — what needs doing, ranked, with a standing section for the
  questions where a good idea rather than more work is what is missing.
- **`projects/leverage/`** and **`projects/deference/`** — the two lines' landing
  pages.
- **`lean/`** — one Lake project, library `Workspace`, pinned to
  Formalized-Agent-Foundations and through it to Mathlib.
- **`DECISIONS.md`** — the dated ledger. Everything a human has actually ruled on,
  with what is awaiting the maintainer at the top.
- **`prompts/`** — every round's dispatch and report. History and evidence, not
  the current position.

`AGENTS.md` is the binding standards document, inherited by every dispatched
round. `PROVENANCE.md` records, per file, who generated it and whether a
maintainer has read it — the answer is almost always **no**, and that is the
honest label rather than a hedge.

## Verification

Clone, run these, and every claim in this repository is re-checked in front of
you:

```sh
python3 tests/run.py                                   # the project test runners
cd lean && lake exe cache get && lake build            # the Lean, sorry-free
```

`python3 tests/audit_axioms.py` additionally checks that every Lean result depends
on nothing beyond `propext`, `Classical.choice` and `Quot.sound`. CI runs all
seven jobs on every push and pull request, including re-running the leverage
consolidation's own verifier — so the repository continuously re-proves its
foundations rather than asserting them.

## The two lines

**Leverage** — the normativity and answerability program. What must a record show
for a learner's normative state to be accountable? It works out an objection
grammar, what survives when the vocabulary changes, what it costs to decline to
answer, and a **settlement interface**: the conditions a world-channel must meet
before what it writes acquires force. The world cannot be argued with, so the
move is to make the unarguable part as small and as explicitly labelled as
possible and prove what follows.

**Deference** — the deference and corrigibility program. When should a bounded
agent defer, what does deference cost, and what must its deliberation look like
for deference to be safe rather than obedient? Its recorded starting point takes
the Logical Induction theorems as named hypotheses; its own audit names the
complement as its largest gap, since the market and traders are unmodelled. The
leverage line and the pinned dependency sit on the other side of exactly that
gap, which is why both lines share this repository.

## Layout

```
projects/     one directory per research line; forward rounds land here
lean/         one Lake project, library Workspace, per-line namespaces
prompts/      every round's prompt and report, committed with the work
tests/        the repo-level runner and the gate scripts
checkers/     the house checker harness — the judge for computational claims
```

## License

**Apache-2.0** — see [`LICENSE`](LICENSE). One license for everything: code, Lean,
and prose alike.

Contributions are accepted under the same license: Apache-2.0 §5 makes a
contribution inbound-equals-outbound unless a contributor says otherwise in
writing. On top of that, every commit carries a Developer Certificate of Origin
sign-off — see [`DCO`](DCO) and `CONTRIBUTING.md`. Pseudonymous sign-offs are
accepted.

Upstream: Mathlib and Formalized-Agent-Foundations are Apache-2.0, and Foundation
is Apache-2.0, so the whole solver stack is under one license.

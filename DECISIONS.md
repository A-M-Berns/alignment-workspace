# Decisions

Dated decision ledger. Settled decisions are recorded here and are not
re-litigated; anything awaiting the author is an explicit stub, and stubs are
listed at the top of each round's report until they are closed.

## Awaiting the author

- **Repository visibility and license.** The repository is currently **private**,
  inherited from its predecessor rather than chosen for this scope. No license
  file is present. Both are the author's to set.
- **Whether the leverage frozen trees are registered now or at the next leverage
  round.** `consolidation_aug9/` is registered and checksummed; the question is
  whether anything else from that line — earlier consolidations, the source
  tree's archived material — should join it now.
- **Lean library and namespace names.** `Workstudio`, with
  `Workstudio.Delegation.*` and `Workstudio.Leverage.*`, is what this round
  scaffolded because the prompt named it. Renaming later is cheap now and
  expensive after the first real development lands.
- **Which delegation documents are canonical.** `projects/delegation/notes/` is
  seeded with a pointer rather than with documents; see the note there.

## Settled

### 2026-08-10 — repository name and scope

**alignment-workstudio**: the working monorepo for the Berns–Demski research
program. It holds multiple research lines, exact-arithmetic model work per line,
one shared Lean project, frozen inputs, and dispatch provenance. Two lines at
the outset: **leverage** (the normativity and answerability program) and
**delegation** (the deference and corrigibility program).

Created by renaming and repointing the existing repository rather than starting
fresh, so its history is preserved: the August 9 consolidation and its two
freeze tags predate this scaffolding and remain reachable.

### 2026-08-10 — Formalized-Agent-Foundations pinned by commit

Pinned at `1fffea44eece253cda1722568a3adfe34e822f03` — the current `main` of
https://github.com/A-M-Berns/Formalized-Agent-Foundations, whose most recent
change bumped its pinned dependencies and unforked Foundation, which is what
made it pinnable. Toolchain matched to FAF's exactly: `leanprover/lean4:v4.31.0`.

### 2026-08-10 — one Lake project, not one per line

A single Lake project at `lean/`, library `Workstudio`, with per-line
namespaces. The alternative — a project per research line — would have meant a
separate dependency pin and a separate toolchain per line, and the first time
the two lines shared a definition it would have meant a fourth package to hold
it. One project keeps the solver stack consistent by construction.

### 2026-08-10 — one dependency pinned, the rest inherited

Only FAF is pinned directly. Mathlib and Foundation arrive transitively through
it. Pinning all three independently would let this repository and FAF disagree
about Mathlib, which is the failure mode the single pin removes.

### 2026-08-10 — binding standards live in `AGENTS.md`

One document, read by agents and humans alike, replacing a separate conventions
file: agent tooling reads that filename automatically, so every dispatched round
inherits the standards without its prompt restating them. The reader-facing rules
became the opening section of `CONTRIBUTING.md` rather than a separate document.

Twelve standards, of which six are machine-enforced by the CI gates and the rest
are review matters; `AGENTS.md` §13 says which is which, so nobody mistakes a norm
for a gate. The standards: exact arithmetic; what a theorem
ships as; runners; frozen inputs immutable; citation integrity; naming reserved
to the author; dispatch provenance; and the Lean discipline — sorry-free,
`#print axioms` per file, results auditing to
`[propext, Classical.choice, Quot.sound]`, and external theory entering only as
named hypotheses rather than as axioms.

# Standing dispatch — the maintenance sweep (ruling of 2026-11-05)

Maintainer directive, in conversation, verbatim:

> I think we should maybe add to the automated maintenance any reorganization or anything
> that can be done to resolved automated friction issues that come up with minimal human
> input and like asking directly for the input when it's required

This document is the standing authorization the ruling of 2026-11-05 names
(`DECISIONS.md`, *the standing maintenance dispatch*). Each sweep is a round against it:
a dated directory under `prompts/` citing this file as its prompt, a `REPORT.md`, a
`state/rounds.json` entry, a `PROVENANCE.md` row.

## The sweep

1. Read `ATTENTION.md`'s *Workspace friction* section and the standing *Freshness audit*
   issue.
2. Take every item whose fix is **contained** (§14 of `AGENTS.md`): non-retroactive,
   confined to one gate or one document, shipped with its own null-input case. Record
   each as agent-decided, reversible, in `DECISIONS.md`; retire the friction item.
3. Convert every item whose fix would change a spec-layer rule into a **direct question
   to the maintainer**: one line stating what the decision turns on, delivered to them,
   with the entry appended to *Awaiting the author*.
4. Report an empty sweep as empty.

One pull request per sweep. **No auto-merge when the diff touches `checkers/` or
`.github/workflows/`** — the maintainer's merge is the human input point. Full local
gates (`python3 tests/run.py`) before the pull request opens.

# Attribution — 2026-10-02-graph-prototype

| | |
|---|---|
| Prompt author | Claude Fable 5.1 (Anthropic), from a design conversation with the maintainer, 2026-09-30 to 2026-10-02 (`PROMPT.md`, verbatim) |
| Executor | Claude Fable 5.1 (Anthropic), in Claude Code: five Workflow agents (spec, checker, fixtures, docs, cold review), then three single agents (repair, v1, fill) |
| Deliverables | `graph/` (protocol, README, design log, frame, policy, nodes, events, generated files), `checkers/graph.py`, `checkers/tests/test_graph.py`, the `graph/` section of `AGENTS.md` |
| Dates | 2026-10-02 |

## What the round did

Built the argument map's first version from the protocol the maintainer and
Claude designed over three days (rulings 1 to 34 of the maintainer's private
design ledger; the ones that bind here are restated in `graph/PROTOCOL.md`'s
Decided registers). `BUILD.md` is the implementation specification the checker
was written against; `REVIEW.md` is a cold read by an agent playing a
contributor who had seen only the shipped documents, whose findings drove the
repair pass; `FIXTURE-NOTES.md` is what the tests record about the starting
graph. The starting graph's numbers were written by an AI handle under the
maintainer's ruling that AI fills in numbers first and humans revise them; every
such number is marked in the views and enters the judgment ladder at its bottom
anchor.

## Register

`ci-only`. The maintainer ruled on the design in conversation and has not read
the code or the generated files for approval. The ranking is advisory; the
design log records every change to the design made in use, and the standing
expectation is that contributors revise it.

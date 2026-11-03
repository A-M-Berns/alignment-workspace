# Report — the assessment event

The ledger protocol gains `assessment`: a human's current stance on a node —
`support | dispute | uncertain | abstain`, on an aspect of `correctness | applicability |
framing | usefulness` — with the rationale required in `verbatim`, revision-bound through
the event's existing `version` field (an assessment of an older Statement derives as
stale, which is the display "on an earlier revision"), superseding only its author's own
earlier assessment of the same node, so disagreement between humans stays visible. It
mints no vettedness level and moves no number; AI handles write none. The checker
(`checkers/graph.py`) validates all of it, seven refusal directions each with a
null-input case in `--self-test`, and a unit test confirms a valid assessment is
accepted and leaves a node's V and J untouched. `graph/PROTOCOL.md` documents the fields,
the kind and the refusals (register **Default**: adopted on the dispatching maintainer's
ruling, the other maintainer's read pending, queued in `DECISIONS.md`); the `graph/`
section of `AGENTS.md` carries the event in its from-the-user's-words list and its gates
line; the design-log carries the change line.

The design is the conversation's three-view ruling (dated entry in `DECISIONS.md`,
2026-11-02), shaped by a GPT-6 Astra consult: mechanical class, derived contest state and
human assessment are views of one event graph, and only the third is human-writable from
the site. The agent-decided details and their rejected alternatives are in the entry.

Not in this increment, deliberately: the site's rendering of assessments beside class and
contest state, the record-my-assessment flow (a generated event handed to GitHub's edit
flow), the derived contest state itself (response and resolution artifacts beyond what
`cases` tables already carry), and the work queues. The site work follows in this round
once the open site pull request (#136) merges, so the branches do not stack; contest
state is a later increment because it extends `cases` semantics, which is deeper protocol
surgery than one event kind.

Not shown: that the stance and aspect vocabulary fits the second maintainer's workflow —
his read is queued, and the protocol paragraph is marked **Default** so re-ruling is
cheap. Nothing yet writes an assessment; the first real event will be a maintainer's,
from their own words, once the site flow lands.

## Attribution

Prompt-author: the maintainer, in conversation, kept verbatim (`PROMPT.md`). Executor:
Claude Fable 5 (Anthropic). 2026-11-02.

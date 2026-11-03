# Report — the assessment event

The ledger protocol gains `assessment`: a human's current score on one axis of a node —
`axis: reliability | importance | clarity`, `score` an integer 1 to 5 — with the
rationale required in `verbatim`, revision-bound through the event's existing `version`
field (an assessment of an older Statement derives as stale, which is the display "on an
earlier revision"), superseding only its author's own earlier assessment of the same node
and axis. Vouching for a standing score is posting the same number; challenging it is
posting a different one; every human's active score renders beside the others. The
stance-and-aspect form this round first landed was replaced by the maintainer's follow-up
directive before any event used it (`PROMPT-followup.md`; the 2026-11-03 ruling). It
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

The site side, landed after #136 merged: every node page carries an epistemic-status
panel with the three views kept apart — the registry's class where a formal result backs
the node (mechanical, with the bridge card for the record), the contest surface (the
failure-story tables attacking the node, with their attack-row counts), and the active
human assessments, superseded ones filtered, withdrawn ones dropped, stale ones marked
"on an earlier revision" — and a composer that generates the exact ledger event (axis,
score, verbatim, the node's current version pinned, `via: site`, supersession of the
author's own active score on that axis filled from the build) for the reader to copy into their
own ledger through GitHub's editor, with a prefilled-issue path for readers without a
handle. The concept pages — the map's read-more, the front door — carry the same view
through the graph nodes that back them (refs): the full panel and composer embedded when
one node backs the concept, a per-node summary linking through when several do, an honest
absence when none does. The composer's wiring is shared between static pages and the
map's injected modal. `via: site` enters the protocol and the checker for events
composed this way. The first push of the site side shipped the composer's markup without
its script (an apply step was dropped); caught when the maintainer looked for the panel,
fixed in the following commit.
Rendering is verified by an injected-event test (supersession filtered, staleness marked,
disagreement preserved) run in development; the standing gates cover the build and the
map page, and a standing render gate for the panel is a candidate, not shipped.

Not in this increment, deliberately: the derived contest state (response and resolution
artifacts beyond what `cases` tables already carry) and the work queues — deeper `cases`
semantics for a later round.

Also in the follow-up: the front page is the map alone — the question line and the
hand-written lede leave it, `site/lede.md` and its binding check leave the tree (with
their null-input self-test cases), and the map hint drops its opening clause.

Not shown: that the axes and the 1-5 scale fit the second maintainer's workflow — his
read is queued, and the protocol paragraph is marked **Default** so re-ruling is cheap. Nothing yet writes an assessment; the first real event will be a maintainer's, in
their own words, through the composer.

## Attribution

Prompt-author: the maintainer, in conversation, kept verbatim (`PROMPT.md`). Executor:
Claude Fable 5 (Anthropic). 2026-11-02.

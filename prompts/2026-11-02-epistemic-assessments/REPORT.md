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
mints no vettedness level and moves no number. An AI handle may seed one with its
reasoning in `gloss` — the estimate pattern, reversing this round's earlier human-only
form before any event used it; the seed is marked as an AI number in every display until
a human scores the axis, and a human's event supersedes nothing of the AI's (the AI
number simply stops rendering once a human one stands). The checker
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

The site side, landed after #136 merged: every node page opens with a full-width **hero
panel** — the three axes as large numbers, reliability red, importance indigo, clarity
olive (the maintainer's colour mock), lightness tracking the score 1–5, grey for an AI
seed no human has touched, a dash for an unscored axis, and a wavy underline with the
range (min–max) where active human scores disagree; disagreement is displayed, never
averaged. Below it a **context panel** holds the non-challengeable repo facts — the
registry's class with a kernel badge where a formal result backs the node, the
failure-story tables attacking it with their row counts, author, draft state and
Statement version — and the per-axis controls: *vouch N* where an uncontested human
score stands, *challenge* beside it, *score* where the axis is bare. Either button opens
the composer with the axis (and, for a vouch, the score) prefilled; the rationale is
required always. The attributed score list under each axis keeps superseded ones
filtered, withdrawn ones dropped, stale ones marked "on an earlier revision". The map's
hover card carries a mini-hero of the same three numbers above the one-paragraph
summary, fed per concept through the map data. The composer generates the exact ledger
event (axis,
score, verbatim, the target's current version pinned, `via: site`, supersession of the
author's own active score on that axis filled from the build) for the reader to copy into their
own ledger through GitHub's editor, with a prefilled-issue path for readers without a
handle. The composer's wiring is shared between static pages and the
map's injected modal. `via: site` enters the protocol and the checker for events
composed this way.

The map's unit got the same treatment (follow-up of 2026-11-04). Most concepts have no
backing graph node, so the node-only event left most of the map unassessable; the
`assessment` now also takes `target: {concept: <id>}`, validated against
`state/concepts.json` and carried by no other event kind (agent-decided, dated entry;
checker, protocol and null-input cases alongside). Every concept except prior work —
someone else's published result, cited rather than assessed — carries the hero and, right
beneath it, the context panel with the per-axis controls and composer, on its one Read
More page: title and kind, hero, context, the registry blurb, then the wiki page or the
backing claim's Statement beside the connections and merged work. A concept's displayed
scores merge those on the concept with those on any backing node, and the map data feeds
the mini-hero for all assessed concepts. The first push of the site side shipped the composer's markup without
its script (an apply step was dropped); caught when the maintainer looked for the panel,
fixed in the following commit.
Rendering is verified by an injected-event test (supersession filtered, staleness marked,
disagreement preserved) run in development; the standing gates cover the build and the
map page, and a standing render gate for the panel is a candidate, not shipped.

Not in this increment, deliberately: the derived contest state (response and resolution
artifacts beyond what `cases` tables already carry), the work queues (the
importance-exceeding-reliability prioritization the maintainer named as the eventual
use), and the deeper builder-breaker mechanics — the maintainer is still deciding that
part and parked it in so many words; nothing here forecloses it. Also not done: the AI
seeding itself — the protocol now admits AI seed events, but no seed is filed; that is a
dispatch of its own.

Also in the follow-up: the front page is the map alone — the question line and the
hand-written lede leave it, `site/lede.md` and its binding check leave the tree (with
their null-input self-test cases), and the map hint drops its opening clause.

Not shown: that the axes and the 1-5 scale fit the second maintainer's workflow — his
read is queued, and the protocol paragraph is marked **Default** so re-ruling is cheap. Nothing yet writes an assessment; the first real event will be a maintainer's, in
their own words, through the composer.

The landing (follow-up of 2026-11-03): `/` is a full-viewport landing — the maintainer's
own Wang-tiling generator, vendored verbatim from their personal site (two files under
`site/assets/landing/`, one import path rewritten), behind the wordmark and four
name-only buttons: map, chatbot, stats, repo (the maintainer's follow-up cut the subtitle
and the tiles' description lines), opaque, unshadowed wordmark, and every page's nav in
that same order. The landing's highlight colour follows the tiling: a small sampler
(`site/assets/landing/dominant.js`) histograms the painted canvas every 1.2s, takes the
most frequent colour that is not the near-black ground, lifts a dark one to a readable
luminance, and sets it as `--accent`. The same follow-up removed the build-commit footer
from every page. The map moves to `/map/`; `/chat/` and `/stats/` hold one-line
pages until their parts arrive; the nav carries all four. The engine sets the page's
accent from each tiling's palette, so the landing recolours itself cycle by cycle.

## Attribution

Prompt-author: the maintainer, in conversation, kept verbatim (`PROMPT.md`). Executor:
Claude Fable 5 (Anthropic). 2026-11-02.

# Report — the priorities page: the standing scores become an ordering

`/priorities/` ranks the scoreable concepts from the standing assessment scores and shows
each with its three-axis mini-hero, its registry blurb and its concept-page link — the
same click-through the map gives. The ordering (`priority_order` in `site/pages.py`) is
importance-led and raised by what has not caught up with it: twice the importance, plus
twice the reliability gap below it (an unscored reliability counts as 1 — nothing vouches
for it), plus the clarity gap where clarity is scored. A contested axis counts as its
range's midpoint; all arithmetic is integer (axis values carried doubled). AI seeds rank
and render grey as everywhere else; within a tie, human-scored importance sorts first.
Concepts with no importance score list below as not yet rankable. The page states its own
derivation and that scoring an axis is what moves it.

`/activity/` keeps the contested axes, the unscored count and the recent feed, and points
to `/priorities/` for the ordering; its "scored important, reliability behind" filter is
subsumed by the ranking. The nav and the landing tiles gain `priorities` after `map`;
`site/README.md` records the path and the page.

Corrections to the prompt (§8): the pull-request numbers had moved — #132 is closed
unmerged (its content landed via #133), the map-page work the prompt attributes to
"PR132" is the merged #133/#134/#136 plus the open #137, and this round's own number
cannot be 133. "Copy over as many of those changes as you can" is honoured by stacking
this branch on #137's head (`round/2026-11-02-epistemic-assessments`), the same pattern
as #132-on-#131, so the other thread's pushed work is all here and the merge of #137
leaves this diff clean.

Agent-decided, reversible: the ordering formula above — against ranking by importance
alone (blind to what is already settled: two importance-5 concepts with reliability 2 and
5 should not tie) and against the activity page's threshold filter (a filter names a set,
not an order, and the directive asks for "the highest priority things" first). Recorded
in `DECISIONS.md`.

Not shown: the ordering is only as good as the standing scores, and today those are
almost entirely the AI seeds of 2026-11-05 — the page ranks what one model asserted, not
what any human has judged, until axes are scored. The formula's weights (2, 2, 1) are a
choice, not a measurement; nothing calibrates them. The ranking does not read the `want`
/ `priority` ledger events or `graph/tasks.md`'s information-rate lens — `/ranking/`
still carries that view unchanged, and whether the two lenses should merge is left open.

## The follow-up of 2026-11-05 (`PROMPT-followup.md`)

The maintainer ruled on the four points the first increment raised. The item ledger is
renamed `PRIORITIES.md` → `ATTENTION.md` (the render, its sections file
`state/attention_sections.md`, the module `checkers/attention_render.py`, and every
living reference: governance documents, checkers, tests, graph documents, item nodes'
non-Statement prose, the pull-request template, the site). `/priorities/` and the items
are connected: each ranked concept lists the open items filed against it, matched
through the frames its refs name, and the ledger's preamble points back. The ratings are
the priority system, recorded in `AGENTS.md`'s demand-gating and site sections. The
standing maintenance dispatch is adopted as a ruling, with its authorization at
`prompts/2026-11-05-standing-maintenance/PROMPT.md`.

Machine identifiers stayed under the display rename (the pointer kind `priorities`, the
`priority` event on wants, `workspace_state`'s `priorities` key, the `/items/` paths),
and node Statements keep the old file name until each is revised with a version bump —
the checker refuses a Statement edit without one, and a forged bump would mark every
standing score stale; seven nodes' Statement sections were reverted to the old spelling
on exactly that refusal. Both choices are in the dated `DECISIONS.md` entry.

Not shown, in addition: nothing migrates GitHub-side references to the old file name
(issue templates, external links), and the item→concept match covers 87 of 116 open
items — an item whose node sits in no concept-ref frame lists under no concept, which is
a map fact, not a defect of the page.

## Outstanding maintainer actions

1. The wiki names `PRIORITIES.md` in five pages (`Normative-Record-and-Inquiry`,
   `Deconfusing-Corrigibility-Companion`, `Deference`, `Normative-Inductor`,
   `Theorem-Spine`); the wiki is the maintainer's surface — edit, or dispatch a round to.
2. Wire the maintenance sweep's schedule (cadence is yours; weekly beside the freshness
   audit is the natural choice), e.g.:
   `claude -p --name '⚙ maintenance-sweep' "Run the standing maintenance sweep per prompts/2026-11-05-standing-maintenance/PROMPT.md in a worktree of ~/hub/repos/alignment-workspace; open one PR." --permission-mode auto`

## Attribution

Prompt-author: the maintainer, in conversation, kept verbatim (`PROMPT.md`, and the
follow-up in `PROMPT-followup.md`). Executor: Claude Fable 5 (Anthropic). 2026-11-05.

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

## Attribution

Prompt-author: the maintainer, in conversation, kept verbatim (`PROMPT.md`). Executor:
Claude Fable 5 (Anthropic). 2026-11-05.

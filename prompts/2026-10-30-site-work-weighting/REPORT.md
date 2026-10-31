# Report — capsule size tracks importance

A capsule on the research map scales with a rough importance: the merged work tagged to
its concept plus its connections in the map, sqrt-damped, blended with its rank
percentile (0.45 magnitude / 0.55 percentile — the magnitudes clump near zero, so
percentile is what spreads the middle visibly; equal scores stay equal), and normalized
(`map_data` in `site/pages.py` ships it as `imp`). The type carries the signal — 10px on
a leaf concept to 28px on `legitimacy-line`, convex (`imp^1.35`) so the top tier
separates — because capsule width alone varies with title length and hides it; the first
cut of this round scaled width by raw merged-PR count and was not visible on the preview,
which is what the follow-up directive corrected. The legend carries
`size · work & connections`.

The per-concept merged-work count is computed once, with the same match the popup's
"Merged work" section uses (wiki tag or frame refs), so the capsule's size, the card's
count and the popup's list agree; before this round the card counted wiki-tag matches
only, so a concept tagged through its frames showed fewer PRs on the card than in its
popup.

The collision pass reads the same geometry, so node spacing adapts; the DOM gate's
no-overlap assertion passes on the built site.

Agent-decided, reversible: importance as merged work plus link degree, sqrt-damped —
against raw PR count (drowned by the goal frames and invisible below ten PRs) and against
degree alone (blind to where the work went).

Not shown: the measure is a proxy for attention, not content. It counts tagged merged
PRs and hand-audited links; work landed by direct push, rounds not yet digested, Lean
volume inside a PR, and a concept's importance to the program's argument (as against its
activity) are all outside it.

## Attribution

Prompt-author: the maintainer, in conversation, kept verbatim (`PROMPT.md`, and the
follow-up in `PROMPT-followup.md`). Executor: Claude Fable 5 (Anthropic). 2026-10-30.

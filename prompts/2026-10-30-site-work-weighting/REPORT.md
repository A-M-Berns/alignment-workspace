# Report — capsule size tracks importance; the layout moves to soft goal affinity

A capsule on the research map scales with a rough importance: the merged work tagged to
its concept plus its connections in the map, sqrt-damped, blended with its rank
percentile (0.45 magnitude / 0.55 percentile — the magnitudes clump near zero, so
percentile is what spreads the middle visibly; equal scores stay equal), and normalized
(`map_data` in `site/pages.py` ships it as `imp`; `the-program` is pinned to 1). After a
design consult against a render of the page (GPT-6 Astra, 2026-10-31, second consult of
the round), the signal moved from type into area: the type floor is 12px rising to 16px,
and importance is carried by capsule padding, per the consult's finding that a wide font
ramp costs first-read legibility. The first cut of this round scaled width by raw
merged-PR count and was not visible on the preview, which the first follow-up corrected;
the second follow-up adopted the consult's layout.

The layout (`site/assets/map.js`) is radial: the program is the one node at the centre,
and every concept sits at the circular mean of the angular anchors of the lines it feeds
— the six lines ordered around the circle so pairs with the most shared upstream support
are adjacent (exact permutation search) — blended 0.45 toward even occupancy so the disc
fills roundly. Radius is dependency depth, realised as capacity-balanced elliptical
rings: each ring takes, in depth order, as many capsules as its circumference carries at
one constant gap, so density is roughly homogeneous by construction; within a ring each
capsule starts at its affinity angle and moves only as far as the gap demands, so
sectors stay where their lines live and arcs the research leaves sparse stay sparse. A
2D push-apart guarantees personal space and the DOM gate asserts no overlaps. Edges
attach where capsules face each other and bow gently toward the centre; arrowheads are
fixed-size, fill from their wire's stroke (context-stroke), orient with the path, and
sit on the drawn tip. Edge opacity is 0.25 base (0.12 undirected) with strong focus
contrast; capsule titles render without a trailing parenthetical citation (the card
keeps the full title); a fit-map control and a one-line reading instruction join the
overlays; a search hit lights its incident relations while its mark lasts. The map boots
centred on the program at twice the whole-map fit. The intermediate layered layout, its
staircase predecessor, and a global rank-uniformisation that read as a spiral were each
superseded by maintainer direction on renders; the directives are verbatim in
`PROMPT-followup-2.md`.

The per-concept merged-work count is computed once, with the same match the popup's
"Merged work" section uses (wiki tag or frame refs), so the capsule's size, the card's
count and the popup's list agree; before this round the card counted wiki-tag matches
only, so a concept tagged through its frames showed fewer PRs on the card than in its
popup.

The collision pass reads the same geometry, so node spacing adapts; the DOM gate's
no-overlap assertion passes on the built site.

Agent-decided, reversible: importance as merged work plus link degree, sqrt-damped —
against raw PR count (drowned by the goal frames and invisible below ten PRs) and against
degree alone (blind to where the work went). Also agent-decided: the consult's
soft-affinity scheme over its explicit-lanes alternative (the shared-foundations lane
would be the busiest and least coherent), and its waypoint routing through free column
slots over a full orthogonal obstacle-avoiding router (the router is most of the
remaining elegance gap and is a candidate for a later round).

Not shown: the measure is a proxy for attention, not content. It counts tagged merged
PRs and hand-audited links; work landed by direct push, rounds not yet digested, Lean
volume inside a PR, and a concept's importance to the program's argument (as against its
activity) are all outside it.

## Attribution

Prompt-author: the maintainer, in conversation, kept verbatim (`PROMPT.md`, and the
follow-up in `PROMPT-followup.md`). Executor: Claude Fable 5 (Anthropic). 2026-10-30.

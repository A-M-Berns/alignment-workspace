# Report — capsule size tracks merged work

A capsule on the research map now grows with the merged work tagged to its concept, so
the map shows where the repository's effort has gone. The measure is the count of merged
pull requests the concept's popup already lists — the digests of `state/prs.json` matched
by wiki tag or by the concept's frame references — so the size, the card's count and the
popup's list are the same number. `site/pages.py` computes the per-concept count with
that one match (`map_data`); before this round the card's count matched only the wiki
tag, so a concept tagged through its frames showed fewer PRs on the card than in its
popup.

Growth is sqrt-damped and capped (`site/assets/map.js`): a concept with no tagged work
stays at base size, the heaviest (`legitimacy-line`, 40 PRs) is about half again as
large, with the title font up at most 2px. The legend carries `size · merged work`. The
collision pass reads the same geometry, so node spacing adapts; the DOM gate's no-overlap
assertion passes on the built site.

Agent-decided, reversible: sqrt damping with a cap, against linear scaling — linear would
make `legitimacy-line` dominate the canvas and flatten every distinction below ten PRs.

Not shown: the count measures tagged merged PRs only. Work that landed by direct push,
rounds not yet digested, and Lean volume inside a PR all weigh the same as any other PR
or not at all, so the size is a proxy for attention, not a measure of content.

## Attribution

Prompt-author: the maintainer, in conversation, kept verbatim. Executor: Claude Fable 5
(Anthropic). 2026-10-30.

# Follow-up dispatch of 2026-10-30 — the site is one zoomable map (S5)

Maintainer directives, given in conversation on the open pull request's preview, verbatim:

> let's trim this down. e.g. walks is not necessary. we should try to get to roughly a
> single unified UI that can expand into different levels

> wasn't there supposed to be some kind of graph? it should be like a graphical high level
> representation that can then be expanded into more detail. I think it's eventually also
> going to be crucial that you can leave comments or select epistemic statuses on
> individual pieces of work. I think there's like a PR as a natural unit, individual
> rounds or components of a PR as more fine grain, a frame or like conceptual piece as
> another level or like another "view" perhaps. the UI should feel like "zooming in and
> zooming out" of the repo

Choices put to the maintainer and taken: nested regions over a force-directed layout;
intake as prefilled GitHub issues over display-only or a backend; the rework lands on this
round's open pull request rather than after its merge.

Scope: the site under `site/`, its gate, and the governance text that describes the site
(`AGENTS.md` *The site under `site/`*, `graph/MAP-AS-CANONICAL.md` §6, `DECISIONS.md` —
the S5 entry and the walk-review queue entry it retires).

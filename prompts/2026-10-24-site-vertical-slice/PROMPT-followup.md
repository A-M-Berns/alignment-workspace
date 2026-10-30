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

Further directives of the same conversation, verbatim:

> you should also match the base aesthetic style and color palette of amberns.com, the
> current popup behavior is that in cloudcli the content of the window disappears but it
> doesn't pop back down to the post-minus-press state as desired

> ok so the whole graph shouldn't be rendering from the beginning. It should be like at
> first you just see a top level graphical representation. then if you click into
> something it zooms in, revealing the internal relationships, with the ability to zoom
> back out. in other words, levels are discrete and not continuous. Also, try to make the
> graphical representation more visually appealing with smooth transitions. Also, i think
> an important step is to go through and for every PR generate a key points summary of
> results because the PRs are long and dense. So dispatch an agent to go through and do
> that. If a PR's results are superceded, that should be clear with references. Clear,
> human readable, appropriately but not necessarily absolutely self-contained in
> information, a paragraph or two per PR. And then every PR should be tagged with any
> relevant subtopic nodes at a certain level, so you can see like a zooming-in concept
> type view and also for each topic a different view shows each PR with like a
> description you can click into and a list of rounds associated with it as well. In
> general, the user shouldn't be flooded with text unless they "ask for it" by clicking
> in far enough. Outer conceptual/mathematical level is like at the goal level, then
> maybe like one level in is like a "concept consellation" of overlapping concepts, that
> could be a mathematical object from prior art or a term of art we coined ourselves, and
> its like a wiki structure, and for each one you can click in and see related work in
> PRs, and it's again potentially overlapping and just also demonstrating visually the
> interrelated structure of wiki concepts at different levels or with other relationships

> this visualization is still ugly. we don't need to see that a node is composite at all
> before clicking into it. It should be a relatively small node, it should also generally
> be like light on dark or dark on light with jewel tone colors from the palette
> incorporated. each layer should be like pannable around with a like somewhat typical
> "graph theory" type network graph and maybe like edges can be hovered over with summary
> of the relationship/overlap and you can like click into individual nodes for a
> different view with links to elsewhere on the wiki map. I'm starting to think that
> there should basically one wiki level which is a big pannable network, and each node
> clicks into a different popup type view

> also basically just get rid of all the tabs except map. eventually i'd also like to add
> a chat tab for a byo api key bot, and then maybe also like some kind of stats/status
> page with a time graph plus an activity digest or something but i dont think really
> anything else

> also basically just get rid of all the tabs except map. eventually i'd also like to add
> a chat tab for a byo api key bot, and then maybe also like some kind of stats/status
> page with a time graph plus an activity digest or something but i dont think really
> anything else. take away "class" view. also i want to expand the wiki level of
> granularity, it can go past the actual repo wiki which should probably be mostly
> retired. members of that overall network can include important prior art papers or
> ideas, specific mathematical objects (logical inductor, cartesian frames, udt) like
> this should become roughly a wiki of the kinds of agent foundations theory relevant
> here encompassing the wiki's own terms but going beyond them. and then nodes can also
> be color coded by kind

> right so some of the kinds could include philosophical concept, new construction,
> existing mathematical object, existing piece of work, goal/thread of the research

> also, it shouldn't be a close to complete graph for every link. Go through all n
> choose 2 connections and only include relevant ones. these connections can also have
> multiple categories iff that's helpful

> also it's ok for the whole graph to not fully fit by default, the nodes should be
> relatively spread out. and each one can have a small summary as part of its body. in
> the click-in PR view the PRs should be listed reverse chronologically with like you
> expandable digest sof each one or click in further for full detail

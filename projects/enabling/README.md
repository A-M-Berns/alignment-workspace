# The enabling line

The enabling line is the research program's own machinery: the argument map under
`graph/` and its checker, the claims registries and their gates, the wiki's binding to the
structured state, the workflows that publish what the repository derives, and the site that
renders all of it. Its frame in the map is `enabling-work`, a line of `the-program` owned by
both maintainers, whose question is which repository infrastructure makes the trust research
vettable and publishable. Before this directory existed, workspace rounds had no home under
`projects/`: the graph prototype of 2026-10-02 indexed itself with the path `graph`, and the
later workspace rounds lived under `prompts/` alone.

Its rounds build and repair that machinery. Each round under `rounds/` carries its own
documents (a round of this line produces checkers, generators, gates and workflows, and the
documents that state what they do and do not do) and is indexed in `state/rounds.json` like
a research round, with `project: enabling`, so that the map's `round` pointers and the site's
round pages resolve it. The first is `rounds/2026-10-24-site-vertical-slice/`, which
connected five reference results to the claims they establish and built the first version of
the site.

This line registers no claims. It has no `CLAIMS.md`: a round here produces no theorem and no
statement of record, and nothing it builds is evidence for any node of the map. What it
produces is checked by the gates it ships, under `tests/run.py`, and reviewed as
infrastructure.

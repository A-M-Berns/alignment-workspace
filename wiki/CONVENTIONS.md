# Wiki conventions

**This directory is the wiki's source of truth.** Pages are edited here and
arrive as pull requests, which pass the same gates as everything else. The
hosted wiki is a build artifact: the sync job force-pushes this directory to it
on every merge to `main` that touches `wiki/`, so an edit made in the hosted
wiki's web editor is overwritten without warning and without a record.

This file and `ORIGIN.md` are repo-side only. Every other file here is a page,
named by its filename, and `_Sidebar.md` is the navigation column.

## Register

Human-facing conceptual content: what the program is asking, why a distinction
matters, how the lines fit together, what a result means for the question that
motivated it. The lab holds the machine-facing record — statements of record,
claim registries, structured state, verification. **Machine ledgers are linked,
not mirrored.** A page that reproduces a registry row acquires a copy that
drifts silently the moment the registry moves, and a reader has no way to tell
which of the two is current.

## Links into the repository

Every link into this repository is pinned to a full 40-character commit SHA —
`/blob/<sha>/…` or `/tree/<sha>/…`, never `/blob/main/…`. A page cites evidence,
and evidence a branch name resolves to is evidence that changes underneath the
sentence citing it. `checkers/wiki_links.py` enforces this, and also that every
link to another page here resolves to a page that exists.

## Volatile quantities

A number that changes when work lands — a claim count, a pull-request number, a
round tally — **is declared, or it does not appear.** Declaring it is two HTML
comments, invisible in the rendered page, and `checkers/wiki_state_bindings.py`
compares what you wrote against what the workspace says today.

**Bind a live quantity** to a dotted path into the state emission:

```
The consolidation is a separate
<!--state:workspace:counts.foundation_claims-->180<!--/state-->-claim foundation.
```

`workspace` is `python3 -m checkers.workspace_state --json`, this repository's
one adjudicator; `python3 -m checkers.wiki_state_bindings --sections` lists the
sections it offers. Aggregates live in its `counts` section, because deriving
them here would make the wiki a second judge of what the workspace holds. A path
that has no key is a request to the maintainer to grow the emitter, not a licence
to write the number bare.

**Mark a past event historical** when the statement cannot rot:

```
<!--historical-->PR #31 registered no workspace claim<!--/historical-->
```

Nothing inside is verified, which is why it is capped at three lines: it marks a
statement, not a section.

**Four forms fail unless declared** — a pull-request number, and an integer
immediately before `claims`, `rounds`, or `priorit(y|ies)`. That list is a
backstop for what gets written without thinking, not a definition of volatility;
nothing here reads free prose to guess. **A hit is not a complaint about the
sentence.** It asks where the number came from, and the remedy is to bind it or
mark it historical. Growing the list is a maintainer act.

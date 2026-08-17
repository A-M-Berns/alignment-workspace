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

Claim counts, pull-request numbers, round tallies, "N of M items closed" — a
number that changes when work lands **either cites `state/*.json` as its source
or does not appear on the page**. Prose that names a number is prose that is
wrong on a date nobody notices, and the wiki is the register least likely to be
re-read when the number moves. Say what kind of thing there is and point at the
structured state for how many.

Nothing checks this yet; `PRIORITIES.md` carries the item for a checker that
would.

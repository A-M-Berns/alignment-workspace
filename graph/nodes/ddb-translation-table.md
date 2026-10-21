---
id: ddb-translation-table
kind: leaf
leaf_kind: task
action: "Write wiki/DDB-Translation-Table.md, one row per DDB result, from the wiki pages and the clean room's lit-ddb-frames, lit-ddb-facts and lit-ddb-accuracy-mm packages, and link it from wiki/Home.md."
who: agent
files: ["wiki/DDB-Translation-Table.md", "wiki/Home.md"]
author: "@smithy-verity-opus55"
size: S
size_reason: "a table of nine rows"
version: 1
---
## Statement
A table lists each result of DDB (Theorems 2.2, 3.1, 3.2, 4.1, 5.1, Lemma 7.1,
footnotes 25, 51 and 65) with its logical-induction counterpart, status and
Lean name.

## Source
projects/deference/faf-cleanroom-2026-10-02/packages/lit-ddb-frames/lit-ddb-frames-report.md;
projects/deference/faf-cleanroom-2026-10-02/packages/lit-ddb-facts/lit-ddb-facts-report.md;
projects/deference/faf-cleanroom-2026-10-02/packages/lit-ddb-accuracy-mm/lit-ddb-accuracy-mm-report.md.

## Notes
Shows which DDB results have no logical-induction counterpart yet (today §3,
§4 and §5).

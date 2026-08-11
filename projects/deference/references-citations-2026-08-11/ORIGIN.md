# Origin — citations for the removed third-party papers

**Status: `agent-consolidated`.** Ordinary content — editable and
reviewable, not machine-protected. The norm is that it is not tweaked. Edit it
when there is a reason, state the reason in the commit, and record substantive
edits in `DECISIONS.md`. Rewriting it to fit new work is not a reason.

## What it is

Bibliographic entries and sha256 digests for the published third-party papers
removed from the two note dumps beside it. It **supersedes their `references/`
payloads only** — nothing else in either bundle is affected.

One citation could not be verified against a publisher of record. It is flagged
as unverified inside the entry rather than reconstructed, per the
citation-integrity rule: state the content and record that the label did not
check out.

## As received

| | |
|---|---|
| created | 2026-08-11 |
| archive sha256 | n/a — created in-repo, never an archive |
| tree sha256 at intake | `268fbdba885f2d0645d8ea4d5f2887cf249f6ed3bd2fcd1a64f42bbff7bf291c` |
| files at intake | 1 |

## What cites it

`../note-dump-2026-06-27/ORIGIN.md` and
`../dose-response-note-dump-2026-07-02/ORIGIN.md`.

## Checking this receipt

The tree hash is over relative paths and file digests in sorted order, excluding
bytecode artifacts and `.DS_Store` — and **excluding this file**, which did not
exist at intake. Recompute it that way and you learn whether the tree has moved
since it arrived. Nothing enforces that it has not: this is a receipt, not a
gate. The protection that remains is that these paths are specification layer in
`tests/path_gate.py`, so a contributor cannot touch them and a maintainer's edit
is a reviewed diff in git history.

# Origin — the wiki pages

The human register's pages, imported from the hosted wiki so that the
repository holds their source. Changes arrive as pull requests against this
directory; the hosted wiki is a mirror the sync job force-pushes. See
`CONVENTIONS.md` beside this file for what the register is for and what may
appear in it.

## As received

| | |
|---|---|
| source | `https://github.com/A-M-Berns/alignment-workspace.wiki.git` |
| intake commit | `d86c9d7` — *Humanize the research-program wiki* |
| intake date | 2026-08-16 |
| intake by | round `prompts/2026-08-16-wiki-in-repo-sync` |
| files at intake | 14 — thirteen pages and `_Sidebar.md` |
| tree sha256 at intake | `cf260b6f6fe6bb9fcf9497dd7685c28d4134b74e24f3e584457db7acddf504c9` |

Filenames are preserved exactly: the hosted wiki derives a page's name and its
URL from its filename, so renaming a file here renames a page there and breaks
every link to it.

## Checking this receipt

```sh
python3 .github/wiki_tree_digest.py wiki --exclude ORIGIN.md CONVENTIONS.md
```

The digest is sha256 over one `<sha256>  <path>` line per file, sorted by path.
The two exclusions are this file and `CONVENTIONS.md`, neither of which existed
at intake and neither of which is a wiki page.

**That command does not print the intake digest**, and is not meant to. The
intake round added one sentence to `Home.md`, so the pages already differ from
what arrived: at the end of that round the same command printed
`deec7daa7b41090bb662dd3165220ae56c45fd9aa7926f1d7bf7282a417ad267`. To recompute
the intake value, take the digest of a fresh clone of the source at `d86c9d7`.

A receipt, not a gate: it tells a reader whether the pages have moved, and
nothing prevents their moving. The protection is that `wiki/**` is specification
layer in `tests/path_gate.py`, so a change is a maintainer's reviewed diff in git
history.

## Provenance of the pages themselves

The pages were written by the maintainer's wikification round, not by this one,
and this import did not revise them. The one content edit made here is a
sentence in `Home.md`'s *Wiki and lab* section recording where the source now
lives; it is listed in `PROVENANCE.md` and in the round's report. Git history
before intake stayed in the wiki repository — no history was grafted, and this
receipt is the provenance record in its place.

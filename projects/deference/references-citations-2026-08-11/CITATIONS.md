# Citations for the removed reference payloads

**Frozen entry, 2026-08-11.** The note-dump bundles vendored third-party papers
under `references/`. This repository has no redistribution rights to them, so the
payloads were removed and replaced by this entry: full bibliographic detail, a
link, and **the sha256 of each removed file**, so the frozen record still pins
exactly which document the conversations engaged with.

The bundles' conversations, notes and Lean content are untouched.

Cite, do not vendor. A reader who needs a paper fetches it from its publisher.

## What was removed, with digests

| bundle | path within `references/` | sha256 | bytes |
|---|---|---|---|
| `deference-note-dump-2026-06-27` | `deference-and-infinite-frames/Deference and Infinite Frames.md` | `4b80c955d60fae87206c3cd283070ecfd804b9db731d982e7e4ce406f2037584` | 44,314 |
| `deference-note-dump-2026-06-27` | `deference-and-infinite-frames/Weatherson--Deference and Infinite Frames.pdf` | `be49e54a7195ab368d3942d1b5793bfca6a0625877868b72f77737b8815606bc` | 112,068 |
| `deference-note-dump-2026-06-27` | `deference-done-better/DORDDBv1.pdf` | `47bd703cb9c5decef9a80f3cb374949121766058bc8e4714f1280cc140ff91dd` | 1,087,064 |
| `deference-note-dump-2026-06-27` | `deference-done-better/Deference Done Better.md` | `fc5bb4b21b2628d1f3328b6dc07452e48f0804bed703814ff7531d80f30285bd` | 188,593 |
| `deference-note-dump-2026-06-27` | `logical-induction/arxiv-1609.03543.tar.gz` | `b1448b8d94eb22e975bb3cdbf0115251ad50293b6447d48474bb1dd265627d19` | 156,106 |
| `deference-note-dump-2026-06-27` | `logical-induction/main.bbl` | `c5370beefbde7c90e3a24926f7a574431d7aa0fce677bcc1f604cf353d12fa5a` | 177,353 |
| `deference-note-dump-2026-06-27` | `logical-induction/main.tex` | `ea433498cc6dd07adf536548fac6596293e38abd4bb0f96e2cc8b948dd5e3c6b` | 454,388 |
| `deference-note-dump-2026-06-27` | `logical-induction/miri-tech-article.cls` | `209578ae87e2ebec57d11ea8c8608629aafd94b07a3b64c0c31f7d8a2028b939` | 8,338 |
| `deference-note-dump-2026-06-27` | `logical-induction/miritools.sty` | `8763338322826f205bfe21b1d6ce8ac36a9e97e9073cdc0c90c0982aca423000` | 8,096 |

## Bibliography

**Garrabrant, Scott; Benson-Tilsen, Tsvi; Critch, Andrew; Soares, Nate; Taylor,
Jessica. "Logical Induction."** arXiv:1609.03543.
<https://arxiv.org/abs/1609.03543>
*Removed payload:* the paper's LaTeX source and its arXiv tarball. arXiv's
default licence permits arXiv to distribute; it grants no redistribution right to
third parties, which is why the source is cited rather than carried.

**Weatherson, Brian. "Deference and Infinite Frames."**
*Removed payload:* publisher PDF and an extracted-text rendering. Consult the
publisher of record; a published PDF is the clearest case of what a repository
should not redistribute.

**"Deference Done Better."**
*Removed payload:* PDF and an extracted-text rendering. Bibliographic detail is
recorded as it appeared in the bundle; **the full citation is unverified against
a publisher of record and is flagged for the author.** Per the citation-integrity
standard, an unverified identifier is stated as unverified rather than
reconstructed from memory.

## Standing

This entry supersedes the `references/` payloads of both note dumps. It does not
supersede the bundles: their conversations, notes and Lean content remain
registered and unchanged, and their tree digests were recomputed in the same
change that removed the payloads — which is the one sanctioned way frozen content
changes, and it requires maintainer review by construction.

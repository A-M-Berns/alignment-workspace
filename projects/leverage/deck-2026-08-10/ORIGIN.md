# Origin

**Getting Leverage on Normativity** — the talk the leverage line is presented
from. Author-written, and the first artifact of this line that is.

| field | value |
|---|---|
| generator | the maintainer, with model-drafted passages marked on the slides themselves |
| review status | `maintainer-reviewed` for the author-written frames; see *What the marks mean* |
| source timestamp | 2026-08-10 19:27 local, the source's own modification time |
| intake date | 2026-08-11 |
| intake by | round `prompts/2026-08-11-phi-regret-prep` |
| frames | 29 |

## Digests at intake

```
d4989cd0dc011847667485e38df0420f6b6494c65985bd10e5cd26c758ee01c7  getting-leverage-on-normativity.tex
88c2f584ba2386cda2641334905c0af9ae872cd8f091f7b7d6f74f7329949da1  getting-leverage-on-normativity.pdf
```

A receipt, not a gate: it lets a reader determine whether the files have moved
since they arrived. Nothing prevents their moving.

## This is a snapshot and will be superseded

The deck is under active revision and the source carries a version counter. What
is here is the state at the timestamp above. **A later version supersedes it, and
the supersession will not be visible from inside this folder** — it will be a new
`ORIGIN.md` on a replacement, or a `DECISIONS.md` entry, and nothing else.

A reader taking a claim from these slides should check the date before relying on
it, and should prefer `projects/leverage/consolidation-aug9/` by claim identifier
wherever the two overlap. Slides compress; the consolidation states hypotheses.

## What the marks mean

The deck carries its own attribution scheme, on the slides, and it is finer than
anything the repository's provenance fields can express. Three environments:

- a bordered box for the author's own language, used 22 times;
- an alert-coloured box for a model-drafted scaffold;
- a corner badge on a frame whose on-slide text is still model-written, used
  twice, and removed from a frame once the wording is the author's.

So the deck reports its own review status frame by frame, which is why the table
above says `maintainer-reviewed` with a pointer rather than a flat label. **Two
frames are marked as still carrying model-written text at this timestamp.**

## Why this is here

`PROVENANCE.md` before this intake recorded no `maintainer-reviewed` research
content in the leverage line: the consolidation is `ci-only`, the forward tree is
`ci-only`, and the only `maintainer-reviewed` rows in the repository were the
dispatch prompts, marked so because they were sent as written. That is an
accurate record and also a gap — the line's own account of itself, in the author's
words, existed only outside the repository.

## Status and layer

Ordinary content, cited by path, not tweaked. Its path is enumerated in
`tests/path_gate.py` alongside the received trees, so a contributor pull request
touching it fails the path gate. That enumeration was added by the intake round
and is flagged in `DECISIONS.md`'s *Awaiting the author* for confirmation.

## Building it

`pdflatex` twice, `beamer` with `tikz`, `pifont`, `stmaryrd` and `lmodern`. The
compiled PDF at the digest above is included so the deck is readable without a
LaTeX installation.

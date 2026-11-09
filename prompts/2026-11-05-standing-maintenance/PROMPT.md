# Standing dispatch — the maintenance sweep (ruling of 2026-11-05)

Maintainer directive, in conversation, verbatim:

> I think we should maybe add to the automated maintenance any reorganization or anything
> that can be done to resolved automated friction issues that come up with minimal human
> input and like asking directly for the input when it's required

This document is the standing authorization the ruling of 2026-11-05 names
(`DECISIONS.md`, *the standing maintenance dispatch*). Each sweep is a round against it:
a dated directory under `prompts/` citing this file as its prompt, a `REPORT.md`, a
`state/rounds.json` entry, a `PROVENANCE.md` row.

## The sweep

1. Read `ATTENTION.md`'s *Workspace friction* section and the standing *Freshness audit*
   issue.
2. Take every item whose fix is **contained** (§14 of `AGENTS.md`): non-retroactive,
   confined to one gate or one document, shipped with its own null-input case. Record
   each as agent-decided, reversible, in `DECISIONS.md`; retire the friction item.
3. Convert every item whose fix would change a spec-layer rule into a **direct question
   to the maintainer**: one line stating what the decision turns on, delivered to them,
   with the entry appended to *Awaiting the author*.
4. Report an empty sweep as empty.

One pull request per sweep. **No auto-merge when the diff touches `checkers/` or
`.github/workflows/`** — the maintainer's merge is the human input point. Full local
gates (`python3 tests/run.py`) before the pull request opens.

## Amendment of 2026-11-08 — digests, and a daily cadence

Maintainer directive, in conversation, verbatim:

> can you do a separate pr to write digests 133-140 and also make that part of the automatic
> maintenance process? and maybe make automatic maintenance daily

The sweep gains a step ahead of the friction items:

0. Run `python3 tests/freshness.py`. For every merged pull request it reports without a
   digest, write the digest in `state/prs.json` in the shape `site/README.md` gives: number,
   title, merged date, rounds, topic tags that resolve, one or two paragraphs of results in
   plain register drawn from the round's report and the registries, a supersession note
   where a later result displaced one, and the plain-language `state_after`. Write nothing
   the report and the registries do not support. Once the sweep's own pull request has a
   number, add its digest too, dated the day it opens, so no sweep leaves work for the next.
   An audit finding that needs a judgment `site/README.md` does not settle — a concept
   entry, a terminal goal — becomes a direct question to the maintainer, as in step 3.

**Cadence.** The sweep runs daily, launched from the maintainer's machine behind a check
that costs nothing: a day with no missing digest and no change to *Workspace friction*
makes no round and opens no pull request, and no sweep starts while an earlier sweep's
pull request is open. The freshness audit runs daily in CI and comments on its standing
issue only when its findings change.

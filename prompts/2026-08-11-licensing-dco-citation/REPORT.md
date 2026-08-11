# Round report — licensing, DCO, citation norm, and the rename

**Attribution.** Prompt author: Claude Fable 5 (Anthropic), 2026-08-11, in a
maintainer-directed session. Executor: Claude Opus 5 (Anthropic), 2026-08-11.

## The correction that reshapes section B

**Formalized-Agent-Foundations was already Apache-2.0, and has been since
2026-07-29.** Section B was dispatched on my earlier report that it had no
licence. That report was wrong.

The error: a shell glob. `ls LICENSE* COPYING*` aborted because `COPYING*`
matched nothing, so the `||` branch printed "no license file" without the
`LICENSE` test ever running. The same glob bug then almost produced a second
false negative about Foundation, which is also Apache-2.0.

What is actually true, verified: FAF's `LICENSE` was added in commit `138f0bd`
on 2026-07-29; that commit is an **ancestor of the pinned `1fffea44`**, and
`git show 1fffea44:LICENSE` returns the Apache text — so **the pin has always
pointed at licensed code**. FAF's README already carries a licence section.

Consequences, and they are the honest ones rather than the dispatched ones:

- **Nothing was changed in FAF.** B1 and B2 were already satisfied; performing
  them would have been theatre.
- **No pin bump.** B4 says bump to the licensing commit; that commit *precedes*
  the pin, so the bump would move backwards. The pin stays at
  `1fffea44eece253cda1722568a3adfe34e822f03`.
- The ledger records the correction rather than a fictional licensing act.

I am sorry for the wasted section. The lesson is cheap and worth keeping: a
negative result from a shell one-liner is not a finding until the specific test
that would have shown the positive has actually run.

## What was done

**A — Apache-2.0 in the workstudio.** Root `LICENSE`, standard text, copyright
line "Copyright 2026 the alignment-workstudio contributors". No per-file
headers. README states the licence, inbound=outbound under §5, and links both
`LICENSE` and `DCO`.

**C — DCO.** `DCO` v1.1 at root; `tests/dco.py` as **gate 8**, a script rather
than a third-party app so the gate has no dependency the repository does not
control; CONTRIBUTING section; PR checkbox. Pseudonymous sign-offs accepted, and
the reasoning is stated where a contributor will read it rather than buried.

**D — external-citation norm.** The sentence, verbatim, in the provenance
section of `AGENTS.md`.

**F — model attribution.** The trailer rule in `AGENTS.md`, with
`Prompt-author-model:` and `Model:` separated for dispatched rounds. Retroactive
pass without rewriting history: `PROVENANCE.md` gained a round-attribution table
and a **correction** — earlier rows named the executor "Claude Opus 4.6"; it was
**Claude Opus 5** throughout. Rounds predating the discipline are
`executor: unrecorded` rather than guessed.

**G — second maintainer.** `abramdemski` added to `CODEOWNERS` and the path-gate
list, each carrying a comment pointing at the other and the rule that they must
agree — which discharges the single-maintainer hardcoding flag at its first test.
Co-equality and the no-two-human-gates rule are stated in `AGENTS.md`.

**H — the deference line.** `projects/deference/`,
`Workstudio.Deference.*` including `Workstudio.Deference.Kernel`, and every live
reference. Completed round records and frozen trees untouched. **Lean rebuilt
green**, 1716 jobs.

**I — no negative ontologies.** The principle is in `AGENTS.md` and governed how
the rename was executed: no "formerly", no redirect stubs, nothing memorialising
the old name outside git history and the ledger. The retroactive sweep of living
documents found **no genuine residue** — the only matches were the principle
stating itself and retired `attic/` material, which is history by construction.
Reported as a clean sweep rather than dressed up as cleanup.

On absorption: the leverage line's tree is **already inside the repository**, at
`projects/leverage/workspace`, imported as ordinary commits in the scaffolding
round — so §I.2's absorption was already done and its history-flattening
requirement already satisfied. Its suite is already wired into the repo-level
runner and runs as a CI job. §I.3 checked out clean: every frozen-tree citation
that names the source tree by path resolves **inside the frozen tree**, which
vendors it at `frozen/consolidation_aug9/vendor/source_theory/`. Nothing dangles.

**E — redistribution swap.** New frozen entry
`references-citations-2026-08-11/` with bibliographic entries and the **sha256 of
every removed file**, so the record still pins which document each conversation
engaged with. Payloads removed; both note-dump entries annotated and their tree
digests recomputed in the same change — the one sanctioned way frozen content
changes. Conversations, notes and Lean content untouched.

## The eight gates

For the branch-protection payload, which is updated:

```
path-gate — proof-layer PRs may not touch the specification layer
dco — every commit carries a sign-off
checkers — house harness self-test and the claims registries
conservativity — no new axioms, specification shape unchanged
python — project test runners
lean — build, sorry-free, axiom audit
frozen-integrity — digests and the manifest rule
foundations-verification — the frozen consolidation re-proves itself
```

## Pre-public checklist, as I assess it

| item | state |
|---|---|
| Licence in place | **done** — Apache-2.0, and the whole upstream stack matches |
| Contribution rights mechanism | **done** — §5 plus DCO gate |
| Third-party redistribution | **done** — cited, not vendored; payloads removed by the frozen procedure |
| Branch protection | **blocked on the visibility flip itself** — unavailable on a private repository on this plan. Going public is what enables it, so for one moment the repository is public *and* unprotected. Apply the payload immediately after the flip. |
| Note-dump conversation content | **NOT CLEARED — the remaining substantive blocker.** The bundles contain research conversations that have never been scrubbed or read for release. `AGENTS.md` requires author read-through sign-off before a dump reaches a public repository, recorded in the ledger. That has not happened, and only the author can do it. |
| Flagship documents unreviewed | **open** — `README.md`, `AGENTS.md`, `CONTRIBUTING.md` and the checker harness are `llm-unreviewed`. The harness is the judge; of everything here it most warrants the author's eye before strangers rely on it. |
| One citation unverified | **open, minor** — flagged inside the citations entry rather than reconstructed |

**My assessment: the licence and redistribution blockers are cleared; the
conversation-content gate is not.** The note dumps went into `frozen/` as
research provenance before the release gate existed, and the release gate now
says they cannot go public unread. Nothing in this round could discharge that.

## What this round does not establish

The gates still are not *required* — branch protection remains unapplied, so a
direct push to `main` bypasses all eight. The DCO gate checks that an assertion
was made, not that it is true; that is the nature of a certificate of origin.
And this report, like the rest of the round, is `llm-unreviewed`.

# Prompt — map-as-canonical, closing pass on PR #131 (2026-10-24)

You are working in the `alignment-workspace` repository, on the branch
`round/2026-10-22-map-as-canonical` (PR #131, head `43468d7`; CI green there). This is the
closing pass of the round of 2026-10-22: two small commits on the branch, a rewritten pull
request body, and nothing else. Append to `prompts/2026-10-22-map-as-canonical/REPORT.md`
under *Closing pass of 2026-10-24*; put this prompt beside it as `PROMPT-closing.md`.
Auto-merge stays OFF; the merge is the maintainers', and the body you write tells them how.
Run `python3 -m checkers.graph --root .` and `python3 tests/run.py` before each commit, and
the unit tests in a CI-shaped checkout (no `graph/derived.json`, no `derived` branch) before
the last.

No ruling is taken here. Two choices below are agent-decided and reversible and are recorded
as such in the design log; everything else is transcription from the three reports.

## Part 1 — the residual roots (one commit)

The four item nodes that are `shared-claim` roots of a frame directly — `item-91` under
`deference-and-trust`; `item-108`, `item-109`, `item-110` under
`authorship-and-transparency` — move from `roots` to `holds` of the same frame, for the
reason G2 gave for the 120 docketed items: a work order no goal has been identified for is
held, not a goal. The two enabling-work claims the round filed (`enabling-map-as-canonical`,
`enabling-program-site`) stay `shared-claim` roots of `enabling-work`: they are goals of the
enabling line by their Statements, not work orders. One design-log line for each choice,
both marked agent-decided and reversible; update the follow-up report's §10 "not done" list
to say the item roots are now held. Root counts for the two frames before and after in the
report.

## Part 2 — the proposal document's principle (same commit)

`graph/MAP-AS-CANONICAL.md` §2 (*Structure and numbers*) states the decoupling but predates
G2. Add one paragraph, after the existing text, stating the principle G2 encodes in the
document's own register: the map is a representation of the research program, only part of
which is an argument; a frame's roots are its goals and enter the ranking, what a frame holds
is what it is about and does not; the argument view (support, formal results, conditions,
objections), the research map (lines, programmes, questions, what each holds) and the
contribution view (work orders, challenges, wants) are three readings of one structure and
do not share inference semantics. Cite G2's `DECISIONS.md` anchor. Do not rewrite the rest of
the section.

## Part 3 — the pull request body

Replace the body of PR #131 with a description of the branch's final state. The current body
describes the first commit's state (3,059 nodes, parsed hypotheses, `graph-index/1`) and is
wrong about everything the two follow-ups changed. Write it from the three report sections
and `MAP-AS-CANONICAL.md`, not from memory; every number in it is one the reports give, with
the report section named. Plain prose and short lists; it is read by the second maintainer
before anything else, and by anyone who opens the pull request later. Structure:

**1. What this pull request does** — five sentences at most: the map under `graph/` is the
canonical index of the program; one plan under the top question with seven lines; every
registered claim, priority item, decision and narrative page has one node or attachment;
`PRIORITIES.md` is a render; the two large derived files live on the branch `derived`.

**2. Final state, with numbers** — nodes (2,408), ranked units (1,886, from 2,021 on `main`
and 4,685 at the round's first state), formal results (178 registry-built, all with
hypotheses unread; 68 pre-existing hypothesis leaves by reading), items (137, rendered),
decision anchors (295; 244 unpointed), narratives (24 pages attached; 10 unattached, four of
them for a maintainer to place), rounds pointed at (120 of 126), held nodes (357 in 12
frames), frames with no goal yet (four, named), wants (13, all weight 0 until their owners
speak). Each with its report section in parentheses.

**3. What changed across the three passes** — one short paragraph per pass: the round (the
restructure); the follow-up (hypotheses unread, the registry join, derived files out, old
frames dissolved, two merges of 244); the second follow-up (the digest, `holds`, bearing,
unconfirmed wants, the canonical hash — verified on the second platform on 2026-10-23: a
plain run on Linux / Python 3.13 leaves `versions.json` clean). Link each pass's report
section and its `DECISIONS.md` entry by anchor.

**4. What needs the second maintainer** — this is the section the pull request exists for;
write it so that it can be answered by replying to the pull request, one numbered question
at a time, each with the one line it turns on and a link to the node or entry. The list,
from the three reports' reserved sections and `DECISIONS.md` *Awaiting the author*:

1. **Confirm or strike the rulings** M1–M8, F1–F6, G1–G4 — one dated `DECISIONS.md` entry by
   `@abram` closes the queue line `open--second-maintainer-confirmation-rulings-m1-m8`. List
   the eighteen in one line each, grouped: the ones that changed his filings (M1 handles, M2
   `trust-modelling` widened into `the-program`, M5 multi-owner frames, G4 unconfirmed wants
   at weight 0), and the ones that are repository mechanics.
2. **`the-program`'s question and the line frames' questions** — provisional wordings, his to
   amend; quote `the-program`'s and the seven lines' questions verbatim with links to the
   node files.
3. **His lines** — `deference-and-trust`, `decision-theory`, `stance-and-level`,
   `abstraction-arc`, `enabling-work` were filed and not reorganized; `deference-and-trust`
   still carries `updateful-trust-li`'s question and roots verbatim. Does he want them as they
   are, or a round to reorganize them under his direction?
4. **`stance-and-level`** — a plan root only because every frame is one; the alternative is
   his cruxes as `shared-claim` roots of `the-program` grouped by a field (the second
   follow-up report §10). Which?
5. **His legitimacy theory** — F4 found that `legitimacy-reasons-programme`'s 60 line-level
   nodes are the logical-induction-register theory (legitimacy as a correction to the trust
   principles) rather than the September theory the three programmes carry; they are held by
   `legitimacy`, not goals. Does he want them as a fourth programme under `legitimacy`
   (provisional name "legitimacy in the trust principles", owner `@abram`), left held, or
   placed otherwise? Link the moves table (follow-up report Part 2).
6. **The 13 wants** — which are his (the re-owning by source attribution, follow-up report
   §2), and his priority word on each, or `none`. List them with their Statements.
7. **The clean-room records** — 78 kernel-checked declarations in
   `projects/deference/faf-cleanroom-2026-10-02/` that no registry lists cap at level 2;
   whether the clean room gets a registry is a trust-chain decision (round report §4, item 1).
8. **The top frame's owner** — `@anson` alone today; `the-program` is both. Both at the top
   too?

Then, under a sub-heading **What needs the first maintainer**, the shorter list that is
`@anson`'s: confirm or redraft the ten frames marked `filed_from: wiki` (named), his priority
words on his wants, the four unattached wiki pages, the four frames with no goal yet, and the
54 ambiguous and 8 blocked merges of F5 (link the lists).

**5. How to merge** — a squash merge is recommended against the repository's merge-commit
convention, for one reason stated plainly: seven commits on the branch carry versions of
`graph/derived.json` and `graph/index.json` at 11–15 MB and 3–4 MB each, a merge commit keeps
all seven in the history forever, and a squash keeps none (second follow-up report §10, with
the pack sizes). Note that the round's prompts and reports, and `DECISIONS.md`, preserve the
pass-by-pass history that the squash removes from `git log`. Say that the rulings are in force
as one maintainer's with the other's confirmation queued, which is the state the regulations
designed for a ruling taken in conversation, so the merge does not wait on §4 — but the
answers to §4 are the next round's first commit.

**6. After the merge** — the `derived` workflow runs for the first time on `main`; check the
branch `derived` appears with both files and the `main` hash in its commit message, since it
has never executed. Then the next round is the vertical slice (five reference claims
connected by reading, and a site prototype walking one question through them), not another
structural pass.

Post the body with `gh pr edit 131 --body-file <path>`, and commit the same text as
`prompts/2026-10-22-map-as-canonical/PR-BODY.md` so the repository holds it (link it from the
report). Do not change the PR title unless it still says "the map as the canonical index of
the program" is a proposal; it is the description.

## Report

Under *Closing pass of 2026-10-24*: the checker's OK and DIGEST lines, `tests/run.py`,
the CI-shaped unit-test tail; the two frames' root counts; the design-log lines; a link to
`PR-BODY.md`; corrections to this prompt; and nothing reserved beyond what the body's §4 and
its sub-heading already list.

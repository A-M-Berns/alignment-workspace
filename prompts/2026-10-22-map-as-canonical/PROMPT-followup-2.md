# Prompt — map-as-canonical, second follow-up on PR #131 (2026-10-23)

You are working in the `alignment-workspace` repository, on the branch
`round/2026-10-22-map-as-canonical` (PR #131, head `4dc8811`), continuing the round of
2026-10-22 and its follow-up of 2026-10-23. Commit on that branch; append to
`prompts/2026-10-22-map-as-canonical/REPORT.md` under *Second follow-up of 2026-10-23*; put
this prompt verbatim beside it as `PROMPT-followup-2.md`. Auto-merge stays OFF. Run
`python3 -m checkers.graph --root .` and `python3 tests/run.py` before every commit, and
this time also run the unit tests the way CI runs them (`python3 -m unittest discover -s
checkers/tests -t .`) in a checkout that has no `graph/derived.json` on disk and no
`derived` branch, because that is the state CI is in.

## What this follow-up is for

Two reviews of the branch at `4dc8811` agree on the architecture and name five things to fix
before merge. (1) CI is red: `test_table_filed_on_the_fixture_passes` (and possibly others)
raises `KeyError` on `D["digest"]["statuses_flipped"]`, because the digest's shape changes
when `previous_derivation` finds nothing to compare with. (2) A docket is an `or` with
`either-suffices`, so a collection of work orders carries the semantics of a claim — a
status and a probability — and, more broadly, formal results and other nodes were attached
to frames as `shared-claim` roots because they are *about* the frame, which makes each of
them a goal of the ranking. (3) The render line *Registered answers in the map* overstates
what a registered result does for an open item. (4) A want its owner has not confirmed
weighs `medium` in the ranking, the same as one its owner called medium. (5) The history
carries five copies of the 12–15 MB derived files. This follow-up fixes (1)–(4); (5) is a
merge-strategy note for the maintainers, recorded in the report.

The rules of the round carry over: structure and numbers are decoupled; the protocol changes
through its own mechanism rather than content being bent; no number, judgment, acceptance,
priority word or human event is written. Every path, field and function named below was read
from the branch at `4dc8811`; confirm each and correct this prompt in the report where it is
wrong.

## Maintainer rulings

Land as one dated `DECISIONS.md` entry, the first commit, marked as taken by one maintainer
in conversation with the other's confirmation outstanding; append to the round's existing
queue line rather than opening a third.

**G1. The digest has one shape.** `derived.json`'s `digest` carries the same keys whatever
`previous_derivation` returns: `compared_with` (a name, or `none`), `statuses_flipped`,
`root_statuses_flipped`, `levels_moved`, `events_new`, `revisions`, `wants_new`,
`proposals_awaiting` and whatever else the comparing branch emits — the lists empty and the
counts zero when there is nothing to compare with. The `DIGEST` line says `no previous
derivation` in that case, as now. A test that asserts a status flip supplies the previous
derivation it needs explicitly — by writing the fixture's first derivation to the path
`previous_derivation` reads, or by a test-only parameter — and never depends on a file a
prior run left behind or on a branch existing. No test is loosened to tolerate a missing key.

**G2. A frame holds what it is about; its roots are its goals.** A frame gains a field
`holds` (provisional name): a list of node ids the frame is about that are not goals of the
ranking. A node in `holds` is attached (rule 1's "attached to nothing" is satisfied by
membership), carries no role or preset, is no root, enters no status, value, stake or unit
of the frame, and is listed in `derived.json`, the index (`in_frames` gains a
`membership: holds` entry beside `role`) and the view under the frame as *held*. A node may
be both held by one frame and a root of another. Then: every docket `or` is dissolved — its
items go into `holds` of the frame it hung under, the docket node files are deleted (not
superseded: they were placeholders the follow-up created, not claims anyone filed) — and
every formal result that is a `shared-claim` root of a frame solely because the round filed
it there (the 2026-10-22 and 2026-10-23 filings; the report says how it told these from
roots that predate the round) moves from `roots` to `holds`. The same for the roots F4
moved to the `legitimacy` line frame on 2026-10-23 "because they bear on none of the three
programmes": they are held, not goals, until a maintainer places them. The report gives
root counts per frame before and after and the count of nodes held.

**G3. Bearing, not answering.** The render line becomes *Registered results bearing on this
item:* and the index key `answered_by` becomes `bearing` (schema `graph-index/3`; §6.1 of
`graph/MAP-AS-CANONICAL.md` updated). An item's `item_status` is unchanged by any registered
result; closing is a maintainer act with a statement of record, as the regulations say.

**G4. An unconfirmed want weighs nothing.** A want with `filed_from: quote` and no
`priority` event by its owner carries weight 0 in the ranking (it is listed, flagged *owner
has not confirmed*, and the pooled list still asks for the word, as now); an explicit
`priority` word gives it the word's weight; `none` still disowns. A want filed by its owner
in a session (no `filed_from`) with no priority word keeps the Default `medium`, since the
owner filed it. `PRIORITY_WORDS` and the want-weight function in `checkers/graph.py`,
`PROTOCOL.md` §2 (owned wants) and the glossary say so; a design-log line records the Default
change; the self-test gains the null input (a quoted want with no word weighs zero; with a
word, the word).

## Part 1 — G1

Fix `previous_derivation`'s callers so the digest is built with the full key set on the
`(None, None)` path. Audit every test under `checkers/tests/` that reads `D["digest"]`:
each either supplies its previous derivation explicitly or asserts only the keys that hold
without one. Run the suite in the CI-shaped checkout described above and paste the tail. If
the CI run at `4dc8811` failed on any test other than the one named, say which and fix it
by the same standard.

## Part 2 — G2

Add `holds` to the frame parser and rule 2 (a held id must resolve; a held node may not
also be a root of the same frame; a held node may not be a frame, a valuation node or a
want — a want is a root of exactly one frame by rule 1); make `attached` read `holds`;
exclude held nodes from the frame's status, value, stake, goal set, safety margin, load and
unit generation, and from `--scope` unless `--scope` names the held node itself; render them
in the view under a *held* heading per frame with their kinds, and in the index as said.
Then the three moves: dockets dissolved into `holds` and deleted; round-filed formal-result
roots to `holds`; F4's line-level legitimacy roots to `holds`. The `spell-out` candidate
logic and the "unspelled frame" flag must not read a frame with roots `[]` and a non-empty
`holds` as unspelled — it is spelled, with nothing yet a goal; say so in the flag text. Update
`PROTOCOL.md` §2 (the frame paragraph and the roots/goals paragraph), §8 glossary (*held*,
*docket* retired), §9 rule 1 and 2; `graph/README.md` where it describes a frame; the
`AGENTS.md` graph section's *Goals are frames and wants* paragraph; and
`graph/MAP-AS-CANONICAL.md` §1 and §6. Design-log lines for the field and for the three
moves. Self-test null inputs: a held id that resolves to nothing; a node both held and a
root of one frame; a want in `holds`.

## Part 3 — G3 and G4

The render line and the index key; the want weight. Both small; each its own commit with
its design-log line.

## Part 4 — reproducibility of `versions.json`

A plain run on another machine (Python 3.13, 2026-10-23) changed `graph/versions.json`'s
recorded `derived.json` hash while two runs on that machine agreed with each other. Find
what in `derivation_hash` or in the derivation varies across interpreters (float repr, set or
dict order, a hash seed, the audit draw's RNG) and make the hash a function of the derivation
alone — a canonical serialization with sorted keys and fixed number formatting, over the
fields the hash is meant to cover. Report the cause; if it cannot be removed in this
follow-up, say so and reserve it, because a `versions.json` that every contributor's plain
run dirties is noise in every pull request.

## Report

Under *Second follow-up of 2026-10-23*: verification first (the checker's OK and DIGEST
lines, `tests/run.py`, the unit-test tail from the CI-shaped checkout, node and root counts
per frame before and after, held counts); the three G2 moves as counts, with the list of
frames whose `roots` became empty; the Part 4 cause; every protocol and checker change with
its design-log line and rule; deviations with reasons; corrections to this prompt; what this
follow-up did not do; and two notes for the maintainers, each with a *turns on* line: that
the branch's history holds five copies of the derived files and a squash merge of the pull
request keeps one, against the repository's merge-commit convention; and that
`stance-and-level` is a plan root only because the protocol makes every frame one, so the
second maintainer may prefer his cruxes back as `shared-claim` roots of `the-program`
grouped by a field rather than a frame — not changed here.

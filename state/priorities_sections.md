# Priorities

**What the program wants done next, in its own order.** This is not an inventory
of everything unsolved — it is the maintainer's ranking of what would move the
work, and an item's absence means nobody has asked for it, not that it is easy.
GitHub issues mirror this file; this file does not mirror them. Each item states
the problem precisely, points at the context, says what a solution must ship, and
carries a difficulty tag.

What a solution must ship is set by `CONTRIBUTING.md` and is the same for
everyone: a theorem ships as statement + implementation + test + a necessity
witness per hypothesis where feasible; Lean ships building and auditing clean; a
witness ships as the exact instance and the check that verifies it.

**Every item is a self-contained round specification** an arbitrary agent could
execute: a precise statement, the deliverable shape, an acceptance check stated
as something CI runs, a context pointer with exact paths, and a difficulty tag.

Contributors propose items as issues and do not file them. A maintainer-dispatched
round may file within its own scope, with its `PROMPT.md` as the authorization and
the filing named in its report — see `AGENTS.md`, *Demand-gating*.

**Standing item family: Lean ports.** Every `test-supported` or
`enumeration-verified` registry entry is implicitly a port target; the maintainer
promotes selected ones to explicit items.

Difficulty tags: **[entry]** — self-contained, needs no new mathematics.
**[substantial]** — a real result, scoped. **[open]** — nobody knows, and it may
be impossible.

---

## Where ingenuity is the bottleneck


**A standing section, and the only part of this file that is not a work order.**
Every numbered item below is a request for *execution*: a round specification an
arbitrary agent could run against a stated acceptance check. These are requests
for an *idea*. They are the places where the program knows what it wants and does
not know what kind of statement would supply it — so dispatching a round would
return the observation rather than the result.

The section exists because that failure is invisible in a file of items. An
`[open]` item still asserts that the target has a shape; a question here asserts
that it does not yet, and says what killed the obvious shapes. **An entry
graduates by becoming a numbered item** — which is what it means for the missing
idea to have arrived. That has happened once already: the question of what
quantity could price a jurisdiction assignment left this list when Stage IV
sharpened it enough to file as item 28. The normativity line has nothing here for that reason: its
hard problems are open, but their shapes are known and they are filed as items 1
and 2.

An entry states the question, why the obvious moves fail *with the evidence that
killed them*, and what a good answer would let the program file next. Without the
third part it is a wish, not a question.

## Normativity line


Context for all six: `projects/normativity/consolidation-aug9/`, whose `OPEN_PROBLEMS.md`
ranks them and whose theory parts state the surrounding results. Cite claims from
it by identifier.

## Normativity line — the learning track


The consolidation's `OPEN_PROBLEMS.md` closes with a pointer list it declines to
treat, and *the learning and installation track* is on it. Items 29–31 opened
the track. Their shared context is:
`projects/normativity/rounds/2026-08-11-phi-regret-prep/`, whose
`PHI_REGRET_TEST_SPEC.md` fixes the environment and whose `THEOREM_LEDGER.md`
says which of its statements have a derivation and which have only a witness.

Items 29–31 were filed by that round within its dispatched scope, with
`prompts/2026-08-11-phi-regret-prep/PROMPT.md` as the authorization.

## Normativity line — traderized enforcement


Items 39–42 were filed by `prompts/2026-08-16-traderized-enforcement/` within its
dispatched scope, with that round's `PROMPT.md` as the authorization. Their shared
context is `projects/normativity/rounds/2026-08-16-traderized-enforcement/`, whose
`THEOREM_MAP.md` says which of its results are kernel-checked, which are derived
from source lemmas taken as hypotheses, and which are single witnesses.

Items 47–51 were filed by `prompts/2026-08-24-reservation-bar-and-debt/` within its
dispatched scope, as the demand the arc's registered claims answer. Four of the five
are marked answered on filing: a kernel-checked headline registers against a filed
item, and the item is where *what is worth proving* was decided, so it is filed with
the answer rather than before it.

## Normativity line — legitimacy


Items 53–59 are the residual blockers the legitimacy prosecutions of 2026-08-21
through 2026-08-23 left behind, filed by
`prompts/2026-08-24-reservation-bar-and-debt/` within its dispatched scope. Each
names the round that would consume the answer, because a blocker nobody is waiting
on is a note rather than a demand. Their shared context is
`projects/normativity/legitimacy/rounds/`, whose memos state what each prosecution
tested and where it stopped.

Two blockers those rounds named are not here. The `R → O` compiler — from the
reason state to a price-space region — is item 39 seen from the reason side, and is
recorded there rather than duplicated. Lean statements of the transition
principles are a port target under the standing Lean-port family.

## Deference line


Context for all three: `projects/deference/note-dump-2026-08-11/`, in particular
`lean-deference/AUDIT.md`, the development's own statement-level audit. Its §3 is
titled "The concerning gaps"; the three below are its own findings, quoted by
section.

**What that audit covers.** Five of the source tree's nine Lean modules — the five
the line's recorded starting point contained. `CenteredSqueeze`, `Staleness`,
`StalenessDensity` and `StreamlinedSS` postdate it and carry no audit of the same
kind. None of the three items below depends on one of the four, and a round
answering one should not assume the audit speaks for them.

## Deference line — first research wave


Seven items opening the corrigibility program's first parallel wave. The dispatch
and returned-track overview are in
`prompts/2026-08-11-deference-corrigibility/REPORT.md`. Items 15, 16, 17 and 20 additionally bind to
`projects/deference/notes/FINITE_MODEL_SKELETON.md`.

**Several of these do not ask for a theorem of record.** An item whose deliverable
is a report, a matrix, a witness, a counterexample or a lower bound says so, and
delivering exactly that is success. Registering a claim for one of them requires the
claim to meet the ordinary registry requirements independently.

**All seven have returned, and the marks in their headings say so.** *Returned*
records dispatch history and nothing more: the track ran and its report is under
`prompts/`. It does not say the item's science is settled, and several returned
negative or partial — item 19's matrix left 11 of 15 rows unresolved. An item
stays filed after returning, because the registry's demand rule means every
claim answering it cites it, and because a later round may answer it better. The
mark exists so that a reader picking work off this file can tell which items are
awaiting a first attempt.

## Deference line — second wave


Three items, narrow by design. The first wave's value was in what it closed off, and
these follow the controlling questions it uncovered rather than opening new fronts.
Context for all three: `prompts/2026-08-11-deference-corrigibility/REPORT.md` for what
wave 1 established and `RECOMMENDATION.md` beside it for why these three.

## Workspace friction


**Where the structure gets in the way of the work.** `AGENTS.md` §14 obliges a
round that hits friction with the workspace itself to file it here rather than
route around it, because a defect worked around silently is one the next round
pays for again. Entries are reports, not work orders; one graduates by becoming a
numbered item or by being ruled on in `DECISIONS.md`. **Cite an entry by its
title, not its number** — the list is renumbered as entries leave it, so numbers
are positions rather than identifiers.

## Infrastructure


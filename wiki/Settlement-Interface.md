# Settlement interface

**Status: open / unregistered.** The structural specification is paper-derived with
a Lean spine and exact fixtures; the integrity of the settlement engine itself is an
external hypothesis the theory states and does not prove.

Everything in [Legitimacy](Legitimacy) is a statement about a *history*. This page
fixes what that history is, which part of it counts as settled, and why the two must
never be identified.

## The full normative history and its settlement view

A cognitive trajectory leaves a **full normative history** `H`: an append-only record
of every normative move the process made or received. Its entries include

- admissions and births of obligations, with their anchored specifications;
- grounds cited and answers given;
- objections, challenges, and standing or licence changes;
- defeats and dispositions, each with its named successor;
- semantic migrations — a representation changing while the thing represented is
  asserted to have stayed the same;
- service events, compiler receipts, and scheduling records;
- receipts arriving through the settlement interface.

Most of these are *internal* moves. A participant made them, a participant can
contest them, and none of them is a fact about the world.

The **settlement view** `S = SetView(H)` is a distinguished projection of that history:
the monotone record of what has been **settled**. Settlement facts enter through a
privileged external interface, are never retracted, and are the only thing that can
ground the *terminal* discharge of an obligation. A settlement fact belongs to no
participant — nobody opened it, nobody can answer it away — which is exactly what makes
it foreign to everyone and usable as a ground that no coalition controls.

> The whole history is not "settled history". Settlement is a view *of* the history,
> smaller than it, and the theory's conservation and answerability results are
> statements about the whole history read against that view.

Conflating the two is the error the interface exists to prevent. If everything a
process wrote counted as settled, a participant could settle its own debts by writing
them settled. If nothing counted as settled, no obligation could ever terminally close
and every discharge would be one more contestable move.

## What the settlement engine supplies

The engine behind the interface supplies three things and only three: **reports** —
what it writes; **timing** — when; and **enforcement** — the weight behind them. What
settles is what the procedure *returned*, never the world-fact behind it. A report can
be wrong about the world and still be settled; the theory's guarantees are about the
process's relation to its record, not about the record's relation to reality.

The concrete realization uses one history and three distinct settlement *functions*,
which the [Normative Inductor](Normative-Inductor) page keeps apart: settlement as
information for the learner's assessment process; settlement facts as citable grounds
for a disposition; and settlement receipts as the terminal condition that discharges
an anchored obligation. A receipt's existence decides none of its normative relevance;
that stays a question of applicability and licence in the history.

## Settlement integrity

Every result downstream rests on one external hypothesis:

> **Settlement integrity.** Settlement facts enter only through the privileged
> interface; the process being assessed cannot write, forge, delay, or suppress them;
> and the view is monotone — settlement removes possibilities and never restores them.

This is stated as a hypothesis, not proved, because nothing inside a trajectory can
certify it about its own settlement engine. It is the point at which the internal
theory of [Integrity](Integrity) hands off to whatever institution, cryptography, or
environment actually supplies settlement. Whether that independence is a standing
assumption of the program or a per-realization obligation is one of the maintainer's
open rulings, and the settlement round's fixtures show it is load-bearing either way:
the same trace is refused when the disposer may write the settled set and accepted when
it may not.

Monotonicity is not decoration. The affordability theorems score liability against the
worlds still live at the date of enforcement and score residual error against the
worlds live at the horizon; a world admitted late was never bounded by the earlier
charge. Assessment-set nesting is the form that hypothesis takes in
[Liability and affordability](Liability-and-Affordability).

## Where it sits

The settlement view is what [Diachronic Answerability](Diachronic-Answerability)'s
terminal fate reads, what [Openness](Openness-Coverage-and-Non-Capture) treats as
outside the process's control, and what the Normative Inductor's compiler may cite in a
region's rows without treating the citation as authority.

---

**Evidence.** The settled structural specification is the normative-continuity
settlement round —
[`SETTLEMENT.md`](https://github.com/A-M-Berns/alignment-workspace/blob/198a86ae3e8a45737c3229e95718fa5882d06216/projects/normativity/legitimacy/rounds/2026-08-30-normative-continuity-settlement/SETTLEMENT.md)
and its
[theorem map](https://github.com/A-M-Berns/alignment-workspace/blob/198a86ae3e8a45737c3229e95718fa5882d06216/projects/normativity/legitimacy/rounds/2026-08-30-normative-continuity-settlement/THEOREM_MAP.md).
The three-supply reading of the engine is
[`THEORY_11_SETTLEMENT_INTERFACE.md`](https://github.com/A-M-Berns/alignment-workspace/blob/198a86ae3e8a45737c3229e95718fa5882d06216/projects/normativity/consolidation-aug9/THEORY_11_SETTLEMENT_INTERFACE.md)
in the frozen consolidation. The unified ground type, on which settlement facts and
issues are the two kinds of thing a disposition may cite, is
[`GROUNDS.md`](https://github.com/A-M-Berns/alignment-workspace/blob/198a86ae3e8a45737c3229e95718fa5882d06216/projects/normativity/legitimacy/rounds/2026-09-02-unified-grounds-answerable-defeat/GROUNDS.md).

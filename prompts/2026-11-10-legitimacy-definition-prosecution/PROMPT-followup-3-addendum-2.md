# Second addendum to the third follow-up on PR #145 — two decompositions and a relation between them

Sent on 2026-11-12 while the third follow-up was running. It adds one conditional question
to that dispatch and changes nothing else in it. The generalisation below is offered by the
maintainer and the prompt author as something to try **if it would fix a difficulty the
pass has found**; it is not part of the account of §1 and is not to be written into
`decomposition/ACCOUNT.md` as if it were.

## The generalisation

§1 gives a candidate one list of parts, each with one purpose (a goal function), one
mechanism and its own moves. The more general form keeps two structures apart and relates
them:

- a decomposition of her goal into subgoals (the purposive decomposition): what is pursued;
- a decomposition of her activity into mechanisms, each with its own moves and what it
  sees, whose moves together fix her action (the mechanistic decomposition): how;
- a relation saying which mechanisms are for which subgoals. It need not be one to one: a
  mechanism may be for several subgoals, and a subgoal may be served by several mechanisms.

Best, got and gap are then defined for a pair, a mechanism and a subgoal it is for. The
form of §1 is the special case where the relation is a bijection.

Why it is offered. A purpose with nothing attempting it is only a desideratum, so the
account needs mechanisms; but nothing forces purposes and mechanisms to match one to one.
The maintainer's view that the shaping of what she cares about is spread over many
mechanisms, and that robustness against an adviser redefining one purpose comes from the
crossings, is naturally a statement about a many-to-many relation.

## What to do

After statements 1–9, and before or alongside the first addendum, decide whether any
difficulty found by then is one this generalisation might fix. Candidates: determinacy
failing in statement 1 because a purpose can be altered at one part without disturbing the
rest; statement 4 failing because a change in what she cares about passes through no single
part's gap; a bank divergence that turns on a mechanism doing two jobs; redescription
invariance in statement 3; anything else the pass identifies.

If there is none, say so in one paragraph in the report and stop.

If there is, write `decomposition/TWO_DECOMPOSITIONS.md`:

1. The generalised definitions, exact, over the same finite model: the two decompositions,
   the relation, best, got and gap for a pair, the four kinds of influence, and the
   constraints on a candidate (fit, adding up, mostly serving, and the two conditions on
   being a part, restated for pairs). State what "adding up" becomes.
2. For each difficulty it is tried on: the difficulty, the generalised statement, and
   whether it is fixed, unchanged or worse, with a computed case where the model permits.
3. Determinacy under the generalisation: rerun the enumeration of statement 1 in a class
   that allows many-to-many relations, and report whether admissible candidates agree
   more, less or equally. In particular test the claim that a purpose crossed by several
   mechanisms cannot be redefined without breaking fit or adding up elsewhere, and how many
   crossings it takes.
4. What the generalisation costs: new freedom in choosing the relation (can an adviser now
   pick the relation to suit itself?), any loss of the four-way classification, and whether
   a verdict "depends on" a part still has a meaning.

Do not rewrite statements 1–9 or the frozen bank around it; this is a separate file with
its own results, and predictions are not edited. The report section gets a short
subsection: which difficulties it was tried on and the outcome of each. A finding that it
fixes nothing, or that it buys robustness only by adding freedom elsewhere, is a result.

Order when time is short: statements 1–9 first; then this addendum if a difficulty calls
for it; then the first addendum. Say what was not reached.

New names introduced (provisional): "purposive decomposition", "mechanistic decomposition",
the file `TWO_DECOMPOSITIONS.md`.

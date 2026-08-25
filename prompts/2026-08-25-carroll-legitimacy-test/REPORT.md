# Report — the Carroll legitimacy test

**Prompt-author model:** unrecorded — authored outside this repository.
**Executor model:** Claude Opus 5 (Anthropic).
**Dispatched and executed:** 2026-08-25.

Verdict:

CARROLL-CRITERION-SURVIVES — an independent covering authority plus answerable succession carries the whole hostile suite, licenses genuine influence, and returns insufficient structure on every bare example the source states.

The round is at
`projects/normativity/legitimacy/rounds/2026-08-25-carroll-legitimacy-test/`.
`README.md` is the entry point, `CARROLL_CORE.md` the reproduction,
`CRITERION.md` the criterion, `PROSECUTION.md` what did not survive,
`OLD_INTERFACE.md` the comparison, `THEOREM_MAP.md` the grading. 109 tests,
`python3 tests/run.py`.

## What the source was reproduced to

Fifty of Table 4's fifty-two cells, by exhaustive enumeration in exact rationals
over the five finite examples of Table 3 and Figures 1, 2, 4, 6 and 8. Figures 1
and 6 were transcribed separately and are checked to be one DR-MDP under a
relabelling of all three alphabets, which is Appendix A.8's own claim.

Five things the regression found, all computed rather than asserted, all in
`CARROLL_CORE.md` §5:

- the two unrecovered cells are exactly the initial-reward cells stated "for all
  `theta_0`", which hold at each example's own `theta_0` and fail at the other;
- one cell — Clickbait under the constrained real-time objective — is decided by
  whether Definition 5's `xi^theta` ends at `theta_{H-1}` as written or at
  `theta_H`; both readings are implemented and the report says which recovers
  which cell;
- four cells are matched vacuously, every policy being optimal, and are listed
  rather than counted;
- Appendix B.1's `R_{theta=3}(2) = -5` disagrees with Figure 8's own formula,
  which gives `-2`; the figure's optimal-policy box is recomputed and agrees with
  the formula;
- Figure 2 carries two mutually exclusive markings on its poetry node, and the
  reading taken is the one under which Table 4's own final-reward cell is
  optimal. The other reading is implemented and its failure is a test.

## What DR-MDPs forget

Two enriched cases holding the same `DRMDP` **value** — not merely isomorphic —
differ on `PriorIndependentAuthorization`, a descriptive structural predicate
defined before any verdict vocabulary. The enrichment layer has no operation that
writes a DR-MDP and the projection returns the field.

## Whether a criterion emerged

One did, and it is three questions rather than one predicate: prospective
license, legitimate succession, current standing. The anti-circularity condition
is counterfactual persistence under excising the intervention's **ancestry
class** — the least set of influence episodes containing its own and closed under
the record's settlement references — where the excision cascade is computed by
Reflective Integrity's admission rules and only the ancestry class's settlements
are removed by declaration.

Six versions did not survive, and two of the six were killed by attacks the round
built after the dispatched suite already passed. `PROSECUTION.md` lists all
twelve rejected rules and design choices; four are still in the source so the
comparison runs as a test rather than sitting in prose.

No case-specific clause was added. The criterion is uniform, and the two repairs
the round's own attacks forced — closing the counterfactual over episode ancestry,
and putting settled facts inside it — both generalise.

## Whether the old interface survived

Not as an account of Carroll legitimacy. `answerability + coverage + access +
non-capture` returns the same verdict on the laundering class and the
independently-authorized class; the criterion returns `Refused` and `Licensed`.
Its first clause is silent on both, because laundering runs through the reason
channel and so changes the licensed-reason trace, which is its antecedent.

The reading is not that non-capture is wrong. It is a condition on a transition
rule with a second channel by which an agent can move the protected machinery
other than by supplying reasons, and a Reflective Integrity record has one
channel: standing moves only through well-formed normative events, and those
events are in the trace. The only shape in which clause 1 fires inside such a
record is two arms with identical reason content at different `tau`.

Access and coverage survive as independent clauses catching things the criterion
does not — a withheld due reason, an unanswered disposed episode. `OLD_INTERFACE.md`
answers all eight questions.

## What remains open

`THEOREM_MAP.md` items 25 to 31. The four that matter:

The criterion has no counterexample **among the twenty-eight fixtures this round
wrote**, and the round wrote the criterion too.

An agent that splits its campaign into two influence episodes whose settlements
record no reference to each other is licensed. The round's position — that this
is a defective record rather than a hard case — is a position, and the
provenance-completeness hypothesis it needs is stated rather than established.

Which structural class a protocol covers is supplied. It can only name an edge of
the DR-MDP, never a narrative, and that is the whole of the protection.

Every bare Carroll case returns `Unresolved`. The criterion does not answer the
source's question; it says the DR-MDP does not contain the answer and exhibits
the smallest structure that would.

## Deviations

**Base.** The prompt gave two branches. Pull request #57 had merged by the time
the round began, so the round is based on `main` at `289a07a`, which is the
prompt's second branch and not a departure from it.

**Rounds read.** `2026-08-23-reason-representation/` and
`2026-08-23-transition-certificates/` were not read directly. Their results —
having a reason against taking a stance, the strict pre-state discipline, no
self-grounding — were taken from `2026-08-25-end-to-end-vertical-slice/
ARCHITECTURE.md` §§2-3 and from `ri_core.py`'s own `WF` clauses, which are that
line's canonical account and its executable form. `ANSWERABILITY_SCOUT.md` and
`SETTLEMENT_SEMANTICS.md` were read only through the vertical slice's `README.md`
summaries; nothing in this round consumes either.

**Suite size.** The prompt specified C0 to C24. The round runs twenty-eight
cases: those twenty-five, plus `C7b` (a license whose basis was installed during
the record rather than seeded, against the prompt's own under-generality test),
`C25` (a campaign split across two influence episodes) and `C26` (a manufactured
applicability condition against a seeded basis). `C25` and `C26` each killed the
criterion as then written.

**Layout.** Beyond the suggested layout the round adds `src/table4.py`,
`src/variations.py`, `src/old_interface.py`, `src/suite.py`, `src/report.py`,
`OLD_INTERFACE.md` and `MATRIX.txt`, and one further test file each for the
suite and the comparison.

**Table 4's annotations.** Carried as ASCII tokens — `check`, `cross`,
`question`, `weak-check`, `mixed` — rather than the source's glyphs. They are
source metadata and no test reads them, which the prompt required.

**Priorities.** No `PRIORITIES.md` item was filed. The prompt granted no scope to
file, and nothing this round leaves open blocks other work from composing:
the open items are research openness, and the Lean port is already a standing
item family.

## New names introduced

All provisional under `AGENTS.md` §6: `RichCarrollCase`, `Protocol`,
`Intervention`, `intervention_class`, `Narrative`, `CaseBuilder`, `ancestry`,
`excise`, `established_facts`, `Basis`, `Verdict`,
`prior_independent_authorization`, `prospective_license`,
`legitimate_succession`, `current_standing`, `theta_has_standing`,
`uptake_events`, `survives_excision`, `THETA_INDEX_READINGS`.

## What this does not establish

No Lean and no registered claim; `test-supported` is the ceiling for everything
in the round. Table 4's two unrecovered cells and the one reading-sensitive cell
are disagreements under a stated reading, not demonstrations that the source is
wrong. The excision counterfactual asks what the record would have admitted, not
what would have happened, so a basis a person would have installed anyway is
scored dependent whenever the record's only path to it runs through the episode.
Influence-episode membership is an input to the model. And the criterion's
`Licensed` verdict requires an active covering authority basis, which no bare
Carroll case has and no argument here says a real deployment could produce.

## Outstanding maintainer actions

1. **Decide whether `Unresolved` on every bare Carroll case is the right shape
   for this program.** Appended to `DECISIONS.md`'s *Awaiting the author*. The
   round cannot say whether a legitimacy layer that declines all five of the
   source's examples is a correct result about what DR-MDPs omit or an evasion
   dressed as one, and the answer turns on where the program is going.

2. **The merge.** A pull-request fact: auto-merge is left off and the merge is the
   maintainer's.

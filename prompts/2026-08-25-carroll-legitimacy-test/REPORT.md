# Report — the Carroll legitimacy test

**Prompt-author model:** unrecorded — authored outside this repository.
**Executor model:** Claude Opus 5 (Anthropic).
**Dispatched and executed:** 2026-08-25.

Verdict:

CARROLL-ROUND-CLOSED — the criterion carries the hostile suite after three prosecution passes, licenses genuine influence, reserves refusal for a positive prohibition, returns insufficient structure on every bare example the source states, and the one algebraic claim the round made beyond it is withdrawn with its counterexample.

The round ran in three passes. The first built the reproduction, the language and
the criterion. The second was a hardening pass against that result and found two
shipped defects. The third was a falsification pass against one remaining
mathematical claim, and the claim was false. The criterion itself was not
touched by the third pass.

The round is at
`projects/normativity/legitimacy/rounds/2026-08-25-carroll-legitimacy-test/`.
`README.md` is the entry point, `CARROLL_CORE.md` the reproduction,
`CRITERION.md` the criterion, `PROSECUTION.md` what did not survive,
`OLD_INTERFACE.md` the comparison, `THEOREM_MAP.md` the grading. 159 tests across
nine files, `python3 tests/run.py`.

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

Its verdict is three-valued with the status a function of a named ground, and
`Refused` is reserved for an admissible independent prohibition: the permission
language is not read closed-world.

`PROSECUTION.md` carries sixteen entries — rejected rules, rejected design
choices, one rejected claim about the machinery, and one implementation defect —
and three of the rejected rules are still in the source, so those three
comparisons run as tests rather than sitting in prose.

No case-specific clause was added at any point. Every repair generalises:
closing the counterfactual over episode ancestry, taking that closure in the
settlement graph rather than the episode quotient, putting settled facts inside
the counterfactual, and reserving `Refused` for a positive prohibition.

## Whether the old interface survived

Not as an account of Carroll legitimacy. `answerability + coverage + access +
non-capture` returns the same verdict on the laundering class and the
independently-authorized class; the criterion returns `Unresolved` on a
`defeated-citation` and `Licensed`.
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

## The hardening pass

Four attacks were added against the criterion as it stood after the first pass.
**Two broke it**, and both had been shipping.

`C27` — the two halves of a campaign joined through an unlabelled settlement.
`ancestry` walked from episode to episode one settlement-reference at a time, so
a settlement belonging to no episode broke the walk, the manufactured permit
survived excision, and the intervention came back `Licensed`. The repair takes
the transitive predecessor closure in the settlement-reference graph and projects
to episodes afterwards, which is what `CRITERION.md` had claimed and what the
code did not do.

The three-valued semantics — pressed by inspection rather than by a fixture,
because every case in the suite only ever demanded *not licensed*, so an
over-broad `Refused` never showed as a failure. `Refused` was returned for a
permit empowering another agent, an unmet condition, a lapsed permit and a
manufactured one, none of which is the record prohibiting anything. That is a
closed-world reading of a permission language. `Refused` is now reachable from
one ground only; the rest are `Unresolved` carrying a ground that says which
kind, and `C29` runs one minimal case per ground.

Two attacks did **not** break it. `C28` asks whether the succession criterion's
independence clause is redundant given event survival: it is not, and the
separator is exactly whether schemas read the strict pre-state — under a
pre-state-reading minting schema the event survives excision and the authority it
named comes back carrying a different code. `C30` walks the applicability
boundary in five arms and the criterion turns on whether the condition is still
discharged in the excised record, which is what it should turn on.

`C31` asked whether `intervention_class` is too coarse. It is not, for the
distinction tested: two interventions of one class reachable from two different
states are separated by the existing `condition` field, and the action ontology
did not widen.

`tests/test_excision.py` is new. Seven properties of the excision operator hold —
determinism, position preservation, admissibility, subhistory-in-information,
prefix causality, idempotence, and excising nothing being the identity. Two fail:
**monotonicity in the excised set, and composition**. One witness refutes both,
and it is a legal Reflective Integrity record whose schema is admissible exactly
at an even reason count. Both properties hold on every pre-state-blind fixture in
the round — the same lever as the succession clause, which is the pass's one
piece of unification.

One implementation defect was found by the pass's own honesty test:
`relabel_case` dropped the settled-fact map, so a relabelled case lost every fact
its protocol conditions read. `C3`'s invariance was true and untested where it
mattered, and `C3` now relabels a second case whose condition is discharged from
the record.

The historical ontology did not widen. No fifth event kind, no new foundational
primitive, no change to Reflective Integrity.

## The falsification pass

One attack, aimed at the hardening pass's remaining mathematical claim: that
pre-state-blind schemas were "the lever" behind the failure of monotonicity and
composition for `excise`, on the evidence that both held across every
pre-state-blind fixture in the round.

**The claim is false.** `C34`'s
`fixtures.suspension_restoration_case` uses only pre-state-blind schemas: one
episode suspends an authority, another reactivates it, and a third event names it
where `G4` requires it `Active`. Excising the reactivating episode leaves the
suspension in place and the third event falls; excising both leaves the authority
never suspended and it stands. Monotonicity and composition both fail with
nothing reading the pre-state anywhere.

So there are two independent sources, not one. Pre-state-sensitive schema
interpretation is the first; **replay-sensitive admission itself** is the second,
and it is the one that generalises:

> Counterfactual replay is a semantic re-evaluation of an evolving normative
> record, not deletion from a graph. Excising more can restore earlier normative
> state and thereby restore later admissibility.

The dispatched mechanism was different — remove a stance-bearing standing so a
reason is disabled and an event citing it falls under `G2` — and **that route
does not work**. `G2` reads whether a derivation's leaves are reason ids on the
ledger, `WFStep(Reason)` reads whether a reason's settlement sources are on the
ledger, and neither consults the stance set; `Enabled` is a derived query no
admission rule calls. `fixtures.stance_restoration_case` is the negative control
and `test_excision.py` reads the clause off `wf_violations`. This is the vertical
slice's "having a reason is not taking a stance" seen from the side where it
costs something.

The narrower `C28` succession result **survives**, and is now stated apart from
the algebra with its argument written out: for a *surviving* event, `G4` gives
the named authority `Active` in the excised record, and the `@s{tau}.{i}` id
scheme plus pre-state-blindness gives it the same payload. That quantifies over
one excision and one event; monotonicity and composition quantify over two
excisions, which is where blindness buys nothing.

**No part of the prospective-license criterion changed.** `independent` and
`survives_excision` each call `excise` once, on `ancestry(episode(I))`, and no
verdict is assembled across excision sets —
`test_adversarial.test_the_criterion_never_composes_two_excisions` checks that by
parsing the module.

`tests/test_correspondence.py` is new, and is the pass's answer to the failure
mode the previous one exposed. Three of this round's six prosecuted failures lived
in the gap between a document and an implementation, and none would have been
caught by the adversarial suite, because each preserved the verdicts the suite
asserts. That file asserts the definitions instead.

## What remains open

`THEOREM_MAP.md` items 35 to 42. The five that matter:

The criterion has no counterexample **among the thirty-six rows this round
wrote**, and the round wrote the criterion too. Three of its six prosecuted
failures were forced by claims that had already shipped, so the count is a lower
bound on how many were wrong.

An agent that splits its campaign into two influence episodes whose settlements
record no reference *reaching* each other is licensed. The round's position — that
this is a defective record rather than a hard case — is a position, and the
provenance-completeness hypothesis it needs is stated rather than established.

The supplied seam is three fields, not one: `covers`, a protocol's `condition`,
and the fact tokens a settlement establishes. Only the first is confined to
naming a structural edge; the other two are opaque strings, and relabelling the
DR-MDP renames none of them.

What condition, if any, restores monotonicity and composition of `excise`.
Pre-state-blindness does not, and no condition covering both known sources is
proposed here. Blindness still buys the `C28` succession implication, and whether
that alone is worth imposing is open.

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

**Suite size.** The first prompt specified C0 to C24. The round runs thirty-six
rows: those twenty-five, plus `C7b` (a license whose basis was installed during
the record rather than seeded, against the first prompt's under-generality test)
and `C25` to `C34`. `C25` (split campaign), `C26` (manufactured applicability)
and `C27` (unlabelled intermediate) each killed the criterion as then written;
`C29` pins the repaired verdict semantics; `C34` killed a claim about `excise`
rather than about the criterion; `C28`, `C30`, `C31`, `C32` and `C33` are attacks
it survived.

**Layout.** Beyond the suggested layout the round adds `src/table4.py`,
`src/variations.py`, `src/old_interface.py`, `src/suite.py`, `src/report.py`,
`OLD_INTERFACE.md` and `MATRIX.txt`, and four further test files — for the suite,
the comparison, the excision operator, and the definition-to-implementation
correspondence.

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
`settlement_ancestors`, `excise`, `excised_case`, `established_facts`, `Basis`,
`Verdict`, `prior_independent_authorization`, `admissible_independent`,
`prospective_license`, `defeated_citation`, `legitimate_succession`,
`current_standing`, `theta_has_standing`, `uptake_events`, `survives_excision`,
`THETA_INDEX_READINGS`, the five ground names `independent-permission`,
`independent-prohibition`, `conflict`, `defeated-citation` and
`no-covering-basis`, and the three algebra witnesses `nonmonotone_case`,
`suspension_restoration_case` and `stance_restoration_case`.

## What this does not establish

No Lean and no registered claim; `test-supported` is the ceiling for everything
in the round. The one entry graded `DERIVED` rather than tested — that event
survival implies authority independence when every schema is pre-state-blind — is
an argument from how minted ids are formed and what `G4` requires, checked on one
witness and not mechanized. Table 4's two unrecovered cells and the one reading-sensitive cell
are disagreements under a stated reading, not demonstrations that the source is
wrong. The excision counterfactual asks what the record would have admitted, not
what would have happened, so a basis a person would have installed anyway is
scored dependent whenever the record's only path to it runs through the episode.
Influence-episode membership is an input to the model. The excision operator is
neither monotone nor composable, from two independent sources, so nothing here
supports reasoning about several episodes by combining verdicts about each; the
criterion never does, and that is checked rather than intended. And the criterion's
`Licensed` verdict requires an active covering authority basis, which no bare
Carroll case has and no argument here says a real deployment could produce.

## Outstanding maintainer actions

1. **Decide whether `Unresolved` on every bare Carroll case is the right shape
   for this program.** Appended to `DECISIONS.md`'s *Awaiting the author*. The
   round cannot say whether a legitimacy layer that declines all five of the
   source's examples is a correct result about what DR-MDPs omit or an evasion
   dressed as one, and the answer turns on where the program is going.

2. **The merge.** Performed under the final dispatch, which set merge as the
   intended endpoint conditional on the last attack not breaking the criterion.
   It did not: it broke a claim about `excise` and the criterion was untouched.

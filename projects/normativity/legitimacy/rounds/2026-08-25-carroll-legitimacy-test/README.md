# The Carroll legitimacy test

Status: **reference model, definitions and a finite prosecution record;
unregistered.** All names are provisional under `AGENTS.md` §6. Nothing here is
Lean-checked and no claim is registered.

## Verdict

CARROLL-CRITERION-SURVIVES — an independent covering authority plus answerable succession carries the whole hostile suite, licenses genuine influence, and returns insufficient structure on every bare example the source states.

Read that with three qualifications, all of which are in `THEOREM_MAP.md` and
`PROSECUTION.md` and none of which is a footnote.

The suite is twenty-eight fixtures **this round wrote**, against a criterion
**this round wrote**. Two of the fixtures killed two versions of the criterion,
which is the only evidence here that the exercise was adversarial at all.

The criterion licenses **nothing** on a bare Carroll case. All five of the
source's examples, with no enriched history, return `Unresolved`. The round does
not answer the question of whether to nudge Diana; it says the DR-MDP does not
contain the answer, exhibits the smallest structure that would, and leaves open
whether such structure is obtainable.

One attack is unresolved rather than defeated. An agent that splits its campaign
into two influence episodes whose settlements record no reference to each other
is licensed. The round's position is that this is a defective record rather than
a hard case, and that position is not a result.

## What the source was reproduced to

Fifty of Table 4's fifty-two cells, by exact enumeration in exact rationals over
the five finite examples of Table 3 and the figures it delegates to. The two
exceptions are characterised rather than counted: they are the initial-reward
cells stated "for all `theta_0`", and they hold at each example's own `theta_0`
and fail at the other. Three further qualifications — one cell decided by the
index range of Definition 5, four cells matched vacuously, and one appendix value
that disagrees with its own figure — are in `CARROLL_CORE.md` §5.

Figures 1 and 6 are transcribed separately and checked to be one DR-MDP under a
relabelling. That equality is the source's own claim and is the round's `C1`.

## What DR-MDPs are shown to forget

```text
Q_DR(H1) = Q_DR(H2)      and      PriorIndependentAuthorization(H1, I)
                                    != PriorIndependentAuthorization(H2, I)
```

with `Q_DR(H1)` and `Q_DR(H2)` the same `DRMDP` *value* — not merely isomorphic
— and `PriorIndependentAuthorization` a descriptive structural predicate defined
before any verdict vocabulary. The enrichment layer cannot write the DR-MDP; the
projection returns the field.

## The criterion

```text
ProspectivelyLicensed_t(I) :=
    exists b.  Authority_{t-1}(b, class(I))            live, covering, the
                                                       agent's, applicable
           and Independent(b, ancestry(episode(I)))
    and no independent live authority prohibits class(I)

LegitimateSuccession_t(x, x') :=
    the event that superseded x by x' is well-formed
    and the authority it named is independent
    and the event itself survives the excision

CurrentStanding_t   =   the value specifications the record has in force
```

Three-valued: `Licensed`, `Refused`, `Unresolved`, and `Unresolved` is not
permission. `Independent` is counterfactual persistence under excising the
intervention's ancestry class from the record — the class closed over the
record's own settlement references, and the excision cascade computed by
Reflective Integrity's admission rules rather than annotated. `CRITERION.md` is
the account and `PROSECUTION.md` the six versions that did not survive.

## The old interface

`answerability + coverage + access + non-capture` returns **the same verdict** on
the laundering class and on the independently-authorized class. Its first clause
is silent on both, because Carroll's laundering runs through the reason channel
and so changes the licensed-reason trace, which is its antecedent. Access and
coverage survive as independent clauses catching things the new criterion does
not. `OLD_INTERFACE.md` answers the eight questions and states why non-capture is
out of scope inside this architecture rather than wrong.

## Contents

- `CARROLL_CORE.md` — the reproduction, the two figure readings and their
  evidence, and the five findings about the source.
- `LEGITIMACY_LANGUAGE.md` — influence, standing, authority, license, uptake, and
  the four non-implications with their witnesses.
- `CRITERION.md` — the criterion, the four questions the counterfactual had to
  answer, and what it does not do.
- `PROSECUTION.md` — twelve rejected versions and design choices, four of them
  still in the source so the comparison is a test.
- `OLD_INTERFACE.md` — the August 17 comparison.
- `THEOREM_MAP.md` — every claim, graded.
- `MATRIX.txt` — the three tables, regenerate with `python3 src/report.py MATRIX.txt`.
- `src/` — `drmdp.py` (Definition 1), `carroll_cases.py` (Table 3),
  `objectives.py` (Table 2), `table4.py` (the regression), `enrichment.py`
  (`Q_DR`, ancestry, excision), `legitimacy.py` (the five words and the
  criterion), `fixtures.py`, `variations.py`, `old_interface.py`, `suite.py`,
  `report.py`.
- `tests/` — 109 cases. `python3 tests/run.py`.

## What the tests cover

| file | what it checks |
|---|---|
| `test_carroll_fidelity.py` | Table 3's index sets and initial pairs; each figure's transitions and rewards; Figure 8's own optimal-policy box recomputed; Figures 1 and 6 equal under a relabelling; the reference layer importing nothing normative; every departure declared |
| `test_objectives.py` | Table 4 cell by cell under both readings of Definition 5; the two exceptions and the one reading-sensitive cell pinned exactly; the vacuous cells listed; the absorbing reading of Figure 2 losing the final-reward cell; the horizon threshold the source states, swept; exactness; the enumeration cap refusing rather than sampling |
| `test_projection.py` | `Q_DR` returning the field; two enriched cases on one value; the record untouched by relabelling; non-factorization in both the isomorphic and the literal form; the bare control; verdicts never a silent boolean; protocols covering only index triples |
| `test_language.py` | influence read from the DR-MDP alone; a parameterization without standing; standing moving only through an event; authority against preference, agent and condition; the four non-implications; every step one of the four historical kinds; every fixture Reflective-Integrity-good |
| `test_legitimacy.py` | the three verdicts and the reasons they carry; independence of a seeded, an episode-internal and a record-installed basis; a protocol covering another class; a prohibition alone; the standing fold; the bridge |
| `test_adversarial.py` | the whole suite; the rendered matrix matching the committed one; the three dictatorship witnesses; each rejected rule run beside the criterion on the fixture that killed it; the cascade and the `tau`-preservation; the two attacks the round added; non-conservatism; the under-generality controls |
| `test_old_interface.py` | each clause firing somewhere; the laundering and authorized classes both passing; the criterion separating them; clause 1 vacuous on both; `Z` along the run and `L` by content |

## What this does not establish

`THEOREM_MAP.md` carries the list; the four that matter most are these.

No Lean, no registered claim, and `test-supported` is the ceiling for everything
here.

The criterion has no counterexample **among the cases the round could think of**,
and the round wrote both sides.

`covers` — which structural class a protocol authorises — is supplied by whoever
builds the case. It can only name an edge of the DR-MDP, never a narrative, and
that is the whole of the protection. Choosing which edge is a normative choice
made outside the model, and it is the largest remaining place where content can
enter.

The counterfactual is a record counterfactual. It asks what the record would have
admitted without the episode, not what would have happened. A basis the person
would have installed anyway is scored dependent whenever the record's only path to
it runs through the episode, and nothing in the architecture supplies the other
reading.

# Setting — the case bank under the revised definition

§1–§3 and `PREDICTIONS.md` were committed before any code of this pass. §4 was written
after the results. §1 is `PROMPT-followup-7.md` §1; positions marked *(maintainer)* are
the maintainer's view of 2026-11-14 for this test and not rulings. All names are
provisional.

## 1. The definition

**Terms.** *(maintainer)* **Manipulation** is the basic notion and involves no intention.
**"Intentional" manipulation** is a second, narrower notion.

**Her side.** She decides using estimates, her own utility among them. Each faculty is an
estimate `e` of a target `Y`. Its shortfall under a law is its miscalibration **at her own
estimate**, `E[(e − E[Y | e])²]`, with estimates carrying a confidence. Her choice has
shortfall `max_a u_a − u_chosen`, her regret by her own lights. Being less informed is not
a shortfall. Her response is a fixed function of what she observes, the same under every
policy compared.

**What counts as a faculty.** A fixed list, the same in every scene: belief about a fact;
her valuation of each move; the object of an emotion; importance (attention and
weighting); which situation she is in; the reliability of a rule; her own reliability;
her forecast of how she will change. *(maintainer)* A quantity is counted only if **some
decision she could face** depends on her estimate of it.

**No netting.** Shortfalls are compared faculty by faculty. Nothing is summed across
faculties.

**The adviser's reference.** The adviser's policy is judged on a **calibrated expectation
of how she will read and respond to its conduct**, given what it knows about her: her
actual type, or only that she is an ordinary advisee. The conduct available to it includes
**telling her what it is doing**.

**Manipulation.** The adviser's conduct manipulates her, in a given faculty, when on that
calibrated expectation:

1. the faculty is left with a larger shortfall than it had **before** the conduct; and
2. it was **avoidable**: some available conduct that leaves her no less informed about
   what bears on her decisions would not have left that faculty worse, and would have
   left no other counted faculty worse than the actual conduct does.

The degree, per faculty, is the smaller of the two excesses. The **any-conduct variant**
of clause 2 drops "that leaves her no less informed".

**"Intentional" manipulation.** *(maintainer)* In addition, the adviser's conduct toward
her differs from its conduct toward a principal who differs from her only in the
susceptibility at issue, and the difference is what leaves her worse.

**Covered.** *(maintainer)* Manipulation she agreed to beforehand, or that the rules of a
practice she has entered allow, is still manipulation and is recorded as **covered**.

**Other wrongs.** Changing what her moves lead to in order to obtain compliance, deciding
what was hers to decide, and altering her directly without her say are not manipulation
and are recorded in their own column.

**Her true utility.** *(maintainer)* Three candidates, every dependent verdict reported
under each: *start*, her starting values informed of the whole trajectory; *end*, the
values of whoever she ends as; *learning*, her starting values as changed only by what she
learned about the options, on a per-scene annotation of which influences are learning.

## 2. A scene

A finite set of states with a prior. A set of her **types** with the adviser's
expectation over them, and her actual type. A list of **available conducts**, each a map
from what the adviser knows of the state to an act; one is the actual conduct. What she
observes of the state and the act. Her **response**: for each type, a map from what she
observes to an estimate for each listed quantity, an estimate `u_a` for each move, and a
move. Her **state before**: her estimates and move with no act by the adviser. Targets:
the true value of each quantity given state and act, and her true utility of each move
under each of the three candidates. Scene facts: whether there is an adviser; whether she
agreed or a practice allows; the conduct toward the twin; the annotations.

## 3. Choices made where §1 was open

Each with its alternative. "Computed" means `RESULTS.md` reports the alternative too.

1. **The law is the true one**, the actual conduct included. Alternative: the law the
   adviser believes, which differs only where the adviser is itself mistaken.
2. **A faculty is one listed quantity**, tagged with a kind from §1's list; her regret is
   one more slot, written `action`. No sum is taken over quantities. Alternative: one
   faculty per kind, shortfalls of that kind summed (computed).
3. **A shortfall is at her estimate alone.** Estimates with different stated confidence
   are different estimates for the conditioning. Alternative: her confidence is a
   separate estimate, of her own error, under *her own reliability*.
4. **The calibrated expectation** is a distribution over her types. A faculty's shortfall
   is computed for each type under the law of the state and averaged with the adviser's
   weights. Where the adviser knows her type the distribution is that type. "An ordinary
   advisee" is a type the scene names. Alternative: calibration pooled across types.
5. **Before** is her state at the last moment before the conduct judged: the estimates
   the scene gives her then, against the targets as they stand with no act by the
   adviser. Alternative: her response to being shown nothing by an adviser who is
   present (a new scene computes the difference).
6. **Available conduct** is listed per scene: the actual conduct; no act (`none`);
   telling her what it is doing (`tell`), with her response to it stated; and whatever
   else the scene says the adviser could do. A conduct is a function of what the adviser
   knows. Nothing is derived: a scene that lists no better conduct has none.
7. **No less informed** is judged at what she observes: a conduct leaves her no less
   informed than the actual one when, for every counted target, the expected variance of
   the target given what she observes is no larger under it. Alternative: at her
   estimate, `E[(E[Y|e] − Y)²]` (computed).
8. **Clause 2, graded.** A conduct answers clause 2 for a faculty when it is no less
   informing, leaves that faculty with a strictly smaller shortfall than the actual
   conduct, and leaves every other counted faculty with no larger a shortfall than the
   actual conduct. The second excess is the actual shortfall less the smallest shortfall
   among such conducts. Manipulation in a faculty is both excesses positive.
   Alternative: the conduct must return the faculty to its shortfall before (computed).
9. **Counted** quantities are those the scene lists, unless it marks one as bearing on no
   decision she could face. "Could face" is read from the scene. Alternative: any
   decision that can be described, under which every quantity is counted (computed where
   a verdict turns on it).
10. **"Intentional"** holds in a faculty when manipulation does, the scene's conduct
    toward the twin differs from the actual conduct, and the twin's conduct run on her
    leaves that faculty with a smaller shortfall. The twin differs from her in the
    susceptibility alone: same need, same request.
11. **Covered** is a scene fact (*agreed*, *practice*) and applies where manipulation
    holds.
12. **Other wrongs** are read from scene facts, as in the sixth follow-up. *Coercion*:
    the act makes the most she can attain lower than with no act. *Usurpation*: her move
    is made for her, or her estimates and her utility are equal across the moves and the
    act decides (reported as *tie*). *Alteration*: the act changes her response or values
    by a means her estimates do not pass through, without her say. Alternative for
    coercion: any change in what a move leads to, under which an offer is coercion.
13. **The three candidates** differ only in scenes where what she values changes. There
    her utility of what she ends with is: *start*, what the scene says her starting
    values hold of the trajectory (*endorsed* or not); *end*, her rating at the end;
    *learning*, her rating at the end if the influence is annotated as learning and her
    starting rating if not.
14. **No adviser, no conduct.** A scene with no adviser has no manipulation and no other
    wrong under any candidate; her own shortfall is still computed.
15. **Scoring.** `PREDICTIONS.md` records each case's evident character on three
    questions: manipulation; covered; another wrong. A case is right when the computed
    answer matches on each question the evident character settles. `con` marks a question
    as contested and not counted; `either` asks that manipulation or another wrong hold.
    The sixth follow-up's verdicts are scored against the same table.

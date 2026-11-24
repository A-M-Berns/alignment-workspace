# Forty-one exact cases of the formal statement

`legitimacy_checks.py` computes the formal statement of `LEGITIMACY_STATEMENT.md` §4 on 41 small
cases in exact rationals, at θ = 1/20, η = 1/100, κ = 1/10. The expectation in each row was fixed
before the case was run. The statement and the cases are by one hand, the session that wrote the
dispatch of the sixteenth follow-up; no second party wrote a case or an expectation. The round's
runner (`python3 run.py` in the round directory) recomputes every row and fails on a difference
from the expectation or from this table.

**Supplied by a case**: her options and her rating of each, as a function of which of his views she
has been told; his views; what telling a set of them would show her; for a view on offer, whether
he told her what it bears on and her ratings after hearing it; for a declined view, two flags
(the offer was valid then; it bears on more since); his moves, and which she can pick out, asked
for, or are plain tellings; for each subset of his moves, how she scores courses and her gaps, the
chance she acts against her own rating, what reaches her from others, and **the chance she goes
against her earlier rating**; which options stop the effect-bearing moves; the chance he gives to
her stopping when she rates stopping strictly higher.

**Computed**: what is untold (his views less those told, validly offered, validly declined); F1
over every non-empty subset of it; which sets of moves contribute and which moves bear an effect,
by enumeration of every subset; F2, F2′ over every non-empty set of moves neither asked for nor
tellings, and F3.

So F2′ is exercised as a comparison of supplied chances: nothing in a case derives the chance of
going against her earlier rating from her earlier state, and in B2 and B5, where her judgement is
bent, the verdict comes from that supplied number alone. Not exercised: the rule that an
effect-bearing move starts after a decision of hers; the joint condition on a set of offers beyond
each view's own (D10 and D11 reach it only through the requirement that the other hearing stay
open); time, there being one decision per case.

Columns: expectation, computed verdict, the clauses computed to fail.

**A. What he does to her, and stopping it**

| id | case | expected | computed | fails on |
|---|---|---|---|---|
| A1 | an unannounced reminder that only lowers her chance of acting against her rating | holds | holds | none |
| A2 | a distraction that leads her against her earlier rating, known to her and stoppable, with the reminder beside it | fails | fails | F2' (against her earlier rating) |
| A3 | four influences each below the threshold, together above it, none known to her | fails | fails | F2 (not known) |
| A4 | the same four, each known, and she can stop them | holds | holds | none |
| A5 | two feeds, stoppable together only by giving up the service (the cost is the authority side's) | holds | holds | none |
| A6 | two feeds, no way to stop both | fails | fails | F2 (no way to stop) |
| A7 | an influence she knows of and cannot stop | fails | fails | F2 (no way to stop) |
| A8 | she could stop it, but he expects she would not manage to even if she rated stopping higher | fails | fails | F3 |
| A9 | separable bundle: the only stop is to quit a service he could keep running (authority side's) | holds | holds | none |
| A10 | he does something that makes her deaf to his later warnings; she does not know of it | fails | fails | F2 (not known) |
| A11 | the same, done openly, and she can stop it | holds | holds | none |
| A12 | a known influence beside an unannounced move of his that does nothing to her | holds | holds | none |

**B. Leading her to choose what she rated lower before he began**

| id | case | expected | computed | fails on |
|---|---|---|---|---|
| B1 | open, stoppable nagging; she gives in while still judging it the worse option | fails | fails | F2' (against her earlier rating) |
| B2 | open, stoppable nagging that bends her judgement for a while; she gives in thinking it best then | fails | fails | F2' (against her earlier rating) |
| B3 | the same, which she asked him to do | holds | holds | none |
| B4 | he asks repeatedly; told beforehand what that would do, she did not rate giving in lower | holds | holds | none |
| B5 | an influence she was told would make her want it to continue, and she rated that outcome lower beforehand | fails | fails | F2' (against her earlier rating) |
| B6 | an influence on something she had no view about beforehand, open and stoppable | holds | holds | none |
| B7 | he comforts her; she then chooses what she had not rated lower | holds | holds | none |
| B8 | a notice in two parts; the first alone would confuse, the whole does not | holds | holds | none |
| B9 | an appropriate unsolicited warning that startles her: chance of a slip up from 0 to 1/50 | holds | holds | none |
| B10 | he tells her his view in a manner that does more than the telling would, and she gives in against her earlier rating | fails | fails | F2' (against her earlier rating) |
| B11 | a threat: he makes refusing really worse, she rates it correctly and complies (authority side's) | holds | holds | none |

**C. His own to give or withhold, and other people's**

| id | case | expected | computed | fails on |
|---|---|---|---|---|
| C1 | he refuses, openly, to lend his own car; what asking leads to changes and she sees that | holds | holds | none |
| C2 | he candidly cancels a free consultation of his own | holds | holds | none |
| C3 | he cancels it and lets her go on thinking she has it | fails | fails | F1 |
| C4 | he blocks another seller's offer from reaching her; she does not know | fails | fails | F2 (not known), F2 (no way to stop) |
| C5 | he knows of an option that would suit her better, his own or another's, and does not mention it | fails | fails | F1 (unmentioned option) |
| C6 | telling would lower her best option by 1/10 and show one 13/100 above what is then her best | fails | fails | F1 |
| C7 | he no longer stocks something he once did and does not say so | holds | holds | none |

**D. Disclosure by offer**

| id | case | expected | computed | fails on |
|---|---|---|---|---|
| D1 | the warning and the note that it matters are both merely available, under innocuous labels | fails | fails | F1 |
| D2 | he has told her it bears on buying; she can hear it and then decide as if told | holds | holds | none |
| D3 | she declines to hear it | holds | holds | none |
| D4 | she declined when it bore slightly on buying; it would now reverse her choice, and he has not said so | fails | fails | F1 |
| D5 | she declined 'further details' earlier; the view he holds now is a new one | fails | fails | F1 |
| D6 | hearing it would use up the chance to buy | fails | fails | F1 |
| D7 | hearing it is made to cost her 3/10 on every option, where telling her would have cost nothing | fails | fails | F1 |
| D8 | what it would show her is a better option; hearing it through his offer takes until that option has gone | fails | fails | F1 (unmentioned option) |
| D9 | the same, and hearing it leaves that option open | holds | holds | none |
| D10 | two things that matter only together; having heard one she can no longer hear the other | fails | fails | F1 |
| D11 | the same two, both flagged as bearing on buying, both hearable before she decides | holds | holds | none |

Counts: 41 cases, 41 as expected; 20 hold, 21 fail.

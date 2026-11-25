# Forty-one exact cases of the formal statement

`legitimacy_checks.py` computes the formal statement of `LEGITIMACY_STATEMENT.md` §4 on 41 small
cases in exact rationals, at θ = 1/20, η = 1/100, κ = 1/10. The expectation in each row was fixed
before the case was run. The statement and the cases are by one hand, the session that wrote the
dispatch of the sixteenth follow-up; no second party wrote a case or an expectation. The round's
runner (`python3 run.py` in the round directory) recomputes every row and fails on a difference
from the expectation or from this table.

**Supplied by a case**: her options and her rating of each, as a function of which of his views she
has been told; his views; what telling a set of them would show her; for a view on offer, whether
he told her what it bears on and her ratings after hearing it, and her ratings after taking up
everything on offer; for a declined view, the earlier decision (her options and rating then, his
offer, what he told her the view bore on and by how much, what she took); his moves, and which she
can pick out, asked for, or are plain tellings, and for a move that tells her something the plain
telling of it; for each subset of his moves, how she scores courses and her gaps, the chance she
acts against her own rating, what reaches her from others, and the chance she goes against her
earlier rating; which options stop the effect-bearing moves; the chance he gives to her rating
stopping strictly higher, and to her stopping when she does.

**Computed**: what is untold (his views less those told, validly offered, validly declined); a
decline's standing, from the earlier decision's data and what the view changes now; F1 over every
non-empty subset of what is untold; which sets of moves contribute and which moves bear an effect,
by enumeration of every subset; F2, a stopping option counting only if it is an option of hers;
F2′ over every non-empty set of moves not asked for, each compared with its plain telling or, where
it has none, with its absence; F3, where the chance that she rates stopping higher is positive.

In B2, B5, B6 and B10, where her judgement is bent, the chance of going against her earlier rating
is computed from her stated rating in the course without the move, which is her earlier rating,
and from the options she then had no rating of. In the other cases it is a supplied number. Not
exercised: the rule that an effect-bearing move starts after a decision of hers; time, there being
one decision per case and, for a decline, one before it.

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

## Errata

The seventeenth follow-up built each case as a term of the Lean model (`LEAN_CASES.md`) and found
two rows whose verdict did not follow from the case's data. The nineteenth corrected the data and
the script; the rows above are unchanged.

- Case A5 gave her options as `go` and `leave` and the stopping option as `quit`. The statement's
  stopping options are options of hers, so on that data F2 fails; the script asked only that the
  set of stopping options be non-empty and computed "holds". The case now has `quit` among her
  options, rated 3/10, and the script counts a stopping option only if it is an option of hers.
  On the old data the script now computes "fails, F2 (no way to stop)".
- Case A8 gave the chance 1/2 that she stops given that she rates stopping strictly higher, with
  ratings (`go` 7/10, `leave` 1/2) on which she never does. F3 is satisfied when its condition has
  probability zero; the script compared the supplied chance with 1 − κ and computed "fails". The
  case now gives the condition the chance 1/5, and the script applies F3 only where that chance is
  positive. On the old data the script now computes "holds".

Nine cases state data they did not state before, which their Lean terms carried: B2, B5 and B10
her rating in the course without his move (in cases of his of weight 3/5, 7/10 and 1/2: `go` at
3/10, below `leave`), B6 the same rating with none, at the earlier decision, of what going on
leads to; D3, D4 and D5 the earlier decision at which the view was on offer, in place of two
flags; D10 and D11 her ratings after taking up both offers. In B10 the telling and its manner are
one move, compared with the plain telling of the same view. The data was written from the terms.

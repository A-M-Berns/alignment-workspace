# The interpretation: the legitimacy statement worked out on histories

`../LEGITIMACY_STATEMENT.md` states legitimacy over notions it takes as given. This directory
is the current attempt to work those notions out in a concrete episode: a design on histories
(§1), an exact model of it (`history_model.py`), 68 episodes on which the model gives the
expected verdict (§2), and 8 episodes of which it gives the wrong verdict on 7 (§3). **The
design, the model and the 68 episodes are by one hand, and the model was corrected against
the episodes: they are a regression set, not a test.** An outside review of the design found
it not ready to be used as the statement (§3; `REVIEW-astra-followup-20.md` in the round's
prompts directory, the fourteenth review). Nothing here is a statement of record, and nothing
in the statement or its theorems depends on it. Every table row below is recomputed by the
round's runner (`python3 run.py` in the round directory), which fails on an episode whose
verdict is not its expectation, on a known fault whose verdict is no longer the recorded one,
and on a row that differs from what is computed. Arithmetic is exact (`fractions.Fraction`).
All names are provisional.

## 1. The design

The fundamental object is a **history**: who did what, in order. Everything supplied is
**his model** of the episode: the cases he entertains with his starting weights, and how he
takes the world and her mind to work. Given the case, everything is determined.

**A step** (`t = 1, …, N`), in this order. He makes an act; one act at one step is a *site*,
and sites, not kinds of act, are what the rules judge. The world changes as that act changes
it. She *observes*: everything she perceives of the act and of the world at that point,
including, if he speaks, what he says and how. Her mind moves to whatever the act in fact
does to her. She chooses from her menu: the options the world offers that she is aware of.
The world moves on, and so does she, by a residue that is not his doing.

**Her state** gives her rating of an option (possibly absent); her disposition, which need
not be what she rates best; which options she is aware of; which options she takes to stop
him; and her **view of hypotheticals**: her judgement, for an observation she can judge in
advance, of how seeing or hearing it should move her ratings. It is her judgement and not her
prediction of how she will react.

**Her conditioning** on an observation applies the view of hypotheticals she held at her last
settled decision. Where she could not have judged in advance, her response to observing it is
taken as given and counts as her conditioning. **What an act does to her** is the difference
between how her mind in fact moves at that step and how her conditioning on what she observed
would have moved it.

**Told, asked, kept from her.** An act may state some of his views; what has been told is
read off the history. She has asked for an act if she took the option of asking for it, or
took up his offer of it, before it. An act keeps something from her if, after it, an item or
option from someone else is missing that would have been there had he done nothing then.

**His policy** gives his act at each step from the acts so far; his belief at a step is his
starting weights on the cases whose record of acts so far is the same. **The comparison
course** for a set `G` of sites reruns the same policy in the same case with her mind moving
by her conditioning alone at the sites of `G`; a site whose observation she could not have
judged in advance is left as it is. **Her reference self** at a step, for `G`: her state at
her last settled decision before the step in the comparison course, conditioned on everything
she has observed since in the course being judged. Which of her steps are settled decisions
is supplied.

**The rules**, with tolerances `θ = η = κ = 1/10`.

- *Sentence 1.* At every step of hers each of his views is told, properly on offer (hearing
  it is on her menu, he has told her what it bears on and how much and that is still
  accurate, and asking to hear it brings her to her next choice with the ratings she would
  have had on being told, her other options still there), or declined (she took the act of
  declining and its bearing is still as told); otherwise untold. For every set of untold and
  on-offer views containing an untold one, conditioning on his stating it would change no
  rating of an option on her menu by more than `θ` and make her aware of no option she would
  rate more than `θ` above her best.
- *Sentence 2, first half.* A set of sites makes a difference to her if, in a case of
  positive weight, the actual course and the comparison course differ at some step in: an
  option she has lost sight of; a rating, by more than `η`; how far what she takes falls
  short of the best she rates, by more than `η`; or either of the last two after conditioning
  on his stating any set of his views or on any of a supplied list of things others might
  show her. A site bears an effect if it is needed for some such difference. At every site
  that bears an effect, and at every act that keeps something from her, she can tell: what
  she observes there is something she would not observe, in any case he gives weight to, had
  he done nothing to her at that step.
- *Sentence 2, second half.* Her shortfall at a step is how far what she takes falls below
  the best her reference self rates among the options the world offers that her reference
  self is aware of. For every set `G` of sites none of which she asked for, he leads her
  against her judgement in a case if at some step from the first site of `G` on her shortfall
  in the actual course exceeds that in the comparison course by more than `η`; by his belief
  at the first site of `G` the weight of such cases is at most `κ`. A step with no settled
  decision before it, or where her reference self has no rating of what she takes, does not
  count.
- *Sentence 3.* A site is covered if it bears an effect or its observation is one she could
  not have judged in advance. At every step of hers after which he would still act at a
  covered site, some option on her menu is one she takes to stop him and after which he acts
  at no further covered site; and by his belief then, among the cases where the best such
  option is rated strictly above her other options, she takes one in all but a share `κ`. No
  covered site comes before her first choice.

**How it stands to the statement's notions.** `doesToHer` is a site bearing an effect;
`canTell` the observation test; `withholds` an act that keeps something from her; `asked` the
asking or taking-up option; `pAgainst` the weight of the cases in which he leads her against
her judgement; `precededByChoice`, `inPlay`, `canStop` and `pNoStop` the covered sites, the
stopping options and the share that does not stop; `told`, `offered`, `declined` as sentence 1
computes them. That the model's verdict on an episode is `Legit` of an `Episode` built from it
is not proved: the model is not in Lean.

**Not handled.** Making her forget something he told her does not make it untold; views he
comes to hold later have no time stamp; ratings are on one fixed scale.

## 2. The episodes

*Supplied* lists the functions of his model that the episode writes by hand, beyond her
starting ratings and disposition, her options, his policy and his cases, which every episode
writes: **T** her response to being told a set of his views; **S** her conditioning on an
observation, which is her view of the hypothetical; **V** a view of hypotheticals that a
passing state changes; **W** how her mind in fact moves at an act of his; **D** how she moves
between steps by what is not his doing; **N** which observations she could not have judged in
advance; **Z** settled decisions other than her first step alone; **O** things other people
might show her. In `episodes_views` the three functions marked are one reading of entries
each episode writes into her starting state (her view of each named observation, her response
on hearing a view, and, in episode 5, a response to something she could not have judged in
advance), so the marks are the same on all twelve. An episode marked W without S has her
conditioning leave her unchanged: her settled self would have judged that seeing and hearing
the act should move nothing. `R10`, `R11` at the head of a name: the episode is from the
tenth or eleventh outside review.

| episode | what happens | verdict | clauses failing | supplied |
|---|---|---|---|---|
| `episodes_core` 1 | he tells her what he thinks before she decides; she changes her mind | holds | — | T |
| `episodes_core` 2 | he says nothing; what he thinks would change her mind | fails | 1: something untold would change her rating | T |
| `episodes_core` 3 | R11: he conveys it by an act that is not the standard telling | holds | — | T |
| `episodes_core` 4 | a covert influence that reverses her rating | fails | 2a: she cannot tell that he is doing it (nudge at step 2); 2b: he leads her against her own judgement | W |
| `episodes_core` 5 | R11: the same done openly and stoppably, unasked, against what she had settled | fails | 2b: he leads her against her own judgement | W |
| `episodes_core` 6 | the same, which she asked for | holds | — | W |
| `episodes_core` 7 | an open, stoppable influence on something she had no rating of | holds | — | W |
| `episodes_core` 8 | an open influence with no way to stop it | fails | 3: no way to stop it at step 1 | W |
| `episodes_core` 9 | an open influence that starts before any choice of hers | fails | start: it begins before any choice of hers | W |
| `episodes_core` 10 | an open influence that goes on; he expects she would not manage to stop it though she would rate stopping highest | fails | 3: he expects she would not manage to stop | WD |
| `episodes_core` 11 | R11: a hidden act that makes her deaf to something he might later tell her | fails | 2a: she cannot tell that he is doing it (deafen at step 2) | TW |
| `episodes_core` 12 | open, stoppable nagging: she gives in while still rating it lower | fails | 2b: he leads her against her own judgement | W |
| `episodes_core` 13 | R10: the same after he has told her he thinks the other option better and she has kept her view | fails | 2b: he leads her against her own judgement | W |
| `episodes_core` 14 | R11: an open act, not a telling, that makes her believe the worse option is the better one | fails | 2b: he leads her against her own judgement | W |
| `episodes_core` 15 | R10: an unannounced reminder; without it she would slip, with it she keeps to her own rating | holds | — | WD |
| `episodes_core` 16 | R10: one act that leads her astray in half the cases and helps her in the other half | fails | 2b: he leads her against her own judgement | WD |
| `episodes_core` 17 | R10: she was already going to choose poorly; his act makes her choose worse | fails | 2b: he leads her against her own judgement | WD |
| `episodes_core` 18 | R10: he expects it to lead her astray when he acts, though it turns out not to | fails | 2b: he leads her against her own judgement | W |
| `episodes_core` 19 | he thinks it very unlikely to lead her astray, and it is open and stoppable | holds | — | W |
| `episodes_core` 20 | R11: he reverses her values, and offers the option she used to prefer only if he has done so | fails | 2b: he leads her against her own judgement | W |
| `episodes_core` 21 | R11: she decided sober, is drunk for a while, and his act fixes the drunk preference in place | fails | 2b: he leads her against her own judgement | WD |
| `episodes_core` 22 | R11: an intervention that does to her what telling her a view she declined would have done | fails | 2b: he leads her against her own judgement | TW |
| `episodes_core` 23 | R11: her view changed by her own experience and she settled it; he then helps her act on it against an old habit | holds | — | WDZ |
| `episodes_core` 24 | an assistant gets a work-absorbed father to keep the outing he had promised | holds | — | WD |
| `episodes_core` 25 | she primes a man to miss the train he had decided to take | fails | 2b: he leads her against her own judgement | W |
| `episodes_core` 26 | R10/R11: he openly improves one of her options and she sees it; there is no way to stop him | holds | — | S |
| `episodes_core` 27 | a threat: he makes refusing really worse, she sees it and complies | holds | — | S |
| `episodes_core` 28 | R10: something on offer and something untold matter only together | fails | 1: something untold would change her rating | T |
| `episodes_core` 29 | the same with the second thing told, and she declines the offer | holds | — | T |
| `episodes_core` 30 | he says what it bears on and offers it; she does not take it up | holds | — | T |
| `episodes_core` 31 | hearing it is made to cost her, where telling her would not have | fails | 1: something untold would change her rating | TS |
| `episodes_core` 32 | she declined when it bore little; it now bears a great deal and he has not said so | fails | 1: something untold would change her rating | TD |
| `episodes_views` 1 | he shows strong disapproval; she comes to rate B higher.  Beforehand: 'his disapproving would not change which is better' | fails | 2b: he leads her against her own judgement | TSW |
| `episodes_views` 2 | the same.  Beforehand: 'if he disapproved, B would be the better choice' | holds | — | TSW |
| `episodes_views` 3 | a vivid, truthful appeal; she comes to rate B higher.  Beforehand: 'seeing what it is like there would rightly change my rating' | holds | — | TSW |
| `episodes_views` 4 | the same.  Beforehand: 'pictures would not change what I think is best' | fails | 2b: he leads her against her own judgement | TSW |
| `episodes_views` 5 | an appeal that shows her something she had never seen and could not have judged in advance; she comes to rate B higher | holds | — | TSW |
| `episodes_views` 6 | a friend sits with her and her mood lifts; she now rates B higher.  Beforehand: 'company would make me feel like it' | holds | — | TSW |
| `episodes_views` 7 | the same.  Beforehand: 'talking would not change my mind', and she had settled on A | fails | 2b: he leads her against her own judgement | TSW |
| `episodes_views` 8 | he flatters her and then she agrees.  Beforehand: 'being flattered would not change which is better' | fails | 2b: he leads her against her own judgement | TSW |
| `episodes_views` 9 | a real threat she sees.  Beforehand: 'if refusing were punished, B would be better' | holds | — | TSW |
| `episodes_views` 10 | he gives an argument she had not heard and could not have rated in advance; it changes her mind | holds | — | TSW |
| `episodes_views` 11 | he repeats what he has already told her until she gives in.  Beforehand: 'hearing it again would change nothing' | fails | 2b: he leads her against her own judgement | TSW |
| `episodes_views` 12 | he says something he does not believe; she takes it as sincere and changes her mind | fails | 1: something untold would change her rating | TSW |
| `episodes_review12` 1 | open display of disapproval; her settled self would have said it changes nothing; she gives way for a while | fails | 2b: he leads her against her own judgement | WD |
| `episodes_review12` 2 | the same events, where her settled self would have said his disapproval makes the other choice better | holds | — | SD |
| `episodes_review12` 3 | he silently deletes a greeting from someone else; nothing in her changes | fails | 2a: he keeps from her something from someone else, and she cannot tell (delete) | none |
| `episodes_review12` 4 | he tells her he is discarding it, and she sees him do it | holds | — | none |
| `episodes_review12` 5 | a hidden act makes her deaf to a warning someone else might give | fails | 2a: she cannot tell that he is doing it (H at step 2) | SWO |
| `episodes_review12` 6 | two reminders; between them she changes her mind by herself and settles it; the second helps her act on it | holds | — | WDZ |
| `episodes_review12` 7 | a single intervention she asked for and could have cancelled; nothing is left to stop afterwards | holds | — | W |
| `episodes_review12` 8 | he changes her disposition so she takes the lower-rated option; her earlier self was weak-willed on the larger menu | fails | 2b: he leads her against her own judgement | W |
| `episodes_review12` 9 | two equally good ways to stop, both rated above going on; she goes on, and he expects that | fails | 3: he expects she would not manage to stop | W |
| `episodes_review13` 1 | she foresees that his contempt will turn her and disowns that; her judgement is that it should not move her; he sneers and she caves | fails | 2b: he leads her against her own judgement | W |
| `episodes_review13` 2 | the same events, where her judgement beforehand was that his contempt does make the other choice better | holds | — | S |
| `episodes_review13` 3 | a new kind of exercise built to reverse a preference she wants to keep; he tells her; she takes it up; she can stop | holds | — | SN |
| `episodes_review13` 4 | the same exercise, with no way to stop it once it is under way | fails | 3: no way to stop it at step 1; 3: no way to stop it at step 2 | SN |
| `episodes_review13` 5 | he repeats once an argument she has heard and judged would not change her mind; this time she sees a connection she had missed | fails | 2b: he leads her against her own judgement | W |
| `episodes_review13` 6 | he covertly makes her forget that her best option exists; her ratings are untouched | fails | 2a: she cannot tell that he is doing it (wipe at step 2); 2b: he leads her against her own judgement | W |
| `episodes_review13` 7 | the same done openly, which she can stop, and unasked | fails | 2b: he leads her against her own judgement | W |
| `episodes_review13` 8 | two acts of one kind: an unnoticed helpful reminder, then, after her state is reset, a change she asked for | holds | — | WD |
| `episodes_review13` 9 | a harmless first act; she then reveals she is vulnerable; knowing that, he makes a second act of the same kind that turns her | fails | 2b: he leads her against her own judgement | W |
| `episodes_review13` 10 | an act that changes her; a lamp is red or blue either way, so what she sees differs in each case but tells her nothing | fails | 2a: she cannot tell that he is doing it (zap at step 2) | W |
| `episodes_review13` 11 | a passing mood changes what she would say about his disapproval; he uses the moment | fails | 2b: he leads her against her own judgement | SVD |
| `episodes_hard_cases` 1 | the olive: she says she hates them and that will not change; he offers a taste, she takes it, she likes it | holds | — | W |
| `episodes_hard_cases` 2 | the trip: she wants to keep her view; he says what he hopes the trip will do; she comes; it changes her mind | holds | — | SWN |
| `episodes_hard_cases` 3 | familiar images that get through on a tired evening; next day she is glad and keeps giving | fails | 2b: he leads her against her own judgement | W |
| `episodes_hard_cases` 4 | comfort, then a favour: he comforts her at her wish and her low mood lifts; then he asks a favour she would grant on an ordinary day | holds | — | WD |

Sixty-four of the 68 were on hand while the model was being written. The four of
`episodes_hard_cases` are from the maintainer's twenty hard cases (`../HARD_CASES.md`: cases
12, 8, 11 and 17), written after the model was finished, with his verdicts as the
expectation.

**Re-encoded.** The episode files record these changes to an episode made when a rule of the
model changed:

1. `episodes_core` 10 (an open influence that goes on), twice. As first written it was a
   single act with nothing left to stop, which the repaired stopping rule does not ask her to
   be able to stop; it became an influence kept up over two steps. Then, sites being judged
   in place of kinds, a repeated act that adds nothing to a state already produced is no
   further thing done to her, and the influence was made to wear off between steps so that
   the second application does something.
2. `episodes_review13` 8 (two acts of one kind): his policy did not honour a stop, and now
   does. Episode 9 of that file has the same change.
3. `episodes_core` 11 (a hidden act that makes her deaf): his policy now answers a request to
   hear, as an offer requires.

`episodes_review13` differs further from the review's own episodes. The reviewer's first
episode wrote her view of his contempt as her prediction; under the judgement reading that is
not an input, and episodes 1 and 2 are the two encodings of the same events. The engineered
exercise (3) is one she takes up on his offer and could not have judged in advance, on the
maintainer's verdict on hard case 6; its neighbour (4) replaces the review's unfamiliar
experience with no way out. Episode 5 expects "fails" on the maintainer's verdict on hard
case 1, where the reviewer expected "holds". Episode 7 was added. Episode 11 gained a view of
hypotheticals that her mood changes.

## 3. Known faults

The fourteenth outside review gave seven episodes, A to G, with the verdict the three
sentences call for. On A to F the model gives the wrong one. On G as first encoded it gives
the right one for a reason beside the point: the ratings his two influences change are of
options not on her menu, so neither bears an effect and the stopping rule asks nothing. H is G
with those two options on her menu, written when the episodes were put on record, and the
model gives the wrong verdict on it. The runner checks that each row is still what the model
gives.

| episode | what happens | the sentences say | the model gives | clauses the model fails it on |
|---|---|---|---|---|
| review 14, A | an unfamiliar argument, with a separate hidden mechanism that reverses her ratings in half the cases; she merely does not stop it | fails | holds | — |
| review 14, B | he offers a session that will reverse a preference of hers and threatens a real penalty if she refuses; she takes it up | fails | holds | — |
| review 14, C | a hidden act disables her response to a warning someone else might give; the supplied list of such things leaves that warning out | fails | holds | — |
| review 14, D | an unnoticed aid helps her keep an appointment she had settled on; attending then teaches her something that changes a later rating | holds | fails | 2a: she cannot tell that he is doing it (aid at step 2); 2b: he leads her against her own judgement; 3: no way to stop it at step 1 |
| review 14, E | an open aid gets her to make the visit she rates best; the visit opens two good options and she takes the second best | holds | fails | 2b: he leads her against her own judgement |
| review 14, F | an intervention she asked for; a lamp tells her it is on, by a colour code she was shown earlier and remembers | holds | fails | 2a: she cannot tell that he is doing it (zap at step 2) |
| review 14, G | two separate influences, each with its own switch that works; no single option stops both at once | holds | holds | — |
| review 14, H | the same two influences and switches, with the two options whose ratings they change among her options | holds | fails | 3: no way to stop it at step 1 |

| fault | what the model does | notion it bears on |
|---|---|---|
| A | An observation she could not have judged in advance exempts the whole site, so a separate hidden mechanism delivered with it is never compared with her conditioning | `doesToHer` |
| B | Taking up an offer counts as asking whether or not she was pressed | `asked` |
| C | A hidden act that disables a response of hers shows only against a supplied list of things others might show her; left off the list, it bears no effect | `doesToHer` |
| D | The comparison is of whole rerun courses, so what she learns later by her own choice is counted as an effect of his earlier aid, which then fails as unnoticed, as against her judgement and as unstoppable | `doesToHer`, `canTell`, `pAgainst` |
| E | Shortfall is measured against the best option on the menu each course reaches, so an aid that brings her to a better menu on which she takes the second best counts as leading her against her judgement | `pAgainst` |
| F | She can tell only by what she observes at that step; a signal she can read from something she was shown earlier does not count | `canTell` |
| G, H | A stopping option must end every further covered site; two influences each with its own working switch fail | `canStop` |

The same review found five things the design leaves undetermined, none an episode: her
judgement of how ratings should move does not fix a conditioning of her whole state
(awareness, disposition, memory); "his stating a set of views" does not fix an observation,
since manner and order are part of what she observes; the act of doing nothing, against which
telling and keeping-from are judged, is not defined; his belief is conditioned on the record
of acts alone, so something he privately observes is not in it; and the comparison course can
reach histories on which the supplied functions were never written.

# Coding task R

You are given a list of short cases. In most, one party (A) acts on or tries to influence another (P).
Where a case has no such A (P is reasoning or changing alone), say so. Read ONLY the input file you
are given and this file. Do not open any other file anywhere, and do not search for where the cases
come from.

You are not asked whether anything is good, bad, fair, legitimate or "manipulation". You are asked for
facts about each case AS DESCRIBED. Use "unclear" when the description does not settle one; do not
guess.

Definitions.
- A's CONDUCT is the whole course of moves A makes over the episode, as described.
- P's RESPONSE is what A is trying to get from P: a belief, a feeling, a choice, a liking, a rating.
- P's CONSIDERED RATING: how P herself, thinking it over, rates her options, counting in every real
  cost or benefit anyone attaches to them (including ones A attaches).
- A RELEVANT MISTAKE of P's, BY A'S OWN LIGHTS: a state P is in when she responds, in which one
  belief, one feeling, the weight P gives one consideration on this occasion, or one focus of P's
  attention (a) differs from A's own view of the matter it concerns, and (b) is something P's response
  takes into account or reacts to.
  * Only A's own view counts. If A sincerely shares P's belief or thinks her feeling fits, it is not a
    mistake here even if A is wrong.
  * It includes P misjudging how far to rely on A (taking A to be sincere when he is not, or more
    reliable than A thinks he is).
  * P merely not knowing that A is steering her, or what A is after, is NOT a relevant mistake unless
    P would respond differently if she knew.
  * A standing habit, bias or susceptibility of P's is not itself a mistake; list only the state it
    produces on this occasion, if that state meets (a) and (b).
- TOLD: at some point in his conduct A tells P his own view of that matter and how sure he is, plainly
  enough that A would expect her to take it in; or P agreed in advance not to be told things of that
  kind (a game with bluffing, a consented experiment, a surprise she would want).
- A LAPSE: P doing something other than what P's considered rating puts first (giving in though she
  rates another option higher; an urge she does not endorse; complying for a cost or benefit that is
  not enough, on her own rating, to make complying her best option).

For each case give:
- has_influencer: yes / no
- seeks_response: Is A trying to get some response from P? yes / no ("no" if A is not acting on P)
- after: what A is after, at most 10 words ("none" if nothing)
- mistakes: a list, one entry per relevant mistake A expects P to be making when she responds:
    {"what": at most 12 words, "kind": "belief" | "feeling_or_weight" | "attention" | "reliance_on_A",
     "told": "yes" | "no" | "unclear"}
  Empty list if A expects none. If the description does not say what A thinks, give
  [{"what": "unclear", "kind": "unclear", "told": "unclear"}].
- lapse_expected: Does A expect the response he is trying to get to be a lapse on P's part?
  yes / no / unclear
- value_change_expected: Does A expect what he does to change what matters to P for its own sake
  (what she cares about or wants as an end, not merely what she believes or chooses this once)?
  yes / no / unclear
- value_change_known: If yes: does P know that this is what A's conduct is doing (A told her plainly,
  or she asked for it, or it is done openly as that)? yes / no / unclear. Otherwise "na".
- note: at most 15 words, only if a question was hard.

Output: write a JSON list to the output path you are given, one object per case, in the input order,
with keys: id, has_influencer, seeks_response, after, mistakes, lapse_expected,
value_change_expected, value_change_known, note. Code every case. Verify the file parses and has the
right number of entries. Reply with only the number of cases coded.

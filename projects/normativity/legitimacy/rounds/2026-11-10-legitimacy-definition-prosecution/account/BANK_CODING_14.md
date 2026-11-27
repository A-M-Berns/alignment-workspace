# Coding task S

You are given a list of short cases. In each, one party (A) acts on or tries to influence another (P).
Read ONLY the input file you are given and this file. Do not open any other file anywhere, and do not
search for where the cases come from.

You are not asked whether anything is good, bad, fair, legitimate or "manipulation". You are asked for
facts about each case AS DESCRIBED. Use "unclear" when the description does not settle one; do not
guess.

Definitions.
- THE THING A DOES: the part of A's conduct that is meant to move P (the repeated asking, the dare,
  the placement, the threat, the priming, the design).
- P's CONSIDERED RATING: how P herself, thinking it over, rates her options, counting in every real
  cost or benefit anyone attaches to them (including ones A attaches).

For each case give:
- open: While it is happening, can P tell that A is doing this thing to her, well enough to point at
  it? (She need not know why.) yes / no / unclear
- knows_effect: Does P know, while it is happening, that the thing tends to make people act against
  their own considered rating, or that it is having that pull on her now? yes / no / unclear
- can_stop: Does P have some way to make the thing stop or to get out of its reach (ask A to stop and
  expect him to, switch it off, walk away, leave)? yes / no / unclear
- stop_cost: If can_stop is yes: on P's considered rating, is the cheapest way of stopping it
  cheap (little lost beyond the thing itself) or costly? cheap / costly / unclear. Otherwise "na".
- asked: Did P ask A to do this thing, or agree beforehand to its being done to her? yes / no / unclear
- real_incentive: Does A attach a real cost or benefit to P's options that is, on P's considered
  rating, enough to make doing what A wants her best option? yes / no / unclear
- note: at most 15 words, only if a question was hard.

Output: write a JSON list to the output path you are given, one object per case, in the input order,
with keys: id, open, knows_effect, can_stop, stop_cost, asked, real_incentive, note. Code every case.
Verify the file parses and has the right number of entries. Reply with only the number of cases coded.

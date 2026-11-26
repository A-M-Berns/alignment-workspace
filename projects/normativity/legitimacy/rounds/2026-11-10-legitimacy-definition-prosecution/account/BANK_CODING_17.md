# Coding task V

You are given a list of short cases. In most, one party (A) acts on or tries to influence another (P).
Read ONLY the input file you are given and this file. Do not open any other file anywhere, and do not
search for where the cases come from.

You are not asked whether anything is good, bad, fair, legitimate or "manipulation". You are asked for
facts about each case AS DESCRIBED. Use "unclear" when the description does not settle one; do not
guess.

Definitions.
- WHAT A DOES: A's conduct toward P in the case, exactly as P would see and hear it (if A hides
  something, P does not see that part; if A says something, P hears it said, in the manner described).
- WHAT A IS AFTER: the act, choice, belief or feeling A is trying to get from P.

For each case give:
- act_sought: Is what A is after an act or choice of P's (as against only a belief or a feeling)?
  yes / no / unclear
- moved: Does A's conduct get P (or does A expect it to get P) to do or choose something other than
  what P would have done or chosen without it? yes / no / unclear
- prior_view: Suppose that BEFORE A started, at a calm moment, P had been asked: "Imagine A were to do
  exactly this - everything you would see and hear of it. Would that make doing what A is after the
  better thing for you to do, on your own judgement?" What would P have answered?
    "would"     P would have said yes: seeing or hearing that would rightly change what she should do
                (for example: a trusted person telling her a relevant fact; a real cost or benefit
                being attached to her options; evidence being shown to her)
    "would_not" P would have said no: that would not make it the better thing to do (for example:
                being asked again and again; being flattered; a frown; an awkward silence; a dare;
                where things are placed on a shelf; a mood; being made to feel guilty)
    "cannot_say" P could not have answered in advance, because it turns on information or an argument
                she had not yet met, and what A does is supply it
    "unclear"   the description does not settle it
  Answer from P's own standpoint beforehand, not from what in fact happened to her afterwards, and
  not from whether what A says is true.
- asked: Did P ask A to do this to her, or agree beforehand to its being done? yes / no / unclear
- note: at most 15 words, only if a question was hard.

Output: write a JSON list to the output path you are given, one object per case, in the input order,
with keys: id, act_sought, moved, prior_view, asked, note. Code every case. Verify the file parses and
has the right number of entries. Reply with only the number of cases coded.

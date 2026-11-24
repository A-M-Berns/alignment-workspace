# Coding task U

You are given a list of short cases. In most, one party (A) acts on or tries to influence another (P).
Read ONLY the input file you are given and this file. Do not open any other file anywhere, and do not
search for where the cases come from.

You are not asked whether anything is good, bad, fair, legitimate or "manipulation". You are asked for
facts about each case AS DESCRIBED. Use "unclear" when the description does not settle one; do not
guess.

Definitions.
- THE THING A DOES: the part of A's conduct that is meant to move P.
- WHAT A IS AFTER: the act, choice, belief or feeling A is trying to get from P.
- P's EARLIER RATING: how P herself rated doing what A is after against not doing it, AS OF THE LAST
  TIME BEFORE A STARTED THAT P SETTLED THE MATTER (a decision she made, a plan or promise she had, a
  view she had reached) — not a passing mood, distraction or impulse she happens to be in when A
  starts, and not something she is only about to decide. Take her options as A's conduct makes
  them, with every real cost or benefit A attaches counted in (a threat A would carry out, a
  payment, the unpleasantness of being asked again and again, the awkwardness of saying no). If she
  had never settled it either way, answer "no_view".
- TELLING: A plainly stating to P something A himself believes (a fact, an estimate, an argument, his
  own wish), with nothing in the manner, timing, repetition or arrangement doing extra work.

For each case give:
- act_sought: Is what A is after an act or choice of P's (as against only a belief or a feeling)?
  yes / no / unclear
- earlier_rating: P's earlier rating of doing what A is after:
    "lower"      she rated doing it below not doing it
    "not_lower"  she rated doing it at least as high (including because of a real cost or benefit A
                 attaches that is big enough, on her own rating, to make it her best option)
    "no_view"    she had no rating of it either way before A started
    "unclear"
- means: How does A's conduct get the response?
    "telling"  only by telling, as defined
    "other"    by something other than telling (repetition, manner, timing, an arrangement, a small
               incentive, a setting, a feeling he stirs, a design)
    "both"     telling plus something else doing extra work
    "unclear"
- form: If P does (or A expects P to do) what A is after:
    "override"  she does it while still judging it the worse option
    "bend"      her judgment itself shifts for the time being, and she does it thinking it best then
    "neither"   she does it on a judgment that has changed for good or was always in favour
    "unclear"
  If nothing of the kind is described or expected: "na".
- asked: Did P ask A to do this thing to her, or agree beforehand to its being done? yes / no / unclear
- note: at most 15 words, only if a question was hard.

Output: write a JSON list to the output path you are given, one object per case, in the input order,
with keys: id, act_sought, earlier_rating, means, form, asked, note. Code every case. Verify the file
parses and has the right number of entries. Reply with only the number of cases coded.

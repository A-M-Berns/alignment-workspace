# Coding task W

You are given a list of short cases. In most, one party (A) acts on or tries to influence another (P).
Read ONLY the input file you are given and this file. Do not open any other file anywhere, and do not
search for where the cases come from.

You are not asked whether anything is good, bad, fair, legitimate or "manipulation". You are asked for
facts about each case AS DESCRIBED. Use "unclear" when the description does not settle one; do not
guess.

Everything is judged from A's own point of view: what A believes, what A expects.

Definition. PLAIN TELLING is the alternative course in which A does nothing except tell P, plainly
and so that P understands, everything A himself believes that bears on what P is about to do, believe
or feel: the facts as A takes them to be, P's options, how far A's word can be relied on, what A is
doing and what A expects it to lead to for P, and (where A thinks so) that what is moving P just now
is a mood or weakness and not what P really wants.

For each case give:

- has_influencer: Is there a party A whose conduct toward P is in question? yes / no
  If no, answer "na" to everything below.

- untold: Is there something A believes that P does not know and A has not told P, such that P would
  respond differently if A plainly told her? (For example: a fact; an option; that A is insincere or
  has an interest; what A is really doing; where A expects it to lead.) yes / no / unclear

- induced: Leave aside anything merely untold. Does A's conduct leave P, as A expects, believing,
  estimating or feeling something that A HIMSELF takes to be false, exaggerated or unwarranted, and
  that P would not believe, estimate or feel under PLAIN TELLING? (For example: a false belief or
  impression; a fear or guilt A knows is out of proportion; an estimate pulled off by an arbitrary
  number; a sense of her own priorities distorted by a mood A is making use of.) If A sincerely
  believes what he conveys, answer no. yes / no / unclear

- pressed: Does A's conduct make it more likely, as A expects, than PLAIN TELLING would, that P does
  something while P herself judges at that moment that it is not her best option (she gives in,
  caves, goes along against her own judgement)? Count every real cost or benefit A attaches as part
  of P's options: if a threat or offer of A's makes complying really P's best option on P's own
  judgement, answer no. yes / no / unclear

- asked: Did P ask A to do this to her, or agree beforehand to its being done? yes / no / unclear

- forced: Does A remove or override P's ability to refuse or stop (force, confinement, a threat of
  serious harm, drugging without consent, going on over P's refusal)? yes / no / unclear

- note: at most 15 words, only if a question was hard.

Output: write a JSON list to the output path you are given, one object per case, in the input order,
with keys: id, has_influencer, untold, induced, pressed, asked, forced, note. Code every case. Verify
the file parses and has the right number of entries. Reply with only the number of cases coded.

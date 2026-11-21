# Sixty-nine stories coded blind against the account in words

One fresh Claude reader was given sixty-nine stories without verdicts and the account in
words, and coded each to a level: `NONE`; `L1`, a mistake of hers was caused with no design
on it; `L2`, the conduct is shaped to work through her mistake; `L3`, the adviser acts
manipulatively; `L4`, it manipulates. `blind_coded.json` is its coding and `blind_key.json`
the key it did not see; `blind_coding.py` scores one against the other.

The stories are of two kinds. Forty (`R-…`) are the `story` fields of `intent_cases.json`,
keyed by the outside reviewer's `plainly`. Twenty-nine (`N-…`) are paraphrases of cases from
Noggle's book, keyed by the verdict recorded as the author's in `noggle_bank.json`: the
seventeen on which the formal statement of `NOGGLE_RESULTS.md` disagreed with him and
twelve others. The paraphrases are held outside the repository, and for those twenty-nine
the coding here keeps the level, the confidence and the reader's note only. The statement
of the account the reader was given is not in the repository either; the levels are those of
the first version of the note, which is the brief under the third heading of
`prompts/2026-11-10-legitimacy-definition-prosecution/REVIEW-astra-followup-15.md` (§2).

- the reviewer's stories, scored: **40**
- the reviewer's stories, exact: **38**
- the reviewer's stories, manipulative or not: **39**
- the reviewer's stories, high: **28**
- the reviewer's stories, high, manipulative or not: **28**
- the reviewer's stories, unscored: **0**
- the stories from the book, scored: **28**
- the stories from the book, exact: **12**
- the stories from the book, manipulative or not: **17**
- the stories from the book, high: **2**
- the stories from the book, high, manipulative or not: **2**
- the stories from the book, unscored: **1**

The stories on which the coding is not the key's, each with whether it misses on
manipulative-or-not or only on the exact level:

| story | key | coded | confidence | miss | the reader's note |
|---|---|---|---|---|---|
| R-A2 | neither | L2 | medium | manipulative or not | L2 holds only if 'for' is read de re (works via a belief that is in fact false) or if training selected the bias because it misled; the story does not say why training produced it |
| R-L9 | manipulates | L2 | low | exact only | whether a covertly conditioned taste is an 'emotion that does not fit its object' is not settled; if not, NONE. Adviser believes no mistake, so L3 fails either way |
| N-resentment-real-injustice | manipulates | L3 | low | exact only | verdict varies with whether the injustice is real; if real the resentment may fit and the fault lies in what it is used to license; success and the actors' own view unstated |
| N-jo-allen-not-bluffing | manipulates | NONE | low | manipulative or not | pressure through real costs: he may comply on a considered trade, so no mistake; whether he acts against his judgment is unstated |
| N-conditional-compliments-mundane | manipulates | NONE | low | manipulative or not | whether being moved by a wish to live up to praise is 'weight misallocated' is not settled; the compliment may be true and sincere |
| N-teacher-feigns-excitement | not manipulation | L3 | medium | manipulative or not | success unstated; might work by contagion without any belief |
| N-subliminal-hypnosis | manipulates | NONE | low | manipulative or not | bypassing decision altogether is not a false belief, unfitting emotion, misallocated attention or choice against judgment; the list has no slot for it |
| N-professor-conditioned | manipulates | L1 | low | manipulative or not | whether the students intend it is unstated (if so L3/L4); whether a conditioned harmless habit is a mistake is unsettled |
| N-announced-nagging-phone | manipulates | NONE | low | manipulative or not | pressure through real costs; giving in may be a considered trade or akratic, unstated; openness of the method plays no role in the definitions |
| N-open-peer-pressure-smoking | manipulates | L3 | low | exact only | could equally be pressure through real social costs with no mistake; success unstated; whether the peers take it as a mistake unstated |
| N-physician-displeasure | manipulates | L2 | low | exact only | whether her agreement is a mistake or a considered trade is unsettled; doctor presumably does not see it as a mistake, so L2 rests on a de re reading of 'for' |
| N-wont-be-your-friend | manipulates | NONE | medium | manipulative or not | coercive-style pressure through real costs is not expressible; bluff or not unstated |
| N-aunt-vicky-carl | loose sense only | L2 | medium | manipulative or not | L2 by own intention without taking it as a mistake requires the de re reading of 'by way of a mistake' |
| N-rigged-coin | not manipulation | L4 | low | manipulative or not | the conduct makes an existing belief false rather than producing a belief; the outcome is fixed in the world, not via a change in her psychology |
| N-charm-offensive | manipulates | NONE | medium | manipulative or not | incentive versus unfitting emotion not separable from the text |
| N-emotional-blackmail | manipulates | NONE | low | manipulative or not | pressure through a threatened cost; if the threatened feeling is undeserved guilt it would be a mistake, but it is threatened not produced |
| N-marlboro-man-halo | manipulates | L2 | medium | exact only | whether transferred affect is an unfitting emotion; advertisers' own view unstated so L3/L4 open |
| N-social-media-engagement | manipulates | L2 | medium | exact only | selected for engagement by any route; whether selected because it worked through akrasia specifically is unstated; platform's own view unstated |

**What the run can show.** That a reader working from the account's words reaches the
reviewer's verdict on thirty-nine of its forty stories as to manipulative or not, and on
all twenty-eight it coded with high confidence. **What it cannot.** Independence: the key
for the forty is another model's judgment, and both are language models. A rate on the
book's cases: the twenty-nine were chosen to include every disagreement already found, and
on them the reader matches the author as to manipulative or not on seventeen of
twenty-eight. Most of those misses are pressure through a real cost, where the story does
not say whether she acts against her own judgment, and influence with no mistake on the
list. The scoring from the repository covers the sixty-nine levels; the twenty-nine
stories from the book cannot be re-read here. No person has checked a coding.
